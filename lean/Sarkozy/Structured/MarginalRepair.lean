module

public import Sarkozy.Structured.AdditiveCancellation

/-!
# Additive marginal repair (`lem:tr:repair`, parts (a)–(d) and (f) for a given solution)

`lem:tr:repair` (`paper/sections/17_completion_repair.tex`, brief F). The setting is that of
`lem:record:additive-cancellation` (`Sarkozy/Structured/AdditiveCancellation.lean`): a law
`ν` on `X × Y` with marginals `ν_X`, `ν_Y`, its conditional operators `A` and `A* = B` of
norm at most `ρ < 1` on centred functions, and target marginals `(1 + u)ν_X`, `(1 + v)ν_Y`.

This file proves the statements of the lemma about a centred solution `(f, g)` of the
repair equations `f + Ag = u`, `g + A*f = v`:
* `repair_norm_bounds` — (a), the bounds `‖f‖₂ ≤ (e_X + ρe_Y)/(1-ρ²)` and
  `‖g‖₂ ≤ (e_Y + ρe_X)/(1-ρ²)`, "equation by equation";
* `repair_sup_bounds` — (b), `‖f‖_∞ ≤ U_X + K_∞‖g‖₂` given the `L² → L^∞` bound `K_∞` of `A`;
* `repair_positive` — (c), `1 + f + g ≥ 1 - ‖f‖_∞ - ‖g‖_∞ > 0`;
* `repair_one_way` — (d), the one-way bound `‖f‖₂, ‖g‖₂ ≤ U/(1-ρ)`;
* `repair_marginals` and `repair_centred_norm` — (a) "`ν' = (1+f+g)ν` has the marginals
  `μ_X`, `μ_Y`" and (f), the norm `ρ'` of its centred conditional operator, by
  `additive_cancellation`.

Not formalized are:
* the existence and uniqueness in (a), `f = (I - AA*)^{-1}(u - Av)`;
* the invariance statements;
* (e), the swap symmetry, and (g), the Neumann series split.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The triangle inequality for `‖·‖_μ`. -/
theorem nrm_add_le (μ : FiniteLaw X) (f g : X → ℝ) :
    nrm μ (fun x => f x + g x) ≤ nrm μ f + nrm μ g := by
  have hf0 : 0 ≤ nrm μ f := Real.sqrt_nonneg _
  have hg0 : 0 ≤ nrm μ g := Real.sqrt_nonneg _
  have hff : ip μ f f = nrm μ f ^ 2 := by
    unfold nrm
    rw [Real.sq_sqrt]
    unfold ip
    exact μ.expect_nonneg fun x => mul_self_nonneg (f x)
  have hgg : ip μ g g = nrm μ g ^ 2 := by
    unfold nrm
    rw [Real.sq_sqrt]
    unfold ip
    exact μ.expect_nonneg fun x => mul_self_nonneg (g x)
  have hcs := abs_ip_le μ f g
  have hexp : ip μ (fun x => f x + g x) (fun x => f x + g x) =
      ip μ f f + 2 * ip μ f g + ip μ g g := by
    unfold ip
    rw [← μ.expect_const_mul, ← μ.expect_add, ← μ.expect_add]
    exact μ.expect_congr fun x => by ring
  have hle : ip μ (fun x => f x + g x) (fun x => f x + g x) ≤ (nrm μ f + nrm μ g) ^ 2 := by
    rw [hexp, hff, hgg]
    nlinarith [abs_le.mp hcs]
  calc nrm μ (fun x => f x + g x)
      = Real.sqrt (ip μ (fun x => f x + g x) (fun x => f x + g x)) := rfl
    _ ≤ Real.sqrt ((nrm μ f + nrm μ g) ^ 2) := Real.sqrt_le_sqrt hle
    _ = nrm μ f + nrm μ g := Real.sqrt_sq (add_nonneg hf0 hg0)

/-- `‖-f‖ = ‖f‖`. -/
theorem nrm_neg (μ : FiniteLaw X) (f : X → ℝ) : nrm μ (fun x => -f x) = nrm μ f := by
  unfold nrm ip
  congr 1
  exact μ.expect_congr fun x => by ring

/-- `‖f‖_μ ≤ U` for `|f| ≤ U`. -/
theorem nrm_le_of_abs_le (μ : FiniteLaw X) (f : X → ℝ) {U : ℝ} (hU : 0 ≤ U)
    (hf : ∀ x, |f x| ≤ U) : nrm μ f ≤ U := by
  unfold nrm ip
  have hle : μ.expect (fun x => f x * f x) ≤ U ^ 2 := by
    apply μ.expect_le_const
    intro x
    have := abs_le.mp (hf x)
    nlinarith
  calc Real.sqrt (μ.expect (fun x => f x * f x)) ≤ Real.sqrt (U ^ 2) := Real.sqrt_le_sqrt hle
    _ = U := Real.sqrt_sq hU

/-- **`lem:tr:repair`(a), the norm bounds**: a centred solution of `f + Ag = u`,
`g + A*f = v` has `‖f‖₂ ≤ (e_X + ρ e_Y)/(1-ρ²)` and `‖g‖₂ ≤ (e_Y + ρ e_X)/(1-ρ²)`. -/
theorem repair_norm_bounds (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (f : X → ℝ) (g : Y → ℝ) (u : X → ℝ) (v : Y → ℝ) (hf0 : νX.expect f = 0)
    (hg0 : νY.expect g = 0) (hfu : ∀ x, f x + A g x = u x) (hgv : ∀ y, g y + B f y = v y)
    {eX eY : ℝ} (hu : nrm νX u ≤ eX) (hv : nrm νY v ≤ eY) :
    nrm νX f ≤ (eX + ρ * eY) / (1 - ρ ^ 2) ∧ nrm νY g ≤ (eY + ρ * eX) / (1 - ρ ^ 2) := by
  have hf : nrm νX f ≤ eX + ρ * nrm νY g := by
    have e : f = fun x => u x + -(A g x) := by funext x; have := hfu x; linarith
    calc nrm νX f = nrm νX (fun x => u x + -(A g x)) := by rw [← e]
      _ ≤ nrm νX u + nrm νX (fun x => -(A g x)) := nrm_add_le νX _ _
      _ = nrm νX u + nrm νX (A g) := by rw [nrm_neg]
      _ ≤ eX + ρ * nrm νY g := add_le_add hu (hAρ g hg0)
  have hg : nrm νY g ≤ eY + ρ * nrm νX f := by
    have e : g = fun y => v y + -(B f y) := by funext y; have := hgv y; linarith
    calc nrm νY g = nrm νY (fun y => v y + -(B f y)) := by rw [← e]
      _ ≤ nrm νY v + nrm νY (fun y => -(B f y)) := nrm_add_le νY _ _
      _ = nrm νY v + nrm νY (B f) := by rw [nrm_neg]
      _ ≤ eY + ρ * nrm νX f := add_le_add hv (hBρ f hf0)
  have hden : 0 < 1 - ρ ^ 2 := by nlinarith
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hg hρ]
  · rw [le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hf hρ]

omit [Fintype X] in
/-- **`lem:tr:repair`(b)**: `‖f‖_∞ ≤ U_X + K_∞ ‖g‖₂`, where `K_∞` bounds `A` from `L²` to
`L^∞`. -/
theorem repair_sup_bounds (νY : FiniteLaw Y) (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) {Kinf : ℝ}
    (hK : ∀ k x, |A k x| ≤ Kinf * nrm νY k) (f : X → ℝ) (g : Y → ℝ) (u : X → ℝ)
    (hfu : ∀ x, f x + A g x = u x) {UX : ℝ} (hu : ∀ x, |u x| ≤ UX) (x : X) :
    |f x| ≤ UX + Kinf * nrm νY g := by
  have e : f x = u x - A g x := by have := hfu x; linarith
  rw [e]
  calc |u x - A g x| ≤ |u x| + |A g x| := abs_sub _ _
    _ ≤ UX + Kinf * nrm νY g := add_le_add (hu x) (hK g x)

omit [Fintype X] [Fintype Y] in
/-- **`lem:tr:repair`(c), positivity**: `1 + f + g ≥ 1 - F_X - F_Y > 0`. -/
theorem repair_positive (f : X → ℝ) (g : Y → ℝ) {FX FY : ℝ} (hf : ∀ x, |f x| ≤ FX)
    (hg : ∀ y, |g y| ≤ FY) (hF : FX + FY < 1) (x : X) (y : Y) :
    0 < 1 - FX - FY ∧ 1 - FX - FY ≤ 1 + f x + g y := by
  have h1 := abs_le.mp (hf x)
  have h2 := abs_le.mp (hg y)
  constructor <;> linarith

/-- **`lem:tr:repair`(d), one-way repair**: if `|u|, |v| ≤ U`, then
`‖f‖₂, ‖g‖₂ ≤ U/(1-ρ)`. -/
theorem repair_one_way (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (f : X → ℝ) (g : Y → ℝ) (u : X → ℝ) (v : Y → ℝ) (hf0 : νX.expect f = 0)
    (hg0 : νY.expect g = 0) (hfu : ∀ x, f x + A g x = u x) (hgv : ∀ y, g y + B f y = v y)
    {U : ℝ} (hU : 0 ≤ U) (hu : ∀ x, |u x| ≤ U) (hv : ∀ y, |v y| ≤ U) :
    nrm νX f ≤ U / (1 - ρ) ∧ nrm νY g ≤ U / (1 - ρ) := by
  obtain ⟨h1, h2⟩ := repair_norm_bounds νX νY A B hρ hρ1 hAρ hBρ f g u v hf0 hg0 hfu hgv
    (nrm_le_of_abs_le νX u hU hu) (nrm_le_of_abs_le νY v hU hv)
  have hden : 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
  have hpos : 0 < 1 - ρ := by linarith
  have hpos' : 0 < 1 + ρ := by linarith
  have hsimp : (U + ρ * U) / (1 - ρ ^ 2) = U / (1 - ρ) := by
    rw [hden]
    field_simp
  exact ⟨h1.trans (le_of_eq hsimp), h2.trans (le_of_eq hsimp)⟩

/-- **`lem:tr:repair`(a), the marginals of `ν' = (1 + f + g)ν`**: for a centred solution of
the repair equations, the marginal densities of `ν'` are `1 + u` and `1 + v`. -/
theorem repair_marginals (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    (f : X → ℝ) (g : Y → ℝ) (u : X → ℝ) (v : Y → ℝ)
    (hfu : ∀ x, f x + A g x = u x) (hgv : ∀ y, g y + B f y = v y) :
    (∀ φ : X → ℝ, reweightForm ν f g φ (fun _ => 1) = ip νX φ (fun x => 1 + u x)) ∧
      (∀ φ : Y → ℝ, reweightForm ν f g (fun _ => 1) φ = ip νY (fun y => 1 + v y) φ) := by
  constructor
  · intro φ
    rw [reweightForm_apply]
    have e : (fun p : X × Y => (1 + f p.1 + g p.2) * (φ p.1 * 1)) =
        fun p => φ p.1 * (1 + f p.1) + φ p.1 * g p.2 := by
      funext p; ring
    rw [e, ν.expect_add, hmX (fun x => φ x * (1 + f x)), hA φ g]
    unfold ip
    rw [← νX.expect_add]
    apply νX.expect_congr
    intro x
    show φ x * (1 + f x) + φ x * A g x = φ x * (1 + u x)
    rw [← hfu x]
    ring
  · intro φ
    rw [reweightForm_apply]
    have e : (fun p : X × Y => (1 + f p.1 + g p.2) * (1 * φ p.2)) =
        fun p => (1 + g p.2) * φ p.2 + f p.1 * φ p.2 := by
      funext p; ring
    rw [e, ν.expect_add, hmY (fun y => (1 + g y) * φ y), hB f φ]
    unfold ip
    rw [← νY.expect_add]
    apply νY.expect_congr
    intro y
    show (1 + g y) * φ y + B f y * φ y = (1 + v y) * φ y
    rw [← hgv y]
    ring

/-- **`lem:tr:repair`(f), the centred norm of the repaired law**: under (c), the repaired law
`ν' = (1 + f + g)ν` satisfies `lem:record:additive-cancellation`, so its centred conditional
operator (relative to `μ_X`, `μ_Y`) has norm at most
`ρ' = (ρ(1 + F_X + F_Y) + e_X e_Y)/√((1-U_X)(1-U_Y))`. -/
theorem repair_centred_norm (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hAρ : ∀ k, νY.expect k = 0 → nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h, νX.expect h = 0 → nrm νY (B h) ≤ ρ * nrm νX h)
    (f : X → ℝ) (g : Y → ℝ) (u : X → ℝ) (v : Y → ℝ) (hf0 : νX.expect f = 0)
    (hg0 : νY.expect g = 0) (hfu : ∀ x, f x + A g x = u x) (hgv : ∀ y, g y + B f y = v y)
    {UX UY eX eY FX FY : ℝ} (hUX : UX < 1) (hUY : UY < 1) (huU : ∀ x, -UX ≤ u x)
    (hvU : ∀ y, -UY ≤ v y) (he : nrm νX u * nrm νY v ≤ eX * eY)
    (hFX : 0 ≤ FX) (hFY : 0 ≤ FY) (hfF : ∀ x, |f x| ≤ FX) (hgF : ∀ y, |g y| ≤ FY)
    (h : X → ℝ) (k : Y → ℝ) (hh : ip νX h (fun x => 1 + u x) = 0)
    (hk : ip νY (fun y => 1 + v y) k = 0) :
    |reweightForm ν f g h k| ≤
      (ρ * (1 + FX + FY) + eX * eY) / Real.sqrt ((1 - UX) * (1 - UY)) *
        Real.sqrt (νX.expect (fun x => (1 + u x) * h x ^ 2)) *
        Real.sqrt (νY.expect (fun y => (1 + v y) * k y ^ 2)) := by
  obtain ⟨hu, hv⟩ := repair_marginals ν νX νY hmX hmY A B hA hB f g u v hfu hgv
  exact additive_cancellation ν νX νY hmX hmY A B hA hB hρ hAρ hBρ f g hf0 hg0 u v hu hv hUX
    hUY huU hvU he hFX hFY hfF hgF h k hh hk

end Sarkozy.Structured
