module

public import Sarkozy.L20Cap.Rectangle

/-!
# The pair-domain gap (`prop:l20-pair-gap`) and the two-block comparison

`paper/sections/20_middle_reference.tex`, `prop:l20-pair-gap`, and the comparison step of
`prop:l20-rank4` ("The consequence"). Notation of `Sarkozy.L20Cap.Rectangle`.

Proved:
* **`Rv_exact`** (the exact singleton action of the proof of `prop:l20-pair-gap`): for every
  `h` on the labels,
  `E_b[𝖱(C; b)(h(b₀) + h(b₁))] = 2 (\bar𝖪(C) - 16q)/(1 - q) · E_z 𝖪(z, C) h(z)`;
  with `𝐯h(b) = (h(b₀) + h(b₁))/√2` and `𝐳h = E_z 𝖪 h/(√15 r)` this is
  `𝖱𝐯 = √30 r (\bar𝖪 - 16q)/(1 - q) 𝐳`.
* **`two_block`** (the scalar comparison matrix): if `‖Xf₁‖ ≤ τ‖f₁‖`, `‖Xf₂‖ ≤ l‖f₂‖`,
  `|⟨Xf₁, Xf₂⟩| ≤ x‖f₁‖‖f₂‖` for orthogonal `f₁, f₂`, and `0 < Δ ≤ τ² - l²`, then
  `‖X(f₁ + f₂)‖² ≤ (τ² + x²/Δ)‖f₁ + f₂‖²`; the largest eigenvalue of
  `((τ², x), (x, l²))` is at most `τ² + x²/Δ`.
* **`pair_gap`** (`prop:l20-pair-gap`): for `𝖱_c` on `L²(μ^pair)`, if every function splits as
  `f₁ + f₂` with `f₁` in the range of `𝐯' = 𝐯/√g_𝐯` and `f₂` orthogonal to it, with the three
  bounds `τ_g`, `l_g = 2r + N_A`, `x_g = 2rw_g + τ_gN_A` of the proof, and
  `Δ_g = 30q - l_g² > 0`, `τ_g² ≥ 30q`, then `‖𝖱_c‖ ≤ c_gap = (τ_g² + x_g²/Δ_g)^{1/2}`.
* `tau_sq_ge`: `τ_g² ≥ 30q` from `M_g ≥ 15` (as in the proof).
* `vfeat_sq`: `𝐯^*𝐯 = g_𝐯 I` on `𝓗`, `g_𝐯 = (1 - 2q)/(1 - q)` (`prop:l20-rank4`(a), last claim).

The three block bounds are hypotheses of `pair_gap`: the Gram identity
`(𝖱𝐯')^*𝖱𝐯' = 2qE[(\bar𝖪 - 16q)²(16\bar𝖪 - \bar𝖪²)]/((1 - q)²(1 - 2q)) I` (which uses
`lem:spec:affpair`(d)), the complement bound (`𝐯^* = 0` there, `‖𝐰‖, ‖𝐞‖ ≤ 1`, `‖𝖱_∘‖ ≤ N_A`)
and the cross bound (`e_g`, `w_g`, with `ρ_{𝐳𝐰}` of `prop:l20-rank4`(c)) are not formalized.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (PairT F)]

/-- **The exact action of `𝖱` on the pair singletons** (proof of `prop:l20-pair-gap`):
`E_b[𝖱(C; b)(h(b₀) + h(b₁))] = 2(\bar𝖪 - 16q)/(1 - q) · (∑_z 𝖪(z, C)h(z))/p`. -/
theorem Rv_exact (hm1 : quadraticChar F (-1) = -1) (C : CoreT F) (h : F → ℝ) :
    (pairLaw (F := F)).expect (fun b => Rk C b * (h b.1.1 + h b.1.2)) =
      2 * (Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, Kz z C.1 * h z) / Fintype.card F) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  set g : F × F → ℝ := fun y => Kz y.1 C.1 * Kz y.2 C.1 * (h y.1 + h y.2) with hg
  have e : (pairLaw (F := F)).expect (fun b => Rk C b * (h b.1.1 + h b.1.2)) =
      (pairLaw (F := F)).expect (fun b => g b.1) := rfl
  rw [e, pairLaw_expect g]
  simp only [hg]
  have h1 : ∑ y : F, ∑ y' : F, Kz y C.1 * Kz y' C.1 * (h y + h y') =
      2 * ((∑ y, Kz y C.1) * ∑ y, Kz y C.1 * h y) := by
    have : ∀ y y' : F, Kz y C.1 * Kz y' C.1 * (h y + h y') =
        (Kz y C.1 * h y) * Kz y' C.1 + Kz y C.1 * (Kz y' C.1 * h y') := fun y y' => by ring
    simp only [this, sum_add_distrib, ← sum_mul_sum]
    ring
  have h2 : ∑ y : F, Kz y C.1 * Kz y C.1 * (h y + h y) = 32 * ∑ y, Kz y C.1 * h y := by
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    have := Kz_sq hm1 C.2 y
    rw [sq] at this
    rw [this]
    ring
  rw [h1, h2, Kbar]
  field_simp
  ring

/-- **`𝐯^*𝐯 = g_𝐯 I` on `𝓗`** (`prop:l20-rank4`(a), used in `prop:l20-pair-gap`): for `h` of mean
zero, `E_b[(h(b₀) + h(b₁))²] = 2(1 - 2q)/(1 - q) · E_z h²`, i.e. `‖𝐯h‖² = g_𝐯‖h‖²` with
`𝐯h(b) = (h(b₀) + h(b₁))/√2` and `g_𝐯 = (1 - 2q)/(1 - q)`. -/
theorem vfeat_sq (h : F → ℝ) (h0 : ∑ z, h z = 0) :
    (pairLaw (F := F)).expect (fun b => (h b.1.1 + h b.1.2) ^ 2) =
      2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, h z ^ 2) / Fintype.card F) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  set g : F × F → ℝ := fun y => (h y.1 + h y.2) ^ 2 with hg
  have e : (pairLaw (F := F)).expect (fun b => (h b.1.1 + h b.1.2) ^ 2) =
      (pairLaw (F := F)).expect (fun b => g b.1) := rfl
  rw [e, pairLaw_expect g]
  simp only [hg]
  have h1 : ∑ y : F, ∑ y' : F, (h y + h y') ^ 2 =
      2 * (Fintype.card F : ℝ) * ∑ y, h y ^ 2 + 2 * (∑ y, h y) * ∑ y, h y := by
    have : ∀ y y' : F, (h y + h y') ^ 2 = h y ^ 2 + h y' ^ 2 + 2 * (h y * h y') := fun y y' => by
      ring
    simp only [this, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
    rw [← sum_mul]
    ring
  have h2 : ∑ y : F, (h y + h y) ^ 2 = 4 * ∑ y, h y ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  rw [h1, h2, h0]
  field_simp
  ring

/-! ## The two-block comparison -/

section TwoBlock

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] in
theorem recOp_add (β : FiniteLaw Y) (A : X → Y → ℝ) (f₁ f₂ : Y → ℝ) :
    recOp β A (fun y => f₁ y + f₂ y) = fun x => recOp β A f₁ x + recOp β A f₂ x := by
  funext x
  unfold recOp
  rw [← FiniteLaw.expect_add]
  exact β.expect_congr fun y => by ring

theorem nrm_sq_add (μ : FiniteLaw X) (u v : X → ℝ) :
    nrm μ (fun x => u x + v x) ^ 2 = nrm μ u ^ 2 + 2 * ip μ u v + nrm μ v ^ 2 := by
  rw [nrm_sq_eq, nrm_sq_eq, nrm_sq_eq]
  unfold ip
  rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_add, ← FiniteLaw.expect_add]
  exact μ.expect_congr fun x => by ring

/-- **The two-block comparison** (`prop:l20-rank4`, "The consequence"; `prop:l20-pair-gap`):
for orthogonal `f₁, f₂` with `‖Xf₁‖ ≤ τ‖f₁‖`, `‖Xf₂‖ ≤ l‖f₂‖`, `|⟨Xf₁, Xf₂⟩| ≤ x‖f₁‖‖f₂‖`
and `0 < Δ ≤ τ² - l²`, `‖X(f₁ + f₂)‖² ≤ (τ² + x²/Δ)‖f₁ + f₂‖²`. -/
theorem two_block (α : FiniteLaw X) (β : FiniteLaw Y) (A : X → Y → ℝ) {τ l x Δ : ℝ}
    (hΔ : 0 < Δ) (hτl : Δ ≤ τ ^ 2 - l ^ 2)
    (f₁ f₂ : Y → ℝ) (horth : ip β f₁ f₂ = 0)
    (h₁ : nrm α (recOp β A f₁) ≤ τ * nrm β f₁) (h₂ : nrm α (recOp β A f₂) ≤ l * nrm β f₂)
    (h₁₂ : |ip α (recOp β A f₁) (recOp β A f₂)| ≤ x * nrm β f₁ * nrm β f₂) :
    nrm α (recOp β A (fun y => f₁ y + f₂ y)) ^ 2 ≤
      (τ ^ 2 + x ^ 2 / Δ) * nrm β (fun y => f₁ y + f₂ y) ^ 2 := by
  rw [recOp_add, nrm_sq_add, nrm_sq_add β, horth]
  set s := nrm β f₁
  set t := nrm β f₂
  have hs : 0 ≤ s := nrm_nonneg _ _
  have ht : 0 ≤ t := nrm_nonneg _ _
  have e1 : nrm α (recOp β A f₁) ^ 2 ≤ τ ^ 2 * s ^ 2 := by
    have := pow_le_pow_left₀ (nrm_nonneg _ _) h₁ 2
    nlinarith
  have e2 : nrm α (recOp β A f₂) ^ 2 ≤ l ^ 2 * t ^ 2 := by
    have := pow_le_pow_left₀ (nrm_nonneg _ _) h₂ 2
    nlinarith
  have e3 : 2 * ip α (recOp β A f₁) (recOp β A f₂) ≤ 2 * (x * s * t) := by
    have := (le_abs_self _).trans h₁₂
    linarith
  -- `2xst ≤ (x²/Δ)s² + Δt²`
  have hamgm : 2 * (x * s * t) ≤ x ^ 2 / Δ * s ^ 2 + Δ * t ^ 2 := by
    have key : 0 ≤ (x * s - Δ * t) ^ 2 / Δ := div_nonneg (sq_nonneg _) hΔ.le
    have expand : (x * s - Δ * t) ^ 2 / Δ = x ^ 2 / Δ * s ^ 2 + Δ * t ^ 2 - 2 * (x * s * t) := by
      field_simp
      ring
    linarith
  have hD : Δ * t ^ 2 ≤ (τ ^ 2 - l ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hτl (sq_nonneg t)
  have hxd : 0 ≤ x ^ 2 / Δ * t ^ 2 := mul_nonneg (div_nonneg (sq_nonneg x) hΔ.le) (sq_nonneg t)
  have hexp : (τ ^ 2 + x ^ 2 / Δ) * (s ^ 2 + 2 * 0 + t ^ 2) =
      τ ^ 2 * s ^ 2 + x ^ 2 / Δ * s ^ 2 + τ ^ 2 * t ^ 2 + x ^ 2 / Δ * t ^ 2 := by ring
  rw [hexp]
  nlinarith

end TwoBlock

/-! ## The pair-domain gap -/

/-- `τ_g² ≥ 30q` (proof of `prop:l20-pair-gap`): `τ_g² = 2qM_g/((1 - q)²(1 - 2q))` with
`M_g ≥ 15` and `0 < q < 1/2`. -/
theorem tau_sq_ge {q Mg : ℝ} (hq : 0 < q) (hq2 : 2 * q < 1) (hM : 15 ≤ Mg) :
    30 * q ≤ 2 * q * Mg / ((1 - q) ^ 2 * (1 - 2 * q)) := by
  have h1 : 0 < 1 - 2 * q := by linarith
  have h2 : 0 < 1 - q := by linarith
  have hden : 0 < (1 - q) ^ 2 * (1 - 2 * q) := mul_pos (pow_pos h2 2) h1
  have hden1 : (1 - q) ^ 2 * (1 - 2 * q) ≤ 1 := by nlinarith
  rw [le_div_iff₀ hden]
  nlinarith

variable [Nonempty (CoreT F)]

/-- **`prop:l20-pair-gap`**: `‖𝖱_c‖ ≤ c_gap = (τ_g² + x_g²/Δ_g)^{1/2}`, given, for every `f`
on the pairs, a splitting `f = f₁ + f₂` into orthogonal parts (`f₁` in the range of `𝐯'`, `f₂`
orthogonal to it) with `‖𝖱_c f₁‖ ≤ τ_g‖f₁‖`, `‖𝖱_c f₂‖ ≤ l_g‖f₂‖`,
`|⟨𝖱_c f₁, 𝖱_c f₂⟩| ≤ x_g‖f₁‖‖f₂‖`, `τ_g² ≥ 30q` and `Δ_g = 30q - l_g² > 0`. -/
theorem pair_gap {q τg lg xg : ℝ}
    (hτq : 30 * q ≤ τg ^ 2) (hΔ : 0 < 30 * q - lg ^ 2)
    (hsplit : ∀ f : PairT F → ℝ, ∃ f₁ f₂ : PairT F → ℝ, f = (fun b => f₁ b + f₂ b) ∧
      ip (pairLaw (F := F)) f₁ f₂ = 0 ∧
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc f₁) ≤ τg * nrm (pairLaw (F := F)) f₁ ∧
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc f₂) ≤ lg * nrm (pairLaw (F := F)) f₂ ∧
      |ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc f₁) (recOp (pairLaw (F := F)) Rc f₂)| ≤
        xg * nrm (pairLaw (F := F)) f₁ * nrm (pairLaw (F := F)) f₂)
    (f : PairT F → ℝ) :
    nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc f) ≤
      Real.sqrt (τg ^ 2 + xg ^ 2 / (30 * q - lg ^ 2)) * nrm (pairLaw (F := F)) f := by
  obtain ⟨f₁, f₂, rfl, horth, h₁, h₂, h₁₂⟩ := hsplit f
  have hsq := two_block coreLaw pairLaw Rc hΔ (by linarith) f₁ f₂ horth h₁ h₂ h₁₂
  have hc0 : 0 ≤ τg ^ 2 + xg ^ 2 / (30 * q - lg ^ 2) :=
    add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hΔ.le)
  apply nrm_le_of_sq_le _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt hc0]
  exact hsq

end Sarkozy.L20Cap
