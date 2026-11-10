module

public import Sarkozy.Structured.MarkovCompletion

/-!
# Centred additive correction (`lem:record:centered-correction`, part (a))

`lem:record:centered-correction` (`paper/sections/17_completion_repair.tex`, brief F). The
setting:
* `ν` is a probability measure on a finite set, and `K` a kernel with `∫ K d(ν⊗ν) = 1`;
* `K = 𝟙⊗𝟙 + δ_L⊗𝟙 + 𝟙⊗δ_R + K_c`, with `δ_L = K𝟙 - 𝟙`, `δ_R = K*𝟙 - 𝟙` and
  `K_c = Π_⊥ K Π_⊥`;
* `K' = (1 + f(x) + g(y)) K`.

Part (a) bounds the centred correction `D = Π_⊥(K' - K)Π_⊥`:
`‖D‖ ≤ ‖f‖‖δ_R‖ + ‖δ_L‖‖g‖ + (‖f‖_∞ + ‖g‖_∞)‖K_c‖ ≤ 2F(c + e)`.

As in `Sarkozy/Structured/MarkovCompletion.lean`, a compression `Π_⊥ κ Π_⊥` is identified
with the bilinear form of `κ` on centred functions (`kform`).
* `centeredKernel`: `K_c = K - 𝟙⊗𝟙 - δ_L⊗𝟙 - 𝟙⊗δ_R`. Its row and column means vanish when
  `K` has mass one (`centeredKernel_row`, `centeredKernel_col`).
* `centered_correction_decomp`: for centred `φ, ψ`,
  `⟨φ, Dψ⟩ = E[fφ]⟨δ_R, ψ⟩ + ⟨φ, δ_L⟩E[gψ] + ⟨fφ, K_c ψ⟩ + ⟨φ, K_c(gψ)⟩`.
  This is the paper's decomposition `D = (Π_⊥f)⊗δ_R + δ_L⊗(Π_⊥g) + Π_⊥(fK_c)Π_⊥ + Π_⊥(K_c g)Π_⊥`
  read on centred functions.
* `centered_correction_norm`: the bound of (a).

Parts (b) and (c) use the density transport `lem:record:actual-correlation`(b) and are not
formalized here.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Recentering

variable {X : Type*} [Fintype X]

/-- `δ_L(x) = E_y K(x, y) - 1`. -/
noncomputable def deltaL (ν : FiniteLaw X) (K : X × X → ℝ) (x : X) : ℝ :=
  ν.expect (fun y => K (x, y)) - 1

/-- `δ_R(y) = E_x K(x, y) - 1`. -/
noncomputable def deltaR (ν : FiniteLaw X) (K : X × X → ℝ) (y : X) : ℝ :=
  ν.expect (fun x => K (x, y)) - 1

/-- `K_c = K - 𝟙⊗𝟙 - δ_L⊗𝟙 - 𝟙⊗δ_R`. -/
noncomputable def centeredKernel (ν : FiniteLaw X) (K : X × X → ℝ) (p : X × X) : ℝ :=
  K p - 1 - deltaL ν K p.1 - deltaR ν K p.2

/-- The double integral as an iterated expectation in either order. -/
theorem expect_swap (ν : FiniteLaw X) (F : X → X → ℝ) :
    ν.expect (fun x => ν.expect (fun y => F x y)) =
      ν.expect (fun y => ν.expect (fun x => F x y)) := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring

/-- `E δ_R = 0` when `K` has mass one. -/
theorem expect_deltaR (ν : FiniteLaw X) (K : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) :
    ν.expect (deltaR ν K) = 0 := by
  unfold deltaR
  rw [ν.expect_sub, ν.expect_const, ← expect_swap ν (fun x y => K (x, y)), hK, sub_self]

/-- `E δ_L = 0` when `K` has mass one. -/
theorem expect_deltaL (ν : FiniteLaw X) (K : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) :
    ν.expect (deltaL ν K) = 0 := by
  unfold deltaL
  rw [ν.expect_sub, ν.expect_const, hK, sub_self]

/-- The row means of `K_c` vanish. -/
theorem centeredKernel_row (ν : FiniteLaw X) (K : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) (x : X) :
    ν.expect (fun y => centeredKernel ν K (x, y)) = 0 := by
  unfold centeredKernel
  dsimp only
  rw [ν.expect_sub, ν.expect_sub, ν.expect_sub, ν.expect_const, ν.expect_const,
    expect_deltaR ν K hK]
  unfold deltaL
  ring

/-- The column means of `K_c` vanish. -/
theorem centeredKernel_col (ν : FiniteLaw X) (K : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) (y : X) :
    ν.expect (fun x => centeredKernel ν K (x, y)) = 0 := by
  unfold centeredKernel
  dsimp only
  rw [ν.expect_sub, ν.expect_sub, ν.expect_sub, ν.expect_const, ν.expect_const,
    expect_deltaL ν K hK]
  unfold deltaR
  ring

/-- A kernel with vanishing column means only sees the centred part of the left argument. -/
theorem kform_center_left_zero (ν : FiniteLaw X) (K : X × X → ℝ)
    (hcol : ∀ y, ν.expect (fun x => K (x, y)) = 0) (φ ψ : X → ℝ) :
    kform ν ν K φ ψ = kform ν ν K (center ν φ) ψ := by
  unfold kform center
  have h : ∀ x, ν.expect (fun y => (φ x - ν.expect φ) * ψ y * K (x, y)) =
      ν.expect (fun y => φ x * ψ y * K (x, y)) -
        ν.expect φ * ν.expect (fun y => ψ y * K (x, y)) := by
    intro x
    rw [← ν.expect_const_mul, ← ν.expect_sub]
    exact ν.expect_congr fun y => by ring
  simp_rw [h]
  rw [ν.expect_sub, ν.expect_const_mul, expect_swap ν (fun x y => ψ y * K (x, y))]
  have h2 : ∀ y, ν.expect (fun x => ψ y * K (x, y)) = 0 := by
    intro y
    rw [ν.expect_const_mul, hcol y, mul_zero]
  simp_rw [h2]
  simp

/-- A kernel with vanishing row means only sees the centred part of the right argument. -/
theorem kform_center_right_zero (ν : FiniteLaw X) (K : X × X → ℝ)
    (hrow : ∀ x, ν.expect (fun y => K (x, y)) = 0) (φ ψ : X → ℝ) :
    kform ν ν K φ ψ = kform ν ν K φ (center ν ψ) := by
  unfold kform center
  have h : ∀ x, ν.expect (fun y => φ x * (ψ y - ν.expect ψ) * K (x, y)) =
      ν.expect (fun y => φ x * ψ y * K (x, y)) -
        ν.expect ψ * (φ x * ν.expect (fun y => K (x, y))) := by
    intro x
    rw [← ν.expect_const_mul, ← ν.expect_const_mul, ← ν.expect_sub]
    exact ν.expect_congr fun y => by ring
  simp_rw [h, hrow, mul_zero]
  simp

/-- **The decomposition of `D` on centred functions** (`lem:record:centered-correction`(a)):
for `E φ = E ψ = 0`, the form of `(f(x) + g(y))K` at `(φ, ψ)` is
`E[fφ] ⟨δ_R, ψ⟩ + ⟨φ, δ_L⟩ E[gψ] + ⟨fφ, K_c ψ⟩ + ⟨φ, K_c(gψ)⟩`. -/
theorem centered_correction_decomp (ν : FiniteLaw X) (K : X × X → ℝ) (f g φ ψ : X → ℝ)
    (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ =
      ν.expect (fun x => f x * φ x) * ip ν (deltaR ν K) ψ +
        ip ν φ (deltaL ν K) * ν.expect (fun y => g y * ψ y) +
        kform ν ν (centeredKernel ν K) (fun x => f x * φ x) ψ +
        kform ν ν (centeredKernel ν K) φ (fun y => g y * ψ y) := by
  have hK : ∀ p : X × X, K p = centeredKernel ν K p + 1 + deltaL ν K p.1 + deltaR ν K p.2 := by
    intro p; unfold centeredKernel; ring
  -- the form of a rank-one kernel `a ⊗ b`
  have hrank : ∀ (a b φ' ψ' : X → ℝ), kform ν ν (fun p => a p.1 * b p.2) φ' ψ' =
      ν.expect (fun x => φ' x * a x) * ν.expect (fun y => ψ' y * b y) := by
    intro a b φ' ψ'
    unfold kform
    rw [← ν.expect_mul_const]
    exact ν.expect_congr fun x => by
      rw [← ν.expect_const_mul]; exact ν.expect_congr fun y => by ring
  have e : ∀ p : X × X, (f p.1 + g p.2) * K p =
      (fun p : X × X => f p.1 * centeredKernel ν K p) p +
      (fun p : X × X => centeredKernel ν K p * g p.2) p +
      (fun p : X × X => (f p.1 + f p.1 * deltaL ν K p.1) * 1) p +
      (fun p : X × X => f p.1 * deltaR ν K p.2) p +
      (fun p : X × X => (1 + deltaL ν K p.1) * g p.2) p +
      (fun p : X × X => 1 * (g p.2 * deltaR ν K p.2)) p := by
    intro p; rw [hK p]; ring
  rw [kform_congr ν ν e, kform_add, kform_add, kform_add, kform_add, kform_add,
    kform_mul_left ν ν f (centeredKernel ν K), kform_mul_right ν ν g (centeredKernel ν K),
    hrank (fun x => f x + f x * deltaL ν K x) (fun _ => 1), hrank f (deltaR ν K),
    hrank (fun x => 1 + deltaL ν K x) g, hrank (fun _ => 1) (fun y => g y * deltaR ν K y)]
  -- the terms with a constant factor vanish
  have h1 : ν.expect (fun y => ψ y * (1 : ℝ)) = 0 := by
    rw [show (fun y => ψ y * (1 : ℝ)) = ψ from funext fun y => mul_one _, hψ]
  have h2 : ν.expect (fun x => φ x * (1 : ℝ)) = 0 := by
    rw [show (fun x => φ x * (1 : ℝ)) = φ from funext fun x => mul_one _, hφ]
  rw [h1, h2]
  unfold ip
  have e3 : ν.expect (fun y => ψ y * deltaR ν K y) = ν.expect (fun y => deltaR ν K y * ψ y) :=
    ν.expect_congr fun y => mul_comm _ _
  have e4 : ν.expect (fun x => φ x * (1 + deltaL ν K x)) =
      ν.expect (fun x => φ x * deltaL ν K x) := by
    have : (fun x => φ x * (1 + deltaL ν K x)) = fun x => φ x + φ x * deltaL ν K x := by
      funext x; ring
    rw [this, ν.expect_add, hφ, zero_add]
  have e6 : ν.expect (fun y => ψ y * g y) = ν.expect (fun y => g y * ψ y) :=
    ν.expect_congr fun y => mul_comm _ _
  have e7 : ν.expect (fun x => φ x * f x) = ν.expect (fun x => f x * φ x) :=
    ν.expect_congr fun x => mul_comm _ _
  rw [e3, e4, e6, e7]
  ring

/-- **`lem:record:centered-correction`(a), the bound**: if `‖K_c‖ ≤ c` (on centred functions),
`‖δ_L‖, ‖δ_R‖ ≤ e` and `|f|, |g| ≤ F`, then for centred `φ, ψ`
`|⟨φ, Dψ⟩| ≤ (‖f‖‖δ_R‖ + ‖δ_L‖‖g‖ + 2Fc) ‖φ‖‖ψ‖ ≤ 2F(c + e) ‖φ‖‖ψ‖`. -/
theorem centered_correction_norm (ν : FiniteLaw X) (K : X × X → ℝ)
    (hK : ν.expect (fun x => ν.expect (fun y => K (x, y))) = 1) {c e F : ℝ} (hc : 0 ≤ c)
    (hF : 0 ≤ F)
    (hKc : ∀ φ ψ, ν.expect φ = 0 → ν.expect ψ = 0 →
      |kform ν ν (centeredKernel ν K) φ ψ| ≤ c * nrm ν φ * nrm ν ψ)
    (hδL : nrm ν (deltaL ν K) ≤ e) (hδR : nrm ν (deltaR ν K) ≤ e)
    (f g : X → ℝ) (hf : ∀ x, |f x| ≤ F) (hg : ∀ y, |g y| ≤ F) (φ ψ : X → ℝ)
    (hφ : ν.expect φ = 0) (hψ : ν.expect ψ = 0) :
    |kform ν ν (fun p => (f p.1 + g p.2) * K p) φ ψ| ≤ 2 * F * (c + e) * nrm ν φ * nrm ν ψ := by
  rw [centered_correction_decomp ν K f g φ ψ hφ hψ]
  have hn1 : 0 ≤ nrm ν φ := Real.sqrt_nonneg _
  have hn2 : 0 ≤ nrm ν ψ := Real.sqrt_nonneg _
  have he : 0 ≤ e := (Real.sqrt_nonneg _).trans hδL
  have hfn : nrm ν f ≤ F := nrm_le_of_abs_le ν f hF hf
  have hgn : nrm ν g ≤ F := nrm_le_of_abs_le ν g hF hg
  -- the rank-one terms
  have t1 : |ν.expect (fun x => f x * φ x) * ip ν (deltaR ν K) ψ| ≤ F * e * nrm ν φ * nrm ν ψ := by
    rw [abs_mul]
    have a1 : |ν.expect (fun x => f x * φ x)| ≤ F * nrm ν φ := by
      have := abs_ip_le ν f φ
      unfold ip at this
      exact this.trans (mul_le_mul_of_nonneg_right hfn hn1)
    have a2 : |ip ν (deltaR ν K) ψ| ≤ e * nrm ν ψ :=
      (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_right hδR hn2)
    calc |ν.expect (fun x => f x * φ x)| * |ip ν (deltaR ν K) ψ| ≤ (F * nrm ν φ) * (e * nrm ν ψ) :=
          mul_le_mul a1 a2 (abs_nonneg _) (mul_nonneg hF hn1)
      _ = F * e * nrm ν φ * nrm ν ψ := by ring
  have t2 : |ip ν φ (deltaL ν K) * ν.expect (fun y => g y * ψ y)| ≤ F * e * nrm ν φ * nrm ν ψ := by
    rw [abs_mul]
    have a1 : |ip ν φ (deltaL ν K)| ≤ nrm ν φ * e :=
      (abs_ip_le ν _ _).trans (mul_le_mul_of_nonneg_left hδL hn1)
    have a2 : |ν.expect (fun y => g y * ψ y)| ≤ F * nrm ν ψ := by
      have := abs_ip_le ν g ψ
      unfold ip at this
      exact this.trans (mul_le_mul_of_nonneg_right hgn hn2)
    calc |ip ν φ (deltaL ν K)| * |ν.expect (fun y => g y * ψ y)| ≤ (nrm ν φ * e) * (F * nrm ν ψ) :=
          mul_le_mul a1 a2 (abs_nonneg _) (mul_nonneg hn1 he)
      _ = F * e * nrm ν φ * nrm ν ψ := by ring
  -- the `K_c` terms: `K_c` only sees the centred parts
  have t3 : |kform ν ν (centeredKernel ν K) (fun x => f x * φ x) ψ| ≤
      c * F * nrm ν φ * nrm ν ψ := by
    rw [kform_center_left_zero ν (centeredKernel ν K) (centeredKernel_col ν K hK)]
    refine (hKc _ ψ (expect_center ν _) hψ).trans ?_
    apply mul_le_mul_of_nonneg_right _ hn2
    calc c * nrm ν (center ν (fun x => f x * φ x)) ≤ c * (F * nrm ν φ) :=
          mul_le_mul_of_nonneg_left ((nrm_center_le ν _).trans (nrm_mul_le ν f φ hF hf)) hc
      _ = c * F * nrm ν φ := by ring
  have t4 : |kform ν ν (centeredKernel ν K) φ (fun y => g y * ψ y)| ≤
      c * F * nrm ν φ * nrm ν ψ := by
    rw [kform_center_right_zero ν (centeredKernel ν K) (centeredKernel_row ν K hK)]
    refine (hKc φ _ hφ (expect_center ν _)).trans ?_
    calc c * nrm ν φ * nrm ν (center ν (fun y => g y * ψ y)) ≤ c * nrm ν φ * (F * nrm ν ψ) :=
          mul_le_mul_of_nonneg_left ((nrm_center_le ν _).trans (nrm_mul_le ν g ψ hF hg))
            (mul_nonneg hc hn1)
      _ = c * F * nrm ν φ * nrm ν ψ := by ring
  have habs := abs_add_le (ν.expect (fun x => f x * φ x) * ip ν (deltaR ν K) ψ +
      ip ν φ (deltaL ν K) * ν.expect (fun y => g y * ψ y) +
      kform ν ν (centeredKernel ν K) (fun x => f x * φ x) ψ)
    (kform ν ν (centeredKernel ν K) φ (fun y => g y * ψ y))
  have habs2 := abs_add_le (ν.expect (fun x => f x * φ x) * ip ν (deltaR ν K) ψ +
      ip ν φ (deltaL ν K) * ν.expect (fun y => g y * ψ y))
    (kform ν ν (centeredKernel ν K) (fun x => f x * φ x) ψ)
  have habs3 := abs_add_le (ν.expect (fun x => f x * φ x) * ip ν (deltaR ν K) ψ)
    (ip ν φ (deltaL ν K) * ν.expect (fun y => g y * ψ y))
  have hsum : F * e * nrm ν φ * nrm ν ψ + F * e * nrm ν φ * nrm ν ψ +
      c * F * nrm ν φ * nrm ν ψ + c * F * nrm ν φ * nrm ν ψ =
      2 * F * (c + e) * nrm ν φ * nrm ν ψ := by ring
  linarith

end Sarkozy.Structured
