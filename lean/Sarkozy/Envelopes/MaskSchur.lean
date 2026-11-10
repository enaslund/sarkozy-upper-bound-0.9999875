module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# The mask condition for diagonal envelopes (`lem:oct24:mask-schur`(c))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(c), the diagonal case: if the weights
`d_v > 0` on the tensor features satisfy `eq:oct24:mask-schur`,
`(∑_{A(v)=A} α(v)²/d_v)(∑_{A(w)=A^c} α(w)²/d_w) ≤ 1` for every complementary pair of masks, then
the tensor product of the stars lies between `± diag(d_v)`.

**Form (abstract, with the paper's hypotheses).** The tensor features `v` form a finite type `V`;
the mask of a feature is `σ v` in a finite type `S` of sectors with an involution `c` (the
complement `A ↦ A^c`). The tensor of the stars is a block operator `T_{wv} : E → E` on `⊕_v E`
(`E` a real inner product space); the two facts used by the paper's proof are hypotheses:
* (sectors) a star maps its centre to its arms and back, so `T_{wv} = 0` unless `σ w = c (σ v)`;
* (block norms) `‖T_{wv}‖ ≤ α(v) α(w)`, the products of the arm norm bounds.
`mask_schur` proves `|∑_{v,w} ⟨x_w, T_{wv} x_v⟩| ≤ ∑_v d_v ‖x_v‖²` for every `x`, i.e.
`-D ⪯ T ⪯ D` for the self-adjoint `T`; weights on features outside the stars only add a positive
diagonal. The proof is the paper's: on each pair of complementary sectors the conjugated block is
bounded by the outer product of `(α(v)/√d_v)_v` and `(α(w)/√d_w)_w`. `one_star_gain` is
`rem:envelope-gain`: for one arm, the condition is `d_c d_a ≥ α²`.
-/

namespace Sarkozy.Envelopes

open Finset
open scoped RealInnerProductSpace

/-- Weighted Cauchy–Schwarz: `(∑ β_v y_v)² ≤ (∑ β_v²/d_v)(∑ d_v y_v²)` for `d_v > 0`. -/
theorem weighted_cauchy_schwarz {V : Type*} (s : Finset V) (β y d : V → ℝ)
    (hd : ∀ v ∈ s, 0 < d v) :
    (∑ v ∈ s, β v * y v) ^ 2 ≤ (∑ v ∈ s, β v ^ 2 / d v) * ∑ v ∈ s, d v * y v ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq s (fun v => β v / Real.sqrt (d v))
    (fun v => Real.sqrt (d v) * y v)
  have e1 : ∀ v ∈ s, β v / Real.sqrt (d v) * (Real.sqrt (d v) * y v) = β v * y v := by
    intro v hv
    have : Real.sqrt (d v) ≠ 0 := (Real.sqrt_pos.2 (hd v hv)).ne'
    field_simp
  have e2 : ∀ v ∈ s, (β v / Real.sqrt (d v)) ^ 2 = β v ^ 2 / d v := by
    intro v hv
    rw [div_pow, Real.sq_sqrt (hd v hv).le]
  have e3 : ∀ v ∈ s, (Real.sqrt (d v) * y v) ^ 2 = d v * y v ^ 2 := by
    intro v hv
    rw [mul_pow, Real.sq_sqrt (hd v hv).le]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_congr rfl e3] at h
  exact h

/-- **`lem:oct24:mask-schur`(c), the mask Schur test.** Let `σ : V → S` assign to each tensor
feature its mask, `c` the complement of masks (an involution), `T w v` the blocks of the tensor of
the stars, with `T w v = 0` unless `σ w = c (σ v)` and `‖T w v y‖ ≤ α v * α w * ‖y‖`. If the
weights `d > 0` satisfy, for every mask `A`,
`(∑_{σ v = A} α(v)²/d_v)(∑_{σ w = c A} α(w)²/d_w) ≤ 1` (`eq:oct24:mask-schur`), then
`|∑_{v,w} ⟪x_w, T_{wv} x_v⟫| ≤ ∑_v d_v ‖x_v‖²`. -/
theorem mask_schur {V S E : Type*} [Fintype V] [Fintype S] [DecidableEq S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (σ : V → S) (c : S → S)
    (hc : ∀ A, c (c A) = A) (T : V → V → E →ₗ[ℝ] E) (α d : V → ℝ) (hα : ∀ v, 0 ≤ α v)
    (hd : ∀ v, 0 < d v) (hsec : ∀ v w, σ w ≠ c (σ v) → T w v = 0)
    (hnorm : ∀ v w y, ‖T w v y‖ ≤ α v * α w * ‖y‖)
    (hmask : ∀ A, (∑ v ∈ univ.filter (fun v => σ v = A), α v ^ 2 / d v) *
      (∑ w ∈ univ.filter (fun w => σ w = c A), α w ^ 2 / d w) ≤ 1) (x : V → E) :
    |∑ v, ∑ w, ⟪x w, T w v (x v)⟫| ≤ ∑ v, d v * ‖x v‖ ^ 2 := by
  -- sector sums
  set a : S → ℝ := fun A => ∑ v ∈ univ.filter (fun v => σ v = A), α v * ‖x v‖ with ha_def
  set P : S → ℝ := fun A => ∑ v ∈ univ.filter (fun v => σ v = A), α v ^ 2 / d v with hP_def
  set Q : S → ℝ := fun A => ∑ v ∈ univ.filter (fun v => σ v = A), d v * ‖x v‖ ^ 2 with hQ_def
  have ha0 : ∀ A, 0 ≤ a A := fun A => sum_nonneg fun v _ => mul_nonneg (hα v) (norm_nonneg _)
  have hP0 : ∀ A, 0 ≤ P A := fun A => sum_nonneg fun v _ =>
    div_nonneg (sq_nonneg _) (hd v).le
  have hQ0 : ∀ A, 0 ≤ Q A := fun A => sum_nonneg fun v _ =>
    mul_nonneg (hd v).le (sq_nonneg _)
  have hCS : ∀ A, a A ^ 2 ≤ P A * Q A := fun A =>
    weighted_cauchy_schwarz _ α (fun v => ‖x v‖) d (fun v _ => hd v)
  -- step 1: bound each term
  have hterm : ∀ v w, |⟪x w, T w v (x v)⟫| ≤
      (if σ w = c (σ v) then α v * ‖x v‖ * (α w * ‖x w‖) else 0) := by
    intro v w
    by_cases h : σ w = c (σ v)
    · simp only [h, ↓reduceIte]
      calc |⟪x w, T w v (x v)⟫| ≤ ‖x w‖ * ‖T w v (x v)‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x w‖ * (α v * α w * ‖x v‖) := mul_le_mul_of_nonneg_left (hnorm v w _) (norm_nonneg _)
        _ = α v * ‖x v‖ * (α w * ‖x w‖) := by ring
    · simp only [h, ↓reduceIte, hsec v w h, LinearMap.zero_apply, inner_zero_right, abs_zero,
        le_refl]
  have h1 : |∑ v, ∑ w, ⟪x w, T w v (x v)⟫| ≤
      ∑ v, ∑ w, (if σ w = c (σ v) then α v * ‖x v‖ * (α w * ‖x w‖) else 0) :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ =>
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w _ => hterm v w))
  -- step 2: the double sum is `∑_A a_A a_{cA}`
  have h2 : ∑ v, ∑ w, (if σ w = c (σ v) then α v * ‖x v‖ * (α w * ‖x w‖) else 0) =
      ∑ v, α v * ‖x v‖ * a (c (σ v)) := by
    refine sum_congr rfl fun v _ => ?_
    rw [ha_def, mul_sum, sum_filter]
  have h3 : ∑ v, α v * ‖x v‖ * a (c (σ v)) = ∑ A, a A * a (c A) := by
    rw [← sum_fiberwise univ σ (fun v => α v * ‖x v‖ * a (c (σ v)))]
    refine sum_congr rfl fun A _ => ?_
    rw [ha_def, sum_mul]
    refine sum_congr rfl fun v hv => ?_
    rw [(mem_filter.1 hv).2]
  -- step 3: `a_A a_{cA} ≤ (Q_A + Q_{cA})/2`
  have h4 : ∀ A, a A * a (c A) ≤ (Q A + Q (c A)) / 2 := by
    intro A
    have hm := hmask A
    have k1 := hCS A
    have k2 := hCS (c A)
    have hprod : (a A * a (c A)) ^ 2 ≤ Q A * Q (c A) := by
      have : (a A * a (c A)) ^ 2 ≤ (P A * Q A) * (P (c A) * Q (c A)) := by
        rw [mul_pow]
        exact mul_le_mul k1 k2 (sq_nonneg _) (mul_nonneg (hP0 A) (hQ0 A))
      have e : (P A * Q A) * (P (c A) * Q (c A)) = (P A * P (c A)) * (Q A * Q (c A)) := by ring
      rw [e] at this
      have hm' : P A * P (c A) ≤ 1 := hm
      nlinarith [mul_nonneg (hQ0 A) (hQ0 (c A)), mul_nonneg (hP0 A) (hP0 (c A))]
    have hamgm : Q A * Q (c A) ≤ ((Q A + Q (c A)) / 2) ^ 2 := by
      nlinarith [sq_nonneg (Q A - Q (c A))]
    have hab0 : 0 ≤ a A * a (c A) := mul_nonneg (ha0 A) (ha0 (c A))
    have hq0 : 0 ≤ (Q A + Q (c A)) / 2 := by linarith [hQ0 A, hQ0 (c A)]
    nlinarith
  -- step 4: `∑_A (Q_A + Q_{cA})/2 = ∑_A Q_A = ∑_v d_v ‖x_v‖²`
  have hinv : Function.Involutive c := hc
  have h5 : ∑ A, (Q A + Q (c A)) / 2 = ∑ A, Q A := by
    have hswap : ∑ A, Q (c A) = ∑ A, Q A := Equiv.sum_comp (hinv.toPerm c) Q
    rw [← sum_div, sum_add_distrib, hswap]
    ring
  have h6 : ∑ A, Q A = ∑ v, d v * ‖x v‖ ^ 2 := sum_fiberwise univ σ _
  calc |∑ v, ∑ w, ⟪x w, T w v (x v)⟫| ≤ _ := h1
    _ = ∑ A, a A * a (c A) := by rw [h2, h3]
    _ ≤ ∑ A, (Q A + Q (c A)) / 2 := sum_le_sum fun A _ => h4 A
    _ = ∑ v, d v * ‖x v‖ ^ 2 := by rw [h5, h6]

/-- **`rem:envelope-gain`, one star with one arm.** For the star `[[0, α], [α, 0]]` (centre and one
arm of norm `α`) and the diagonal weights `d_c, d_a > 0`, the order `±L ⪯ diag(d_c, d_a)` holds
for all vectors iff `d_c d_a ≥ α²` (the one-factor case of `eq:oct24:mask-schur`). -/
theorem one_star_gain {α dc da : ℝ} (hc : 0 < dc) (ha : 0 < da) :
    (∀ x y : ℝ, |2 * α * x * y| ≤ dc * x ^ 2 + da * y ^ 2) ↔ α ^ 2 ≤ dc * da := by
  constructor
  · intro h
    -- test at `x = √da`, `y = √dc`
    have h1 := h (Real.sqrt da) (Real.sqrt dc)
    rw [Real.sq_sqrt ha.le, Real.sq_sqrt hc.le] at h1
    have hs : Real.sqrt da * Real.sqrt dc = Real.sqrt (dc * da) := by
      rw [← Real.sqrt_mul ha.le, mul_comm]
    have e : 2 * α * Real.sqrt da * Real.sqrt dc = 2 * α * Real.sqrt (dc * da) := by
      rw [mul_assoc, hs]
    rw [e] at h1
    have hpos : 0 < Real.sqrt (dc * da) := Real.sqrt_pos.2 (mul_pos hc ha)
    have h2 : |α| * Real.sqrt (dc * da) ≤ Real.sqrt (dc * da) ^ 2 := by
      rw [Real.sq_sqrt (mul_pos hc ha).le]
      have : |2 * α * Real.sqrt (dc * da)| = 2 * (|α| * Real.sqrt (dc * da)) := by
        rw [abs_mul, abs_mul, abs_of_pos hpos, abs_two]; ring
      rw [this] at h1
      linarith
    have h3 : |α| ≤ Real.sqrt (dc * da) := by
      have := h2
      rw [sq] at this
      exact le_of_mul_le_mul_right this hpos
    have h4 : |α| ^ 2 ≤ Real.sqrt (dc * da) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs, Real.sq_sqrt (mul_pos hc ha).le] at h4
    exact h4
  · intro h x y
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (dc * x + α * y), sq_nonneg (α * x + da * y), mul_pos hc ha,
        sq_nonneg x, sq_nonneg y]
    · nlinarith [sq_nonneg (dc * x - α * y), sq_nonneg (α * x - da * y), mul_pos hc ha,
        sq_nonneg x, sq_nonneg y]

/-! ### A toy instance of the hypotheses of `mask_schur` -/

/-- Non-vacuity of `mask_schur`: one star with one arm on `E = ℝ` (features `0` = centre and `1` =
arm, masks `false`/`true` exchanged by `not`), arm operator the identity, weights `d = (1, 1)`.
All hypotheses hold, and the conclusion is `|2 x₀ x₁| ≤ x₀² + x₁²`. -/
example (x : Fin 2 → ℝ) :
    |∑ v, ∑ w, ⟪x w, (if v ≠ w then (LinearMap.id : ℝ →ₗ[ℝ] ℝ) else 0) (x v)⟫| ≤
      ∑ v, (1 : ℝ) * ‖x v‖ ^ 2 := by
  refine mask_schur (fun v : Fin 2 => decide (v = 1)) (fun b => !b) (fun b => by simp)
    (fun v w => if v ≠ w then LinearMap.id else 0) (fun _ => 1) (fun _ => 1) (fun _ => by norm_num)
    (fun _ => by norm_num) ?_ ?_ ?_ x
  · intro v w h
    fin_cases v <;> fin_cases w <;> simp_all
  · intro v w y
    by_cases h : w = v <;> simp [h]
  · intro A
    have h1 : (Finset.univ.filter (fun x : Fin 2 => ¬x = 1)).card = 1 := by decide
    have h2 : (Finset.univ.filter (fun x : Fin 2 => x = 1)).card = 1 := by decide
    cases A <;> simp <;> rw [h1, h2] <;> norm_num

end Sarkozy.Envelopes
