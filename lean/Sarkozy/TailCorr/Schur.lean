module

public import Sarkozy.TailCorr.Reduction

@[expose] public section

/-!
# A Schur test for `‖T - J‖ ≤ δ` on `L²(μ)`

`paper/sections/25_upper_reference.tex`, `subsec:row-anova-correlation` (the matching row's
correlation `ρ_E`, `‖T_E^b - J‖`); used for the matching rows of the field type `E`.

* **`normBound_of_rowSums`**: if every row and every column of `|T - 1|` has `μ`-mass at most
  `δ` on the support of `μ`, then `‖T - J‖ ≤ δ` on `L²(μ)` (`NormBound μ T δ`).
-/

namespace Sarkozy.TailCorr

open Finset Sarkozy.FiveType

variable {𝔛 : Type*} [Fintype 𝔛]

/-- `⟨Φ, TΨ⟩ - E Φ E Ψ = ∑∑ μ(x) μ(y) Φ(x) (T(x, y) - 1) Ψ(y)`. -/
theorem kf_sub_expect (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (Φ Ψ : 𝔛 → ℝ) :
    kf μ T Φ Ψ - μ.expect Φ * μ.expect Ψ =
      ∑ x, ∑ y, μ.weight x * μ.weight y * (Φ x * (T x y - 1) * Ψ y) := by
  unfold kf FiniteLaw.expect
  rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- One half of the Schur test: `∑∑ μ(x) μ(y) |T(x, y) - 1| Φ(x)² ≤ δ ‖Φ‖²` when every row of
`|T - 1|` has `μ`-mass at most `δ` on the support of `μ`. -/
theorem rowSum_bound (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) {δ : ℝ}
    (hrow : ∀ x, μ.weight x ≠ 0 → ∑ y, μ.weight y * |T x y - 1| ≤ δ) (Φ : 𝔛 → ℝ) :
    ∑ x, ∑ y, μ.weight x * μ.weight y * |T x y - 1| * Φ x ^ 2 ≤ δ * ip μ Φ Φ := by
  unfold ip FiniteLaw.expect
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have e : ∑ y, μ.weight x * μ.weight y * |T x y - 1| * Φ x ^ 2 =
      (μ.weight x * Φ x ^ 2) * ∑ y, μ.weight y * |T x y - 1| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e]
  by_cases hx : μ.weight x = 0
  · rw [hx]
    simp
  · have h0 : 0 ≤ μ.weight x * Φ x ^ 2 := mul_nonneg (μ.nonneg x) (sq_nonneg _)
    calc (μ.weight x * Φ x ^ 2) * ∑ y, μ.weight y * |T x y - 1| ≤ (μ.weight x * Φ x ^ 2) * δ :=
          mul_le_mul_of_nonneg_left (hrow x hx) h0
      _ = δ * (μ.weight x * (Φ x * Φ x)) := by ring

/-- **The Schur test for `‖T - J‖`**: if every row and every column of `|T - 1|` has `μ`-mass at
most `δ` on the support of `μ`, then `|⟨Φ, TΨ⟩ - E Φ E Ψ| ≤ δ ‖Φ‖ ‖Ψ‖`. -/
theorem normBound_of_rowSums (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrow : ∀ x, μ.weight x ≠ 0 → ∑ y, μ.weight y * |T x y - 1| ≤ δ)
    (hcol : ∀ y, μ.weight y ≠ 0 → ∑ x, μ.weight x * |T x y - 1| ≤ δ) :
    NormBound μ T δ := by
  intro Φ Ψ
  rw [kf_sub_expect]
  set w : 𝔛 × 𝔛 → ℝ := fun z => μ.weight z.1 * μ.weight z.2 * |T z.1 z.2 - 1| with hw
  have hw0 : ∀ z, 0 ≤ w z := fun z =>
    mul_nonneg (mul_nonneg (μ.nonneg _) (μ.nonneg _)) (abs_nonneg _)
  -- the absolute double sum
  have h1 : |∑ x, ∑ y, μ.weight x * μ.weight y * (Φ x * (T x y - 1) * Ψ y)| ≤
      ∑ z : 𝔛 × 𝔛, (Real.sqrt (w z) * |Φ z.1|) * (Real.sqrt (w z) * |Ψ z.2|) := by
    rw [← Fintype.sum_prod_type']
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_))
    have hs : Real.sqrt (w z) * Real.sqrt (w z) = w z := Real.mul_self_sqrt (hw0 z)
    have e : (Real.sqrt (w z) * |Φ z.1|) * (Real.sqrt (w z) * |Ψ z.2|) =
        (Real.sqrt (w z) * Real.sqrt (w z)) * (|Φ z.1| * |Ψ z.2|) := by ring
    rw [e, hs, hw]
    simp only
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (μ.nonneg _),
      abs_of_nonneg (μ.nonneg _)]
    ring
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun z : 𝔛 × 𝔛 => Real.sqrt (w z) * |Φ z.1|)
    (fun z => Real.sqrt (w z) * |Ψ z.2|)
  have hA : ∑ z : 𝔛 × 𝔛, (Real.sqrt (w z) * |Φ z.1|) ^ 2 ≤ δ * ip μ Φ Φ := by
    have e : ∀ z : 𝔛 × 𝔛, (Real.sqrt (w z) * |Φ z.1|) ^ 2 =
        μ.weight z.1 * μ.weight z.2 * |T z.1 z.2 - 1| * Φ z.1 ^ 2 := by
      intro z
      rw [mul_pow, Real.sq_sqrt (hw0 z), sq_abs]
    rw [Finset.sum_congr rfl fun z _ => e z, Fintype.sum_prod_type]
    exact rowSum_bound μ T hrow Φ
  have hB : ∑ z : 𝔛 × 𝔛, (Real.sqrt (w z) * |Ψ z.2|) ^ 2 ≤ δ * ip μ Ψ Ψ := by
    have e : ∀ z : 𝔛 × 𝔛, (Real.sqrt (w z) * |Ψ z.2|) ^ 2 =
        μ.weight z.1 * μ.weight z.2 * |T z.1 z.2 - 1| * Ψ z.2 ^ 2 := by
      intro z
      rw [mul_pow, Real.sq_sqrt (hw0 z), sq_abs]
    rw [Finset.sum_congr rfl fun z _ => e z, Fintype.sum_prod_type, Finset.sum_comm]
    have := rowSum_bound μ (fun y x => T x y) hcol Ψ
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl
      fun x _ => ?_)) this
    ring
  have hip : ∀ U : 𝔛 → ℝ, 0 ≤ ip μ U U := fun U =>
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (mul_self_nonneg _)
  calc |∑ x, ∑ y, μ.weight x * μ.weight y * (Φ x * (T x y - 1) * Ψ y)|
      ≤ Real.sqrt (∑ z : 𝔛 × 𝔛, (Real.sqrt (w z) * |Φ z.1|) ^ 2) *
          Real.sqrt (∑ z : 𝔛 × 𝔛, (Real.sqrt (w z) * |Ψ z.2|) ^ 2) := h1.trans h2
    _ ≤ Real.sqrt (δ * ip μ Φ Φ) * Real.sqrt (δ * ip μ Ψ Ψ) :=
        mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = δ * nrm μ Φ * nrm μ Ψ := by
        unfold nrm
        rw [Real.sqrt_mul hδ, Real.sqrt_mul hδ]
        have : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ
        calc Real.sqrt δ * Real.sqrt (ip μ Φ Φ) * (Real.sqrt δ * Real.sqrt (ip μ Ψ Ψ)) =
            (Real.sqrt δ * Real.sqrt δ) * Real.sqrt (ip μ Φ Φ) * Real.sqrt (ip μ Ψ Ψ) := by ring
          _ = δ * Real.sqrt (ip μ Φ Φ) * Real.sqrt (ip μ Ψ Ψ) := by rw [this]

end Sarkozy.TailCorr
