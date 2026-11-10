module

public import Sarkozy.PositiveRoots.CoherentDiagonalCost
public import Sarkozy.PositiveRoots.CoherentDiagonalCross
public import Sarkozy.PositiveRoots.CoherentDiagonalRemainder

/-! The collected two-sided diagonal covariance on the actual accepting rectangle. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.Labellings
open Sarkozy.PartV.CoherentDictionary

variable {p : ℕ} [Fact p.Prime]

theorem diagonal_weighted_bound (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {R M : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ c : CoreT (ZMod p), pairLaw.expect (fun b => Rk c b ^ 2) ≤ R)
    (hcol : ∀ b : PairT (ZMod p), coreLaw.expect (fun c => Rk c b ^ 2) ≤ R)
    (hM : ∀ f : CoreT (ZMod p) × PairT (ZMod p) → ℝ,
      |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw) Ksoft f f| ≤
        M * nrm (coreLaw.product pairLaw) f ^ 2)
    (sc : Support × ℚ) (hsc : sc ∈ collectedTwoSided)
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |(sc.2 : ℝ) * kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => Ksoft x y * chamberTrace sc.1 x y) f f| ≤
      diagonalWeightedPrice p R M sc * nrm (coreLaw.product pairLaw) f ^ 2 := by
  rw [abs_mul]
  by_cases hp : PrivateDiagonal sc.1
  · have h := mul_le_mul_of_nonneg_left
      (private_diagonal_rectangle hp3 Rk hR hcol sc.1 hp.1 hp.2 f f) (abs_nonneg (sc.2 : ℝ))
    simp only [diagonalWeightedPrice, diagonalCoreCost, diagonalPrivateCost, diagonalCrossCost,
      hp, not_true_eq_false, false_and, ite_false, ite_true, Rat.cast_zero, Rat.cast_abs,
      zero_mul, zero_add, add_zero]
    convert h using 1
    · rfl
    · ring
  by_cases hc : CoreDiagonal sc.1
  · have h := mul_le_mul_of_nonneg_left
      (core_diagonal_rectangle hp3 hp7 Rk hR hrow sc.1 hc.1 hc.2 f f) (abs_nonneg (sc.2 : ℝ))
    simp only [diagonalWeightedPrice, diagonalCoreCost, diagonalPrivateCost, diagonalCrossCost,
      hp, hc, not_false_eq_true, not_true_eq_false, true_and, ite_true, ite_false,
      Rat.cast_zero, Rat.cast_mul, Rat.cast_abs, diagonalCoreFactor_real, zero_mul, add_zero]
    convert h using 1
    · rfl
    · ring
  · obtain ⟨i, j, hcase⟩ := diagonal_cross_geometry sc hsc hp hc
    have he : (fun x y : CoreT (ZMod p) × PairT (ZMod p) => Ksoft x y * chamberTrace sc.1 x y) =
        fun x y => -(p : ℝ)⁻¹ * Ksoft x y := by
      funext x y
      rcases hcase with ⟨hL, hR⟩ | ⟨hL, hR⟩
      · exact chamberTrace_core_private hp3 sc.1 i j hL hR x y
      · exact chamberTrace_private_core hp3 sc.1 i j hL hR x y
    rw [he, kernelForm_smul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (p : ℝ)⁻¹)]
    have h := mul_le_mul_of_nonneg_left (hM f)
      (mul_nonneg (abs_nonneg (sc.2 : ℝ)) (by positivity : 0 ≤ (p : ℝ)⁻¹))
    simp only [diagonalWeightedPrice, diagonalCoreCost, diagonalPrivateCost, diagonalCrossCost,
      hp, hc, not_false_eq_true, and_self, and_false, ite_false, ite_true,
      Rat.cast_zero, Rat.cast_abs, zero_mul, zero_add, mul_zero]
    convert h using 1 <;> ring

theorem chamberTwoSided_form
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => Ksoft x y * chamberTwoSided x y) f f =
      (collectedTwoSided.map fun sc => (sc.2 : ℝ) *
        kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
          (fun x y => Ksoft x y * chamberTrace sc.1 x y) f f).sum := by
  have he : (fun x y : CoreT (ZMod p) × PairT (ZMod p) => Ksoft x y * chamberTwoSided x y) =
      fun x y => (collectedTwoSided.map fun sc =>
        (sc.2 : ℝ) * (Ksoft x y * chamberTrace sc.1 x y)).sum := by
    funext x y
    unfold chamberTwoSided
    rw [twoSided_collect_eval]
    unfold dictionaryEval
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro sc _
    ring
  rw [he, kernelForm_list]
  simp_rw [kernelForm_smul]

theorem chamberTwoSided_rectangle_bound (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {R M : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ c : CoreT (ZMod p), pairLaw.expect (fun b => Rk c b ^ 2) ≤ R)
    (hcol : ∀ b : PairT (ZMod p), coreLaw.expect (fun c => Rk c b ^ 2) ≤ R)
    (hM : ∀ f : CoreT (ZMod p) × PairT (ZMod p) → ℝ,
      |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw) Ksoft f f| ≤
        M * nrm (coreLaw.product pairLaw) f ^ 2)
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => Ksoft x y * chamberTwoSided x y) f f| ≤
      coherentTwoSidedPrice p R M * nrm (coreLaw.product pairLaw) f ^ 2 := by
  rw [chamberTwoSided_form]
  calc
    _ ≤ (collectedTwoSided.map fun sc => |(sc.2 : ℝ) *
        kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
          (fun x y => Ksoft x y * chamberTrace sc.1 x y) f f|).sum := abs_map_sum _ _
    _ ≤ (collectedTwoSided.map fun sc =>
        diagonalWeightedPrice p R M sc * nrm (coreLaw.product pairLaw) f ^ 2).sum :=
      List.sum_le_sum fun sc hsc => diagonal_weighted_bound hp3 hp7 hR hrow hcol hM sc hsc f
    _ = _ := by rw [List.sum_map_mul_right, diagonal_price_sum]

end Sarkozy.PositiveRoots.CoherentFrame
