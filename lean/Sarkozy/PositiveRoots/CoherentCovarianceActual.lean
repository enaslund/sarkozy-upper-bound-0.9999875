module

public import Sarkozy.PositiveRoots.CoherentDiagonalBound
public import Sarkozy.PositiveRoots.CoherentCovarianceNumerics

/-! Full coherent covariance, including constants, on the actual induced chamber half. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.Labellings
open Sarkozy.PartV Sarkozy.PartV.CoherentDictionary

variable {p : ℕ} [Fact p.Prime]

theorem chamberTwoSided_actual_bound (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw (by rw [ZMod.card]; omega)) (halfLaw (by rw [ZMod.card]; omega))
      (fun x y => Ksoft x y * chamberTwoSided x y) f f| ≤
      (coherentTwoSidedPrice p (256 * rectangleMassUpper p) (rectangleMassUpper p ^ 2) *
        privateCompression p) * nrm (halfLaw (by rw [ZMod.card]; omega)) f ^ 2 := by
  have hp6 : 6 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  obtain ⟨hrow, hcol⟩ := rectangle_square_rows hW hp3
  have hR : 0 ≤ 256 * rectangleMassUpper p :=
    mul_nonneg (by norm_num) rectangleMassUpper_nonneg
  have h := condLaw_abs (coreLaw.product pairLaw) Avoid (hP_pos hp6)
    (fun x y => Ksoft x y * chamberTwoSided x y)
    (chamberTwoSided_rectangle_bound hp3 hp7 hR hrow hcol (Ksoft_rectangle_bound hW hp3)) f
  change _ ≤ coherentTwoSidedPrice p (256 * rectangleMassUpper p) (rectangleMassUpper p ^ 2) /
    prob (coreLaw.product pairLaw) Avoid * nrm (halfLaw hp6) f ^ 2 at h
  refine h.trans ?_
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (hP_inv_le_privateCompression (by omega))
    (coherentTwoSidedPrice_nonneg hp7 hR (sq_nonneg _))) (sq_nonneg _)

omit [Fact p.Prime] in
theorem covariance_prices_combine (a M : ℝ) (hM : 0 ≤ M) :
    256 * a * coherentOffdiagPrice p + coherentTwoSidedPrice p (256 * a) M +
      ((1936 / 75 : ℝ) + 8 / 45) * (p : ℝ)⁻¹ * M ≤ coherentCovariancePrice p a M := by
  calc
    _ ≤ 256 * a * coherentOffdiagPrice p + coherentTwoSidedPrice p (256 * a) M +
      ((1936 / 75 : ℝ) + 8 / 45) * (p : ℝ)⁻¹ * M + (12476 / 225 : ℝ) * (p : ℝ)⁻¹ * M := by
      exact le_add_of_nonneg_right (by positivity)
    _ = _ := by
      unfold coherentOffdiagPrice coherentTwoSidedPrice coherentCovariancePrice
      ring

theorem coherent_covariance_actual (hW : WeilBound (ZMod p)) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw (by rw [ZMod.card]; omega)) (halfLaw (by rw [ZMod.card]; omega))
      (fun x y => Ksoft x y *
        (coherentScore p dictionary39
          (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) ^ 2 - 13 / 75)) f f| ≤
      (coherentCovariancePrice p (rectangleMassUpper p) (rectangleMassUpper p ^ 2) *
        privateCompression p) * nrm (halfLaw (by rw [ZMod.card]; omega)) f ^ 2 := by
  have hp6 : 6 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have he : (fun x y : CoreT (ZMod p) × PairT (ZMod p) => Ksoft x y *
      (coherentScore p dictionary39
        (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) ^ 2 - 13 / 75)) =
      fun x y => Ksoft x y * coherentOffdiagKernel x y + Ksoft x y * chamberTwoSided x y +
        Ksoft x y * chamberDiagonalRemainder x y := by
    funext x y
    rw [coherent_square_physical]
    unfold chamberDiagonalRemainder chamberAuxiliary
    ring
  have hsplit := kernelForm_add3 (halfLaw hp6)
    (fun x y => Ksoft x y * coherentOffdiagKernel x y)
    (fun x y => Ksoft x y * chamberTwoSided x y)
    (fun x y => Ksoft x y * chamberDiagonalRemainder x y) 1 1 1 f f
  simp only [one_mul] at hsplit
  rw [he, hsplit]
  have ho := coherent_offdiag_actual hW hDLK hp3 hp7 f
  have ht := chamberTwoSided_actual_bound hW hp3 hp7 f
  have hd := chamber_diagonal_remainder_bound hp3 (by omega : 6 ≤ p)
    (Ksoft_actual_bound hW hp3 (by omega)) f
  have hcomp : 0 ≤ privateCompression p := by
    have hp : (7 : ℝ) < p := by exact_mod_cast hp7
    unfold privateCompression
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
  calc
    _ ≤ |kernelForm (halfLaw hp6) (halfLaw hp6)
        (fun x y => Ksoft x y * coherentOffdiagKernel x y) f f| +
        |kernelForm (halfLaw hp6) (halfLaw hp6)
        (fun x y => Ksoft x y * chamberTwoSided x y) f f| +
        |kernelForm (halfLaw hp6) (halfLaw hp6)
        (fun x y => Ksoft x y * chamberDiagonalRemainder x y) f f| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (256 * rectangleMassUpper p * coherentOffdiagPrice p * privateCompression p) *
          nrm (halfLaw hp6) f ^ 2 +
        (coherentTwoSidedPrice p (256 * rectangleMassUpper p) (rectangleMassUpper p ^ 2) *
          privateCompression p) * nrm (halfLaw hp6) f ^ 2 +
        (((1936 / 75 : ℝ) + 8 / 45) * (p : ℝ)⁻¹) *
          (rectangleMassUpper p ^ 2 * privateCompression p) * nrm (halfLaw hp6) f ^ 2 :=
      add_le_add (add_le_add ho ht) hd
    _ = (256 * rectangleMassUpper p * coherentOffdiagPrice p +
        coherentTwoSidedPrice p (256 * rectangleMassUpper p) (rectangleMassUpper p ^ 2) +
        ((1936 / 75 : ℝ) + 8 / 45) * (p : ℝ)⁻¹ * rectangleMassUpper p ^ 2) *
          privateCompression p * nrm (halfLaw hp6) f ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (covariance_prices_combine _ _ (sq_nonneg _)) hcomp) (sq_nonneg _)

theorem coherent_covariance_actual_26400 (hW : WeilBound (ZMod p)) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw (by rw [ZMod.card]; omega)) (halfLaw (by rw [ZMod.card]; omega))
      (fun x y => Ksoft x y *
        (coherentScore p dictionary39
          (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) ^ 2 - 13 / 75)) f f| ≤
      (26400 * (p : ℝ)⁻¹ * privateCompression p) *
        nrm (halfLaw (by rw [ZMod.card]; omega)) f ^ 2 := by
  have hcomp : 0 ≤ privateCompression p := by
    have hp : (7 : ℝ) < p := by exact_mod_cast (by omega : 7 < p)
    unfold privateCompression
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
  exact (coherent_covariance_actual hW hDLK hp3 (by omega) f).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (coherent_covariance_price_lt hp40).le hcomp) (sq_nonneg _))

end Sarkozy.PositiveRoots.CoherentFrame
