module

public import Sarkozy.Variance.WeightedIdentityExpansion

/-! Identify the graph expansion with the paper's concrete weighted soft-count moment. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

def rootOrder : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 4, 1, 3, 5]
  invFun := ![0, 3, 1, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

variable {p : ℕ} [Fact p.Prime]

theorem expandedMoment_rootOrder : expandedMoment (ZMod p) =
    (labelLaw (Fin 6) (ZMod p)).expect (fun x =>
      (WeightedMoment.pAdm p (x 0) (x 1) (x 2) (x 3) : ℝ) *
        softIntegrand (ZMod p) (x 0) (x 1) (x 2) (x 3) (x 4) *
        softIntegrand (ZMod p) (x 0) (x 1) (x 2) (x 3) (x 5)) := by
  unfold expandedMoment
  rw [← label_expect_permute rootOrder]
  apply FiniteLaw.expect_congr
  intro x
  norm_num [rootOrder, admPolynomial, WeightedMoment.pAdm, chi]

theorem expandedMoment_eq_eAdm : expandedMoment (ZMod p) = WeightedMoment.eAdm p := by
  rw [expandedMoment_rootOrder, label_expect_six]
  change (∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p,
    ∑ e : ZMod p, ∑ z : ZMod p, (WeightedMoment.pAdm p a b c d : ℝ) *
      softIntegrand (ZMod p) a b c d e * softIntegrand (ZMod p) a b c d z) /
        (p : ℝ) ^ 6 = _
  have hinner (a b c d : ZMod p) :
      (∑ e : ZMod p, ∑ z : ZMod p, (WeightedMoment.pAdm p a b c d : ℝ) *
        softIntegrand (ZMod p) a b c d e * softIntegrand (ZMod p) a b c d z) =
      (WeightedMoment.pAdm p a b c d : ℝ) * (RootMarginal.softW a b c d : ℝ) ^ 2 := by
    simp only [← mul_sum, ← sum_mul, softIntegrand_sum]
    ring
  simp_rw [hinner]
  unfold WeightedMoment.eAdm
  push_cast
  congr 1
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
