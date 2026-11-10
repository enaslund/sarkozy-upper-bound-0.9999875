module

public import Sarkozy.Variance.WeightedIdentityConcrete
public import Sarkozy.Variance.WeightedIdentityCertificate.Assembly

/-! The weighted 400-term identity is proved, with no certificate hypothesis. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedMoment

open Finset Sarkozy.Variance.WeightedIdentityCertificate

variable (p : ℕ) [Fact p.Prime]

/-- The complete symbolic weighted-moment identity for primes congruent to three modulo four. -/
theorem weightedIdentity_verified (hp3 : p % 4 = 3) : WeightedIdentity p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  unfold WeightedIdentity
  rw [← expandedMoment_eq_eAdm, expandedMoment_sum, weighted_sum (ZMod p) hF hm1,
    g5_eq, g10_eq, g12_eq]
  simp only [q, ZMod.card, one_div]

theorem weightedMoment_concrete_verified (hp3 : p % 4 = 3) {r : ℝ}
    (hr : r * Real.sqrt p = 1) :
    eAdm p ≤ 10 * (1 / (p : ℝ)) + 24 * (1 / (p : ℝ)) * r + 4 * (1 / (p : ℝ)) ^ 2 +
      14 * (1 / (p : ℝ)) ^ 3 ∧
    (Target.AhlgrenOno → eAdm p ≤ 5 * (1 / (p : ℝ)) + 34 * (1 / (p : ℝ)) * r +
      11 * (1 / (p : ℝ)) ^ 3) :=
  weightedMoment_concrete p (by omega) (weightedIdentity_verified p hp3) hr

theorem weightedMoment_hmom_verified (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hAO : Target.AhlgrenOno) {r : ℝ} (hr : r * Real.sqrt p = 1) :
    (∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p,
      if IsAdm p a b c d then ((RootMarginal.softW a b c d : ℝ) / p) ^ 2 else 0) /
        (nAdm p : ℝ) ≤
      (5 * (1 / (p : ℝ)) + 34 * (1 / (p : ℝ)) * r + 11 * (1 / (p : ℝ)) ^ 3) /
        RootMarginal.Z4 (1 / (p : ℝ)) :=
  weightedMoment_hmom p hp3 hp7 hAO (weightedIdentity_verified p hp3) hr

/-- The half-law variance conclusion with the finite certificate input discharged. -/
theorem rootMarginal_ii_second_lamF_verified (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hW : Labellings.WeilBound (ZMod p)) (hAO : Target.AhlgrenOno)
    (μ : FiniteLaw (HalfConf p)) (hunif : ∀ y, μ.weight y = 1 / Fintype.card (HalfConf p))
    {q r : ℝ} (hq : q = 1 / (p : ℝ)) (hr : r * Real.sqrt p = 1)
    (hlow : RootMarginal.LowerFactors q r) (n₁ n s : HalfConf p → ℝ)
    (hn₁ : ∀ y, n₁ y = 0 ∨ n₁ y = 1 ∨ n₁ y = 2)
    (hn : ∀ y, n y = ((RootMarginal.signedNbhd y.val.1 y.val.2.1 y.val.2.2.2.2.1
      y.val.2.2.2.2.2).card : ℝ) - n₁ y)
    (hs : ∀ y, (1 - 24 * RootMarginal.aP q r) *
        (n y * (n y - 1) / ((p : ℝ) / 16) ^ 2) ≤ s y ∧
      s y ≤ n y * (n y - 1) / ((p : ℝ) / 16) ^ 2) :
    chiSq (fun y => μ.weight y * s y / ∑ z, μ.weight z * s z) μ.weight ≤
      RootMarginal.Dfull q r ^ 2 / RootMarginal.Llow q r ^ 2 :=
  rootMarginal_ii_second_lamF p hp3 hp7 hW hAO (weightedIdentity_verified p hp3)
    μ hunif hq hr hlow n₁ n s hn₁ hn hs

end Sarkozy.Variance.WeightedMoment
