module

public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions00
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions01
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions02
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions03
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions04
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions05
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions06
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions07
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions08
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions09
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions10
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions11
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions12
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions13
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions14
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions15
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions16
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions17
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions18
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions19
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions20
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions21
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions23
public import Sarkozy.Variance.WeightedIdentityCertificate.TermReductions24

/-! Sum the 400 independently checked term identities. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem weighted_sum (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ a : Fin 5, ∑ b : Fin 5, ∑ h : Fin 16, termValue F a b h) =
      (4 + 8 * q F) * g5 F + g12 F + 24 * g10 F +
        5 * q F - 4 * q F ^ 2 + 14 * q F ^ 3 - 15 * q F ^ 4 := by
  simp only [Fin.sum_univ_five]
  rw [block0 F hF hm1, block1 F hF hm1, block2 F hF hm1, block3 F hF hm1, block4 F hF hm1, block5 F hF hm1, block6 F hF hm1, block7 F hF hm1, block8 F hF hm1, block9 F hF hm1, block10 F hF hm1, block11 F hF hm1, block12 F hF hm1, block13 F hF hm1, block14 F hF hm1, block15 F hF hm1, block16 F hF hm1, block17 F hF hm1, block18 F hF hm1, block19 F hF hm1, block20 F hF hm1, block21 F hF hm1, block22 F hF hm1, block23 F hF hm1, block24 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
