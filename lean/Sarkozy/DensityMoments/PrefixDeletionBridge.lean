module

public import Sarkozy.DensityMoments.PrefixEqualityEvents
public import Sarkozy.Comparison.FoldedEnergy

/-!
# `thm:density:iid-prefix`(c) in the vocabulary of the comparison and record packages

Bridges from `PrefixDeletion.lean` and `PrefixEqualityEvents.lean` to the existing notions:

* `diagLaw_eq_diagonalLaw`: our diagonal copy `diagLaw c h` is `ReflectionCut.diagonalLaw`
  (`Reflection/Transport.lean`) of the weights of `h`;
* `halfMarginal_weight_plus`, `halfMarginal_weight_minus`: the weights of `h_p` are both
  `Comparison.halfMarginalPlus` and `Comparison.halfMarginalMinus` of the replacement prefix at
  the reserved cut (the minus-half marginal of `μ_p` equals the plus-half one);
* `iidPrefix_bracket_diagonalLaw`: the bracket of (c) with `ReflectionCut.diagonalLaw`;
* `iidPrefix_symPart_sharp`, `iidPrefix_skewPart_sharp`: the symmetric and skew parts
  (`RecordExpansion.symPart`, `skewPart`) of `E_p` have sharp bound `η`
  (`Comparison.Sharp`, `eq:record:sharp`) relative to the half marginals of `μ_p`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open CliqueCopies ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

/-- Our diagonal copy is `ReflectionCut.diagonalLaw`. -/
theorem diagLaw_eq_diagonalLaw (c : ReflectionCut V) (h : FiniteLaw (c.Half → X)) :
    signedIntegral (diagLaw c h).weight = c.diagonalLaw h.weight := by
  apply LinearMap.ext
  intro Φ
  rw [← FiniteLaw.expect_eq_signedIntegral, diagLaw, FiniteLaw.expect_map]
  change ∑ x, h.weight x * Φ (fun v => x (halfIndex c v)) = ∑ x, h.weight x * Φ (c.join x x)
  refine sum_congr rfl fun x _ => ?_
  congr 2
  funext v
  unfold halfIndex ReflectionCut.join
  split_ifs <;> rfl

variable (p : ℕ) [hp : Fact p.Prime] (ℓ : ℕ)

/-- The two half restrictions of the replacement prefix have the same law. -/
theorem expect_cliqueIidLaw_flip (Ψ : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    (cliqueIidLaw p ℓ).expect (fun z => Ψ (fun v => z (reservedCut.flip v.1))) =
      (cliqueIidLaw p ℓ).expect (fun z => Ψ (fun v => z v.1)) := by
  rw [expect_cliqueIidLaw, expect_cliqueIidLaw]
  refine FiniteLaw.expect_congr _ fun q => ?_
  rw [expect_uniform_halfSplit reservedCut, expect_uniform_halfSplit reservedCut]
  have hm : ∀ xp xm : reservedCut.Half → Fin ℓ → Bool,
      (fun v : reservedCut.Half => prefixLabel p ℓ q
        ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) (reservedCut.flip v.1))) =
        fun v => prefixLabel p ℓ q (xm v) := by
    intro xp xm
    funext v
    rw [halfSplit_symm_out _ _ (reservedCut.flip_not_mem v.2)]
    exact congrArg (fun u => prefixLabel p ℓ q (xm u)) (Subtype.ext (reservedCut.flip_flip v.1))
  have hp' : ∀ xp xm : reservedCut.Half → Fin ℓ → Bool,
      (fun v : reservedCut.Half => prefixLabel p ℓ q
        ((halfSplit reservedCut (Fin ℓ → Bool)).symm (xp, xm) v.1)) =
        fun v => prefixLabel p ℓ q (xp v) := by
    intro xp xm
    funext v
    rw [halfSplit_symm_half _ _ v.2]
  simp only [hm, hp', FiniteLaw.expect_const]

/-- The weights of `h_p` are the plus-half marginal of `μ_p`. -/
theorem halfMarginal_weight_plus (x : reservedCut.Half → ZMod (p ^ (2 * ℓ))) :
    (halfMarginal p ℓ).weight x =
      Comparison.halfMarginalPlus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight) x := by
  unfold halfMarginal Comparison.halfMarginalPlus
  change (∑ z, if (fun v : reservedCut.Half => z v.1) = x then (cliqueIidLaw p ℓ).weight z
    else 0) = ∑ z, (cliqueIidLaw p ℓ).weight z *
      (if (fun v : reservedCut.Half => z v.1) = x then 1 else 0)
  refine sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

/-- The weights of `h_p` are also the minus-half marginal of `μ_p`. -/
theorem halfMarginal_weight_minus (y : reservedCut.Half → ZMod (p ^ (2 * ℓ))) :
    (halfMarginal p ℓ).weight y =
      Comparison.halfMarginalMinus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight) y := by
  rw [halfMarginal_weight_plus]
  unfold Comparison.halfMarginalPlus Comparison.halfMarginalMinus
  rw [← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral]
  exact (expect_cliqueIidLaw_flip p ℓ (fun w => if w = y then 1 else 0)).symm

/-- **The bracket of (c) with `ReflectionCut.diagonalLaw`** of the half marginal. -/
theorem iidPrefix_bracket_diagonalLaw :
    reservedCut.Bracket
      (signedIntegral (cliqueIidLaw p ℓ).weight + prefixEta ℓ • reservedCut.diagonalLaw
        (Comparison.halfMarginalPlus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight)))
      (signedIntegral (cliqueIidLaw p ℓ).weight - signedIntegral (deletedWeight p ℓ))
      (signedIntegral (cliqueIidLaw p ℓ).weight + prefixEta ℓ • reservedCut.diagonalLaw
        (Comparison.halfMarginalPlus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight))) := by
  have h := iidPrefix_bracket p ℓ
  have hw : (halfMarginal p ℓ).weight =
      Comparison.halfMarginalPlus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight) :=
    funext (halfMarginal_weight_plus p ℓ)
  rw [diagLaw_eq_diagonalLaw, hw] at h
  exact h

theorem halfL2_eq_plus (F : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    halfL2 (halfMarginal p ℓ) F = Real.sqrt (∑ x,
      Comparison.halfMarginalPlus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight) x *
        F x ^ 2) := by
  unfold halfL2 FiniteLaw.expect
  simp only [halfMarginal_weight_plus]

theorem halfL2_eq_minus (G : (reservedCut.Half → ZMod (p ^ (2 * ℓ))) → ℝ) :
    halfL2 (halfMarginal p ℓ) G = Real.sqrt (∑ y,
      Comparison.halfMarginalMinus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight) y *
        G y ^ 2) := by
  unfold halfL2 FiniteLaw.expect
  simp only [halfMarginal_weight_minus]

/-- **The symmetric part of `E_p` has sharp bound `η`** relative to the half marginals of `μ_p`
(`thm:density:iid-prefix`(c), `eq:record:sharp`). -/
theorem iidPrefix_symPart_sharp :
    Comparison.Sharp reservedCut
      (RecordExpansion.symPart reservedCut (signedIntegral (deletedWeight p ℓ)))
      (Comparison.halfMarginalPlus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight))
      (Comparison.halfMarginalMinus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight))
      (prefixEta ℓ) := by
  intro F G
  have h := (iidPrefix_sym_skew_le p ℓ F G).1
  rw [halfL2_eq_plus, halfL2_eq_minus, ← mul_assoc] at h
  have hform : reservedCut.form (RecordExpansion.symPart reservedCut
      (signedIntegral (deletedWeight p ℓ))) F G =
      (reservedCut.form (signedIntegral (deletedWeight p ℓ)) F G +
        reservedCut.form (signedIntegral (deletedWeight p ℓ)) G F) / 2 := by
    unfold RecordExpansion.symPart
    rw [Comparison.form_smul_law]
    change 1 / 2 * (reservedCut.form (signedIntegral (deletedWeight p ℓ)) F G +
      reservedCut.form (RecordExpansion.reflect reservedCut
        (signedIntegral (deletedWeight p ℓ))) F G) = _
    rw [RecordExpansion.form_reflect]
    ring
  rw [hform]
  exact h

/-- **The skew part of `E_p` has sharp bound `η`** relative to the half marginals of `μ_p`. -/
theorem iidPrefix_skewPart_sharp :
    Comparison.Sharp reservedCut
      (RecordExpansion.skewPart reservedCut (signedIntegral (deletedWeight p ℓ)))
      (Comparison.halfMarginalPlus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight))
      (Comparison.halfMarginalMinus reservedCut (signedIntegral (cliqueIidLaw p ℓ).weight))
      (prefixEta ℓ) := by
  intro F G
  have h := (iidPrefix_sym_skew_le p ℓ F G).2
  rw [halfL2_eq_plus, halfL2_eq_minus, ← mul_assoc] at h
  have hform : reservedCut.form (RecordExpansion.skewPart reservedCut
      (signedIntegral (deletedWeight p ℓ))) F G =
      (reservedCut.form (signedIntegral (deletedWeight p ℓ)) F G -
        reservedCut.form (signedIntegral (deletedWeight p ℓ)) G F) / 2 := by
    unfold RecordExpansion.skewPart
    rw [Comparison.form_smul_law]
    change 1 / 2 * (reservedCut.form (signedIntegral (deletedWeight p ℓ)) F G -
      reservedCut.form (RecordExpansion.reflect reservedCut
        (signedIntegral (deletedWeight p ℓ))) F G) = _
    rw [RecordExpansion.form_reflect]
    ring
  rw [hform]
  exact h

end Sarkozy.DensityMoments
