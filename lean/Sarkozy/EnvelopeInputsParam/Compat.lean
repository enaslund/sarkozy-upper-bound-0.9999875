module

public import Sarkozy.EnvelopeInputsParam.EnvelopeCoupled
public import Sarkozy.EnvelopeInputsParam.RevealExpansion
public import Sarkozy.TheoremCParam.Compat

@[expose] public section

/-!
# Compatibility: I1's reductions are the instances of the generated ones at the record exponent

The files of `Sarkozy.EnvelopeInputsParam` were generated from I1's `Sarkozy.EnvelopeInputs` by a
script. This file checks that the generation changed nothing but the exponent: I1's top
reductions, with exactly their statements (`type_of% @…`), are re-proved from the generated
ones applied to P1's `TheoremCParam.ComparisonData.ofRecord D` at `a = decay`, with
`ha := decay_pos.le`. The hypotheses are passed unchanged: their types agree with the generated
ones by unfolding (`selectionFactor`, `priceExponent`, the pieces and their prices). The
conclusions agree with I1's in the same way.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeInputsParam

section Pieces

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremC.ComparisonData m₀ p pr h E) (L : ℕ)

/-! The pieces are defined by pattern matching, so the two versions agree case by case (the
matchers are different constants, which `isDefEq` does not identify on a variable). -/

theorem cpieceCoef_ofRecord (σ j b x) :
    cpieceCoef (TheoremCParam.ComparisonData.ofRecord D) L σ j b x =
      EnvelopeInputs.cpieceCoef D L σ j b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

theorem cpieceK_ofRecord (b x) :
    cpieceK (TheoremCParam.ComparisonData.ofRecord D) L b x = EnvelopeInputs.cpieceK D L b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

theorem cpieceG_ofRecord (b x) :
    cpieceG (TheoremCParam.ComparisonData.ofRecord D) L b x = EnvelopeInputs.cpieceG D L b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

theorem cpieceM_ofRecord (b x) :
    cpieceM (TheoremCParam.ComparisonData.ofRecord D) L b x = EnvelopeInputs.cpieceM D L b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

theorem ecpieceCoef_ofRecord (ω σ j b x) :
    ecpieceCoef (TheoremCParam.ComparisonData.ofRecord D) L ω σ j b x =
      EnvelopeInputs.ecpieceCoef D L ω σ j b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

theorem ecpieceK_ofRecord (ω b x) :
    ecpieceK (TheoremCParam.ComparisonData.ofRecord D) L ω b x =
      EnvelopeInputs.ecpieceK D L ω b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

theorem ecpieceG_ofRecord (ω b x) :
    ecpieceG (TheoremCParam.ComparisonData.ofRecord D) L ω b x =
      EnvelopeInputs.ecpieceG D L ω b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

theorem ecpieceM_ofRecord (b x) :
    ecpieceM (TheoremCParam.ComparisonData.ofRecord D) L b x = EnvelopeInputs.ecpieceM D L b x := by
  rcases x with (_ | _) | ⟨_, _ | _⟩ <;> rfl

end Pieces

/-- **Compatibility** for `SharpFirstTerms`: I1's `sharpFirstTerms_of_coupledPieces_uniform` is
the generated one at the record exponent (`lem:sharp-first`, `lem:density:coupled`). -/
theorem sharpFirstTerms_of_coupledPieces_uniform_viaParam :
    type_of% @Sarkozy.EnvelopeInputs.sharpFirstTerms_of_coupledPieces_uniform := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ pr h _ E _ _ D ε hε0 hεt c₁ hc₁ hcoup
  have key := sharpFirstTerms_of_coupledPieces_uniform (TheoremCParam.ComparisonData.ofRecord D)
    Sarkozy.decay_pos.le ε hε0 hεt hc₁
  simp only [cpieceCoef_ofRecord, cpieceK_ofRecord, cpieceG_ofRecord, cpieceM_ofRecord] at key
  exact key hcoup

/-- **Compatibility** for `EnvelopeBound`: I1's `envelopeBound_of_coupledPieces_uniform` is the
generated one at the record exponent (`lem:bracket-energy`, `lem:density:coupled`). -/
theorem envelopeBound_of_coupledPieces_uniform_viaParam :
    type_of% @Sarkozy.EnvelopeInputs.envelopeBound_of_coupledPieces_uniform := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ pr h _ E _ _ D εE hε0 hεt c₁ hc₁ hsub hcoup
  have key := envelopeBound_of_coupledPieces_uniform (TheoremCParam.ComparisonData.ofRecord D)
    Sarkozy.decay_pos.le εE hε0 hεt hc₁ hsub
  simp only [ecpieceCoef_ofRecord, ecpieceK_ofRecord, ecpieceG_ofRecord, ecpieceM_ofRecord] at key
  exact key hcoup

/-- **Compatibility** for `EnvelopeEnergies`: I1's `envelopeEnergies_of_inputs` is the generated
one at the record exponent (`lem:envelope-energy`, `lem:hyb:moment`). -/
theorem envelopeEnergies_of_inputs_viaParam :
    type_of% @Sarkozy.EnvelopeInputs.envelopeEnergies_of_inputs := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ _ pr h _ E _ _ hcop D hRI z hz0 hzt c hc rL rR htermL htermR
    hremL hremR
  exact envelopeEnergies_of_inputs hcop (TheoremCParam.ComparisonData.ofRecord D)
    Sarkozy.decay_pos.le hRI z hz0 hzt hc rL rR htermL htermR hremL hremR

/-- **Compatibility** for `FixedIntervalEnvelopeEnergies`: I1's
`fixedIntervalEnvelopeEnergies_of_inputs` is the generated one at the record exponent
(`lem:envelope-energy`, `lem:hyb:moment`). -/
theorem fixedIntervalEnvelopeEnergies_of_inputs_viaParam :
    type_of% @Sarkozy.EnvelopeInputs.fixedIntervalEnvelopeEnergies_of_inputs := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ _ pr h _ E _ _ hcop D hRI z hz0 hzt c hc rL rR htermL htermR
    hremL hremR
  exact fixedIntervalEnvelopeEnergies_of_inputs hcop (TheoremCParam.ComparisonData.ofRecord D)
    Sarkozy.decay_pos.le hRI z hz0 hzt hc rL rR htermL htermR hremL hremR

end Sarkozy.EnvelopeInputsParam
