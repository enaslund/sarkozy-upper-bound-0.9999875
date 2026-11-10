module

public import Sarkozy.UpperComparison.OldRecords
public import Sarkozy.UpperComparison.Symmetry
public import Sarkozy.EnvelopeInputs.FoldedLaws

@[expose] public section

/-!
# The envelopes of the brackets of the upper records

`paper/sections/26_upper_comparison.tex`, proof of `prop:record:upper`(i): "Let `D^old` be the
reserved-diagonal copy of `μ^old_𝔅` … here `D^old` has uniform one-slot marginals, by invariance",
and the deleted records' envelopes `D_h`. These are the fields `D_prob`, `D_diag`, `D_unif` of
`(CP4)(b)` (`TheoremCParam.ComparisonLaw`): every envelope is a reserved-diagonal probability law
with uniform one-slot marginals.

The envelope of the brackets of `Symmetry`, `Emission` and `OldRecords` is `Diag(m_+)`,
`m_+ = plusMarginal ι Π` the half marginal of the record `Π`. Proved:
* `halfMarginalPlus_signedIntegral`: the two plus-half marginals of the tree agree;
* `join_self_flip`, `diagonalLaw_isDiagonalAt`: a diagonal law is reserved-diagonal;
* **`envelope_of_law`**: for a law with uniform one-slot marginals, `Diag(m_+)` is a probability
  law, reserved-diagonal, with uniform one-slot marginals;
* **`upper_envelope`**: the same for every record of an upper block (V1's block field laws).
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.Comparison Sarkozy.TheoremC

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The plus-half marginal of `Sarkozy.Comparison` (`halfMarginalPlus`) and that of
`Sarkozy.RecordExpansion` (`plusMarginal`) agree on a law. -/
theorem halfMarginalPlus_signedIntegral (c : ReflectionCut Slot) (w : (Slot → X) → ℝ) :
    halfMarginalPlus c (signedIntegral w) = plusMarginal c w := by
  funext x
  unfold halfMarginalPlus plusMarginal
  change (∑ z, w z * (if (fun v : c.Half => z v.1) = x then (1 : ℝ) else 0)) = _
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

omit [Fintype X] [DecidableEq X] in
/-- A doubled half configuration is fixed by the reflection. -/
theorem join_self_flip (c : ReflectionCut Slot) (x : c.Half → X) (v : Slot) :
    c.join x x (c.flip v) = c.join x x v := by
  unfold ReflectionCut.join
  by_cases hv : v ∈ c.half
  · have hfv : c.flip v ∉ c.half := c.flip_not_mem hv
    simp only [hv, hfv, ↓reduceDIte]
    exact congrArg x (Subtype.ext (c.flip_flip v))
  · have hfv : c.flip v ∈ c.half := (c.crosses v).mpr hv
    simp only [hv, hfv, ↓reduceDIte]

/-- **A diagonal law is diagonal at its cut.** -/
theorem diagonalLaw_isDiagonalAt (c : ReflectionCut Slot) (m : (c.Half → X) → ℝ) :
    TheoremC.IsDiagonalAt c (c.diagonalLaw m) := by
  intro z hz v
  unfold lawDensity at hz
  rw [EnvelopeInputs.diagonalLaw_apply] at hz
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  by_cases hxz : c.join x x = z
  · rw [← hxz]
    exact join_self_flip c x v
  · simp [hxz] at hx

/-- **The envelope of a law with uniform one-slot marginals**: `Diag(m_+)` is a probability law,
diagonal at the cut, with uniform one-slot marginals. -/
theorem envelope_of_law [Nonempty X] (c : ReflectionCut Slot) (μ : FiniteLaw (Slot → X))
    (hμ : HasUniformMarginals μ) :
    IsProbability (c.diagonalLaw (plusMarginal c μ.weight)) ∧
      TheoremC.IsDiagonalAt c (c.diagonalLaw (plusMarginal c μ.weight)) ∧
      HasUniformSlotMarginals (c.diagonalLaw (plusMarginal c μ.weight)) := by
  have hK : IsPositiveRecord (signedIntegral μ.weight) := by
    refine ⟨PartVRecords.isNonneg_law μ, ?_⟩
    have h := PartVRecords.hasUniformSlotMarginals_smul_law μ hμ 1
    rwa [one_smul] at h
  obtain ⟨hpos, hmass⟩ := EnvelopeInputs.isPositiveRecord_foldPlus c hK
  rw [halfMarginalPlus_signedIntegral] at hpos hmass
  refine ⟨⟨hpos.1, ?_⟩, diagonalLaw_isDiagonalAt c _, hpos.2⟩
  rw [hmass]
  exact PartVRecords.mass_law μ

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The envelopes of the upper records** (fields `D_prob`, `D_diag`, `D_unif` of `(CP4)(b)`): for
every record `Π_ρ` of an upper block, `Diag(m_+)` at `ι` is a reserved-diagonal probability law
with uniform one-slot marginals. -/
theorem upper_envelope (hne : UpperNonempty pr) (ρ : UpIdx) :
    IsProbability (reservedCut.diagonalLaw
        (plusMarginal reservedCut (upComponent (upperBlockFieldLaws pr hne) ρ).weight)) ∧
      TheoremC.IsDiagonalAt reservedCut (reservedCut.diagonalLaw
        (plusMarginal reservedCut (upComponent (upperBlockFieldLaws pr hne) ρ).weight)) ∧
      HasUniformSlotMarginals (reservedCut.diagonalLaw
        (plusMarginal reservedCut (upComponent (upperBlockFieldLaws pr hne) ρ).weight)) := by
  have hu : HasUniformMarginals (upComponent (upperBlockFieldLaws pr hne) ρ) := by
    rcases ρ with ⟨b, t, φ⟩
    cases b
    · exact emit_uniform _ _ (blockGraphLaw_vertex_uniform pr _ (hne.one _ _))
    · exact emit_uniform _ _ (blockGraphLaw_vertex_uniform pr _ (hne.two _ _))
  exact envelope_of_law reservedCut _ hu

end Sarkozy.UpperComparison
