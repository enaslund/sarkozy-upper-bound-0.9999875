module

public import Sarkozy.EnvelopeInputsBlock.Inputs
public import Sarkozy.TheoremCBlock.Anchor

@[expose] public section


/-!
# Theorem C at `a₀` with the envelope hypotheses per term, for any comparison data

P1's `TheoremCParam.ComparisonData.theoremC_reduced_anchor` and
`theoremC_classes_reduced_anchor` take the four envelope hypotheses (`EnvelopeBound` or
`EnvelopeBoundNonneg`, `SharpFirstTerms`, `FixedIntervalEnvelopeEnergies`, `EnvelopeEnergies`)
for comparison data `D` at `a₀`. Here they take the per-term inputs of I1's reductions instead
(the bundles of `Inputs.lean`), together with I1's `IndexMomentBound D`. For the paper's data
`IndexMomentBound` is proved (`paper_indexMomentBound`) and the classes form is
`main_anchor_paper_inputs`; these two theorems serve any other data at `a₀`, for example
comparison data on the block atoms after their port.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeInputsBlock

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.FourierArithmetic

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **Theorem C at the formal exponent with the envelope hypotheses per term** (`thm:comparison`
in the closing form of `thm:density:induction`, at `a₀`; reduced form): P1's
`theoremC_reduced_anchor` with (E1), the sharp first-stage terms and the two envelope energies
given by their per-term inputs (`lem:bracket-energy`, `lem:sharp-first`, `lem:density:coupled`,
`lem:envelope-energy`, `lem:hyb:moment`). The other hypotheses are P1's. -/
theorem theoremC_reduced_anchor_inputs
    (D : TheoremCBlock.ComparisonData Params.anchorDecay m₀ blk p pr h E)
    (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q)) {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔)
    (hΘ : D.Theta 𝓔 < 1) (E1 : EnvelopeBoundInputs D) (SF : SharpFirstInputs D)
    (hDC : TheoremCBlock.DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
        (hRI : IndexMomentBound D)
    (fix : FixedIntervalInputs hcop D) (env : EnvelopeEnergyInputs hcop D)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound Param.anchorSaving :=
  D.theoremC_reduced_anchor hcop h𝓔 hΘ
    (E1.envelopeBound TheoremCParam.ComparisonData.anchorDecay_nonneg)
    (SF.sharpFirstTerms TheoremCParam.ComparisonData.anchorDecay_nonneg) hDC
    (fix.fixedIntervalEnvelopeEnergies hcop TheoremCParam.ComparisonData.anchorDecay_nonneg hRI)
    (env.envelopeEnergies hcop TheoremCParam.ComparisonData.anchorDecay_nonneg hRI) hunit

/-- **Theorem C with the (CP5) class bounds at the formal exponent, with the envelope hypotheses
per term** (`thm:comparison`, `def:cp5`, `def:robust`; reduced form): P1's
`theoremC_classes_reduced_anchor` with (E1) in its `EnvelopeBoundNonneg` form, the sharp
first-stage terms and the two envelope energies given by their per-term inputs. -/
theorem theoremC_classes_reduced_anchor_inputs
    (D : TheoremCBlock.ComparisonData Params.anchorDecay m₀ blk p pr h E)
    (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
    (CB : TheoremCBlock.ClassBounds Params.anchorDecay m₀ blk p D.CL) {𝓔 : ℝ}
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hΘ : D.Theta 𝓔 < 1) (E1 : EnvelopeBoundInputs D) (hCB : CB.RobustNonneg)
    (SF : SharpFirstInputs D)
        (hDC : TheoremCBlock.DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hRI : IndexMomentBound D) (fix : FixedIntervalInputs hcop D)
    (env : EnvelopeEnergyInputs hcop D)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound Param.anchorSaving :=
  D.theoremC_classes_reduced_anchor hcop CB hΨ hΘ
    (E1.envelopeBoundNonneg TheoremCParam.ComparisonData.anchorDecay_nonneg) hCB
    (SF.sharpFirstTerms TheoremCParam.ComparisonData.anchorDecay_nonneg) hDC
    (fix.fixedIntervalEnvelopeEnergies hcop TheoremCParam.ComparisonData.anchorDecay_nonneg hRI)
    (env.envelopeEnergies hcop TheoremCParam.ComparisonData.anchorDecay_nonneg hRI) hunit

end Sarkozy.EnvelopeInputsBlock
