module

public import Sarkozy.MiddleComparison.Paper
public import Sarkozy.MiddleComparison.Fixed

@[expose] public section

/-!
# B2's `ComparisonInputs` with ten of the twelve replacements constructed

`subsec:middle-comparison`. The inputs by specification of `Sarkozy.MiddleComparison.Paper`, with
the two matching replacements of every middle block fixed to `⊗_p K₁` (`matchRec`,
`lem:record:e-law`(a)), the six merge replacements to V3's repairs (`mergeRec`,
`lem:merge-repair`) and the two constant replacements to the strict Paley edge (`constRec`,
`lem:record:accepting-c2`):

* `SpecData hW In S`: `UpperAtomInputs` on an upper block, `ReplacementData` on V3's frame of a
  middle block (any root); `SpecData.toSpecInputs` (through `ReplacementData.toReplacements`);
* **`comparisonInputsOfData`**: B2's `ComparisonInputs` from `SpecData` at every block and B2's
  clique and tail inputs.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **The (CP4) inputs of a class-three block with the merge repairs constructed**: B2's
`UpperAtomInputs` on an upper block; `ReplacementData` (the two folds and the twelve norms) on V3's
frame of a middle block. -/
def SpecData (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B} :
    PaperBlockSpec blockOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes blockOf b) (upperNe hW U) U.W U.r)
  | .middleUniform M => ULift (ReplacementData (blockPrimes blockOf b) (classThree_blockPrimes b)
      (frameU In M))
  | .middleIndividual M => ULift (ReplacementData (blockPrimes blockOf b)
      (classThree_blockPrimes b) (frameI In M))
  | .middleCoherent M => ULift (ReplacementData (blockPrimes blockOf b) (classThree_blockPrimes b)
      (frameC In M))

/-- The inputs by specification of `Paper`, with `matchRec`, `mergeRec` and `constRec`. -/
noncomputable def SpecData.toSpecInputs (hW : Target.Weil) (In : FirstStageInputs blockOf)
    {b : B} : (S : PaperBlockSpec blockOf b) → SpecData hW In S → SpecInputs hW In S
  | .upper _, D => D
  | .middleUniform _, R => ReplacementData.toReplacements R.down
  | .middleIndividual _, R => ReplacementData.toReplacements R.down
  | .middleCoherent _, R => ReplacementData.toReplacements R.down

variable (blockOf) in
/-- **B2's `ComparisonInputs` with the middle atoms and ten of their twelve replacements
constructed.** -/
noncomputable def comparisonInputsOfData (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf)
    (clique : ∀ q : PrefixCoord, DeletionInputs ((v2Reference blockOf hW spec hC).μ₀ (.inl q))
      (paperPrefixAccepted blockOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : B, SpecData hW In (spec b))
    (tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
      TailAtomInputs q (tailNe hW h4)
        (signedIntegral ((v2Reference blockOf hW spec hC).μp q).weight))
    (St At : ℝ)
    (tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St)
    (tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At) :
    ComparisonInputs blockOf hW spec hC In :=
  comparisonInputsOf blockOf hW spec hC In clique
    (fun b => SpecData.toSpecInputs hW In (spec b) (blk b)) tail St At tail_S tail_A

end Sarkozy.MiddleComparison
