module

public import Sarkozy.GramBracketPaper.Main
public import Sarkozy.TailCorrCore.ProvedTail

/-!
# Supplying the proved tail to the main theorem

The `hC` field is constructed from the named literature inputs. The remaining
six block obligations and twelve final obligations are still explicit inputs.
-/

@[expose] public section

namespace Sarkozy.GramBracketPaper

open Sarkozy.TheoremC Sarkozy.TargetLedger Sarkozy.CancellationSteps Sarkozy.MainAnchor
  Sarkozy.MainTarget Sarkozy.FirstStagePaper Sarkozy.PartVLaws

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

noncomputable def A2BlockDataTarget.ofProvedTail
    (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (spec : ∀ b, PaperBlockSpec blockOf b) (In : FirstStageInputs blockOf)
    (Gi : GramInputs blockOf spec)
    (CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries
      (firstStageTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In))
    (ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (gramBracketTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In Gi) CL)
    (MC : TheoremCBlock.MeanCredit targetDecay paperM0 (paperAtomMap blockOf) paperTail ME)
    (SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME) :
    A2BlockDataTarget blockOf hW where
  spec := spec
  hC := TailCorrCore.tailInputsCorr hW hMR hFour
  In := In
  Gi := Gi
  CL := CL
  ME := ME
  MC := MC
  SM := SM

end Sarkozy.GramBracketPaper
