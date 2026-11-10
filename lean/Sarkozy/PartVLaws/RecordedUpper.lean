module

public import Sarkozy.PartVLaws.FinalBridge
public import Sarkozy.UpperRecords.BandCompletion

/-!
# Upper block specifications with the recorded weights

The exact 310-band certificates supply the data and `WeightsOK` field.
The remaining arguments place the block above its band's start and establish
the analytic validity of the recorded root, row, and layer bounds.
-/

@[expose] public section

namespace Sarkozy.PartVLaws

open Sarkozy.CancellationSteps Sarkozy.PartV Sarkozy.UpperRecords

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} {b : B}

noncomputable def UpperBlockInputs.ofBand (i : Fin 310)
    (hp : ∀ j, ((CompletionData.record i).start : ℝ) ≤ blockPrimes blockOf b j)
    {r : ℝ} (hr : 0 < r)
    (hV : ∀ hne hW' hp', ValidInputs (upperBlockFieldLaws (blockPrimes blockOf b) hne)
      (block_upperDatumHyp (blockPrimes blockOf b) hW' hp' hne) r
      (bandOrd i) (bandRes i) (bandCap i)) : UpperBlockInputs blockOf b where
  hp j := (band_start_min i).trans (hp j)
  W := bandWeights i
  r := r
  hr := hr
  ord := bandOrd i
  res := bandRes i
  k := bandCap i
  hWOK := bandWeightsOK i
  hV := hV

end Sarkozy.PartVLaws
