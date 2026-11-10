module

public import Sarkozy.TailCorrCore.ProvedCuts
public import Sarkozy.TailCorrCore.ProvedRows
public import Sarkozy.DLK.Basic

/-!
# The tail inputs are proved

All eleven graph-cut bounds and all ten conditional-row estimates are supplied.
Only the named Weil, moving-root, and four-cycle literature hypotheses remain.
This supplies the main theorem's former `hC : TailInputsCorr P4` obligation.
-/

@[expose] public section

namespace Sarkozy.TailCorrCore

open Sarkozy.PartV Sarkozy.PartVLaws

theorem tailInputsCorr (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) : TailInputsCorr P4 :=
  tailInputsCorr_of_rowBounds hW hMR
    (fun q _ hq => DLK.fourCycleBound hFour (by change 2 ^ 512 ≤ q at hq; omega))
    (fun q _ hq hne hw hp => tailRowBounds hq hw
      (DLK.fourCycleBound hFour (by change 2 ^ 512 ≤ q at hq; omega)) hne hp)

theorem tailInputsValid (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) : TailInputsValid P4 :=
  tailInputsValid_of_corr le_rfl (tailInputsCorr hW hMR hFour)

end Sarkozy.TailCorrCore
