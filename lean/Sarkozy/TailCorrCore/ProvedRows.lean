module

public import Sarkozy.TailCorrCore.OperatorInputs
public import Sarkozy.PartVLaws.TailRowCorrelations

/-! All ten conditional row bounds required by the tail construction. -/

@[expose] public section

namespace Sarkozy.TailCorrCore

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.PartVLaws

theorem tailRowBounds {q : ℕ} [Fact q.Prime] (hq : 2 ^ 512 ≤ q)
    (hW : WeilBound (ZMod q)) (h4 : Extraction.FourCycleBound q)
    (hne : TailNonempty q) (hp : (2 : ℝ) ^ 20 ≤ q) : TailRowBounds q hne hW hp where
  fold20 f' := tail_fold_two hq hW h4 hne f' ((tail_upperDatumHyp q hW hp hne).two0 f')
  fold10 f' := tail_fold_one hq hW h4 hne f' ((tail_upperDatumHyp q hW hp hne).one0 f')
  match20 f' hf' :=
    tail_match_two hq hW h4 hne f' hf' ((tail_upperDatumHyp q hW hp hne).two0 f')
  match10 f' hf' :=
    tail_match_one hq hW h4 hne f' hf' ((tail_upperDatumHyp q hW hp hne).one0 f')

end Sarkozy.TailCorrCore
