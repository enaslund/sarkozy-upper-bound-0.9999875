module

public import Sarkozy.MainTarget.Bridge
public import Sarkozy.MainTarget.IndexMoment

@[expose] public section






namespace Sarkozy.MainTarget

open Sarkozy.CancellationSteps

/-- **The bound `N^{1 − a_T/71}` at CERT1's level** (`thm:main` at the target exponent): from the
literature inputs, H2″ (`Target.ThetaSmallRR`, for `cert:index-moment` at `a_T`) and
`BlockCertObligationsTarget blk` (the envelope hypotheses as propositions), for any block
assignment `blk` of the fixed primes. -/
theorem main_target_paper_block_cert {Bk : Type} [Fintype Bk] [DecidableEq Bk]
    {blk : PaperJ0 → Bk} (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : BlockCertObligationsTarget blk hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_cert_of_hR hWeil hMovingRoot hFourCycle
    (paperRIAt_le_targetLedger hThetaSmallRR) O

/-- **The bound `N^{1 − a_T/71}` at G1's level** (`thm:main` at the target exponent): from the
literature inputs, H2″ (`Target.ThetaSmallRR`, for `cert:index-moment` at `a_T`) and
`BlockFinalObligationsTarget blk`, for any block assignment `blk` of the fixed primes. -/
theorem main_target_paper_block_final {Bk : Type} [Fintype Bk] [DecidableEq Bk]
    {blk : PaperJ0 → Bk} (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : BlockFinalObligationsTarget blk hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_final_of_hR hWeil hMovingRoot hFourCycle
    (paperRIAt_le_targetLedger hThetaSmallRR) O

/-- **The main statement at the owner's target** (`thm:main` at `ε = a_T/71`, i.e.
`s(N) ≤ C N^{1 − a_T/71}`, via `thm:comparison` and `thm:density:induction` at
`a_T = TargetLedger.targetDecay`, `71/10⁵` since RG's rebase): from the literature inputs `Weil`,
`MovingRoot`, `FourCycle` and H2″ (`ThetaSmallRR`), and
`V2FinalObligationsTarget blockOf` (the Part V obligations at `a_T`, with the paper's block laws and
the tail inputs in correlation form), for any partition `blockOf` of the class-three primes into
blocks. -/
theorem main_target_paper_block {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : V2FinalObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_v2_of_hR hWeil hMovingRoot hFourCycle
    (paperRIAt_le_targetLedger hThetaSmallRR) O

end Sarkozy.MainTarget
