module

public import Sarkozy.SharpSums.Final
public import Sarkozy.SharpSums.PriceMeansFix

@[expose] public section

/-!
# The constructor of `SharpBaseInputsPT` with only the large pieces open

SUM (8 November 2026). With `PriceMeansEnvL/R` and `PriceMeansFixL/R` proved
(`SharpSums.PriceMeans`, `SharpSums.PriceMeansFix`, constant `C_P = (K M²)^a K`), the remaining
inputs of SH2's four summations are the four large-piece sums `LargeSumPT*`
(`lem:record:density-lp` at the folded pieces). **`SharpSumInputsL.toSharpBaseInputsPT`**.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpSums

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2 Sarkozy.SharpBase Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)

/-- **The remaining inputs of SH2's four summations after SUM** (`lem:sharp-first`, the error
terms): `SF` (as in `SharpBaseInputsPT`) and the four large-piece sums `LargeSumPT*`
(`lem:record:density-lp` at the folded pieces, constant `c_L ≥ 0`). The chain² parts, the cross
terms, `Y ≲ L^{2σ} α` and the main-price means are proved. 7 fields. -/
structure SharpSumInputsL {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF` on the baseline route (TH's `SharpFirstBaseInputs`). *Open*: `SF.hfold`, `SF.hrem`. -/
  SF : ThetaOne.SharpFirstBaseInputs D.data
  /-- The constant of the large-piece sums. -/
  cL : ℝ
  hcL : 0 ≤ cL
  /-- The large pieces of `Sh.fixM.hr2L`. *Open*. -/
  largeFixL : LargeSumPTFixL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The large pieces of `Sh.fixM.hr2R`. *Open*. -/
  largeFixR : LargeSumPTFixR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The large pieces of `Sh.envM.hr2L`. *Open*. -/
  largeEnvL : LargeSumPTEnvL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The large pieces of `Sh.envM.hr2R`. *Open*. -/
  largeEnvR : LargeSumPTEnvR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL

/-- **`SharpSumInputsP` from `SharpSumInputsL`**: the four main-price means proved, at
`C_P = (K M²)^a K` (`priceMeansEnvL/R` with `(K M²)^a ≤ (K M²)^a K`, `priceMeansFixL/R`). -/
noncomputable def SharpSumInputsL.toSharpSumInputsP {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputsL D) : SharpSumInputsP D where
  SF := I.SF
  CP := cPrice D.data
  hPFixL := (priceMeans_all _ D.data TargetLedger.targetDecay_nonneg).2.2.1
  hPFixR := (priceMeans_all _ D.data TargetLedger.targetDecay_nonneg).2.2.2
  hPEnvL := (priceMeans_all _ D.data TargetLedger.targetDecay_nonneg).1
  hPEnvR := (priceMeans_all _ D.data TargetLedger.targetDecay_nonneg).2.1
  cL := I.cL
  hcL := I.hcL
  largeFixL := I.largeFixL
  largeFixR := I.largeFixR
  largeEnvL := I.largeEnvL
  largeEnvR := I.largeEnvR

/-- **The constructor of SH2's `SharpBaseInputsPT`** (`lem:sharp-first`, the error-term
summation) with only `SF` and the four large-piece sums open. -/
noncomputable def SharpSumInputsL.toSharpBaseInputsPT {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputsL D) : SharpBaseInputsPT D :=
  I.toSharpSumInputsP.toSharpBaseInputsPT

/-- **Non-vacuity: `SharpSumInputsL` is no stronger than SH2's `SharpBaseInputsPT`.** Every
`SharpBaseInputsPT D` gives a `SharpSumInputsL D` with the same `SF` and `c_L = c₂` (the lossless
split, `largeSumPT*_of_rchSum`). -/
noncomputable def SharpSumInputsL.ofSharpBaseInputsPT {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpBaseInputsPT D) : SharpSumInputsL D where
  SF := I.SF
  cL := I.c₂
  hcL := I.hc₂
  largeFixL := largeSumPTFixL_of_rchSum _ D.data paper_pairwise I.SF.dec I.fixL
  largeFixR := largeSumPTFixR_of_rchSum _ D.data paper_pairwise I.SF.dec I.fixR
  largeEnvL := largeSumPTEnvL_of_rchSum _ D.data paper_pairwise I.SF.dec I.envL
  largeEnvR := largeSumPTEnvR_of_rchSum _ D.data paper_pairwise I.SF.dec I.envR

end Sarkozy.SharpSums
