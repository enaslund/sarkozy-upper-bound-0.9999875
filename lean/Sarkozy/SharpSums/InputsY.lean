module

public import Sarkozy.SharpSums.Cross

@[expose] public section

/-!
# The constructor of `SharpBaseInputsPT` with the cross terms reduced

SUM (7 November 2026). `SharpSumInputsY D` replaces the four cross sums of `SharpSumInputs D` by
* one bound `Y ≤ C_Y L^{2/825} α` at counterexamples (`hY`), and
* four mean bounds of the main prices of the folds (`PriceMeans*`, constant `C_P`),
through `crossSumPT*_of_bounds`. **`SharpSumInputsY.toSharpBaseInputsPT`** composes with
`SharpSumInputs.toSharpBaseInputsPT`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpSums

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.SharpBase2 Sarkozy.SharpBase
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **`Y ≲ L^{2σ} α` at counterexamples** (the input `hY` of `crossSumPT*_of_bounds`). The paper
does not state it; its route gives `Y ≤ C_ε N^ε α` (Hölder in `L^{72}` with uniform marginals and
`lem:record:lift-moments`(c), as in the proof of `lem:record:density-lp`), which implies this for
`ε ≤ 2/825`. *Open*. -/
def YBound (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (CY : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    D.Y L A ≤ CY * (L : ℝ) ^ (2 * Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- The cross constant of `Sh.envM`: `√(2 C_dc C_Y) e^{T + U₀ + ∑_j (d_j + v_j)} · 2|𝔗| √C_P`. -/
noncomputable def cXEnv (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (CY CP : ℝ) : ℝ :=
  Real.sqrt (2 * cdc0 D * CY) * Real.exp (D.ME.T + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
    (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)

/-- The cross constant of `Sh.fixM`: as `cXEnv` with `S + A` in place of `T`. -/
noncomputable def cXFix (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (CY CP : ℝ) : ℝ :=
  Real.sqrt (2 * cdc0 D * CY) *
    Real.exp (D.CL.S + D.CL.A + D.GB.U₀ + ∑ j, (D.FS.dT j + D.FS.vT j)) *
    (2 * (Fintype.card D.FS.Tag : ℝ) * Real.sqrt CP)

omit [DecidableEq P] in
theorem cXEnv_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (CY CP : ℝ) :
    0 ≤ cXEnv D CY CP := by
  unfold cXEnv
  have := Real.sqrt_nonneg (2 * cdc0 D * CY)
  have := Real.sqrt_nonneg CP
  positivity

omit [DecidableEq P] in
theorem cXFix_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (CY CP : ℝ) :
    0 ≤ cXFix D CY CP := by
  unfold cXFix
  have := Real.sqrt_nonneg (2 * cdc0 D * CY)
  have := Real.sqrt_nonneg CP
  positivity

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The means of the main prices of the folds of `rchPTEnvL`** (B9's local-density means with
the per-query exponents of the folds): at counterexamples, `E_𝒥 E_ω P_±(j) ≤ C_P` at every tag.
*Open*; the input `hP` of `crossSumPTEnvL_of_bounds`. -/
def PriceMeansEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (CP : ℝ) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ j : D.FS.Tag,
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)

/-- **The means of the main prices of the folds of `rchPTEnvR`** (B9's local-density means with
the per-query exponents of the folds): at counterexamples, `E_𝒥 E_ω P_±(j) ≤ C_P` at every tag.
*Open*; the input `hP` of `crossSumPTEnvR_of_bounds`. -/
def PriceMeansEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (CP : ℝ) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ j : D.FS.Tag,
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)

/-- **The means of the main prices of the folds of `rchPTFixL`** (B9's local-density means with
the per-query exponents of the folds): at counterexamples, `E_𝒥 E_ω P_±(j) ≤ C_P` at every tag.
*Open*; the input `hP` of `crossSumPTFixL_of_bounds`. -/
def PriceMeansFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (CP : ℝ) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ S : Finset E, S ≠ ∅ → ∀ j : D.FS.Tag,
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)

/-- **The means of the main prices of the folds of `rchPTFixR`** (B9's local-density means with
the per-query exponents of the folds): at counterexamples, `E_𝒥 E_ω P_±(j) ≤ C_P` at every tag.
*Open*; the input `hP` of `crossSumPTFixR_of_bounds`. -/
def PriceMeansFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (CP : ℝ) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ S : Finset E, S ≠ ∅ → ∀ j : D.FS.Tag,
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus)) ≤
        CP ∧
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus)) ≤
        CP)

end Sarkozy.SharpSums

namespace Sarkozy.SharpSums

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2 Sarkozy.SharpBase Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)

/-- **The remaining inputs of SH2's four summations, with the cross terms reduced**
(`lem:sharp-first`, the error terms): `SF`; `Y ≤ C_Y L^{2/825} α` at counterexamples (`hY`); the
means of the main prices of the folds (`PriceMeans*`, constant `C_P`); the four large-piece sums
(`LargeSumPT*`, `lem:record:density-lp`, constant `c_L`). The chain² parts are proved. -/
structure SharpSumInputsY {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF` on the baseline route (TH's `SharpFirstBaseInputs`). *Open*: `SF.hfold`, `SF.hrem`. -/
  SF : ThetaOne.SharpFirstBaseInputs D.data
  /-- The constant of `Y ≲ L^{2σ} α`. -/
  CY : ℝ
  hCY : 0 ≤ CY
  /-- `Y ≤ C_Y L^{2/825} α` at counterexamples. *Open*. -/
  hY : YBound D.data CY
  /-- The constant of the main-price means. -/
  CP : ℝ
  /-- The main-price means of `fixC` (L). *Open*. -/
  hPFixL : PriceMeansFixL (BlockAnchor.index_coprime_block D.data) D.data CP
  /-- The main-price means of `fixC` (R). *Open*. -/
  hPFixR : PriceMeansFixR (BlockAnchor.index_coprime_block D.data) D.data CP
  /-- The main-price means of `envC` (L). *Open*. -/
  hPEnvL : PriceMeansEnvL (BlockAnchor.index_coprime_block D.data) D.data CP
  /-- The main-price means of `envC` (R). *Open*. -/
  hPEnvR : PriceMeansEnvR (BlockAnchor.index_coprime_block D.data) D.data CP
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

/-- **`SharpSumInputs` from `SharpSumInputsY`** (`crossSumPT*_of_bounds` at the paper's standing
data), with `c_X = cXEnv + cXFix`. -/
noncomputable def SharpSumInputsY.toSharpSumInputs {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputsY D) : SharpSumInputs D where
  SF := I.SF
  cX := cXEnv D.data I.CY I.CP + cXFix D.data I.CY I.CP
  cL := I.cL
  hcX := add_nonneg (cXEnv_nonneg _ _ _) (cXFix_nonneg _ _ _)
  hcL := I.hcL
  crossFixL := by
    have h := crossSumPTFixL_of_bounds _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.hCY I.hY I.hPFixL
    unfold CrossSumPTFixL at h ⊢
    exact atCex_le_mono_S (by unfold cXFix; linarith [cXEnv_nonneg D.data I.CY I.CP]) h
  largeFixL := I.largeFixL
  crossFixR := by
    have h := crossSumPTFixR_of_bounds _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.hCY I.hY I.hPFixR
    unfold CrossSumPTFixR at h ⊢
    exact atCex_le_mono_S (by unfold cXFix; linarith [cXEnv_nonneg D.data I.CY I.CP]) h
  largeFixR := I.largeFixR
  crossEnvL := by
    have h := crossSumPTEnvL_of_bounds _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.hCY I.hY I.hPEnvL
    unfold CrossSumPTEnvL at h ⊢
    exact atCex_le_mono (by unfold cXEnv; linarith [cXFix_nonneg D.data I.CY I.CP]) h
  largeEnvL := I.largeEnvL
  crossEnvR := by
    have h := crossSumPTEnvR_of_bounds _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.hCY I.hY I.hPEnvR
    unfold CrossSumPTEnvR at h ⊢
    exact atCex_le_mono (by unfold cXEnv; linarith [cXFix_nonneg D.data I.CY I.CP]) h
  largeEnvR := I.largeEnvR

/-- **A constructor of SH2's `SharpBaseInputsPT`** from `SharpSumInputsY`: the chain² parts
proved, the cross terms reduced to `hY` and the price means. -/
noncomputable def SharpSumInputsY.toSharpBaseInputsPT {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputsY D) : SharpBaseInputsPT D :=
  I.toSharpSumInputs.toSharpBaseInputsPT

end Sarkozy.SharpSums
