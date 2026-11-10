module

public import Sarkozy.SharpSums.Sums
public import Sarkozy.SharpBase2.Parts

@[expose] public section

/-!
# A constructor of SH2's `SharpBaseInputsPT` from the cross and large-piece sums

SUM (7 November 2026).

* `atCex_le_mono`, `atCex_le_mono_S`: a density-linear bound at counterexamples is monotone in
  its constant;
* **lossless split** (`crossSumPT*_of_rchSum`, `largeSumPT*_of_rchSum`): each of the eight new
  inputs `CrossSumPT*`, `LargeSumPT*` follows from the corresponding `RchSumPT*` with the same
  constant (the three parts are nonnegative). So the new inputs are no stronger than SH2's, and
  the reduction `rchSumPT*_of_parts` only removes the chain² part;
* **`SharpSumInputs D`**: `SF`, two constants `c_X, c_L ≥ 0`, and the eight labelled sums;
* **`SharpSumInputs.toSharpBaseInputsPT`**: SH2's `SharpBaseInputsPT D` with
  `c₂ = c_X + c_L + chainConstEnv + chainConstFix` (the chain² parts proved).
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

/-- A density-linear bound `F ≤ c L^{-1/825} α` at counterexamples is monotone in `c`. -/
theorem atCex_le_mono {Pm : Params} {Y : ℕ → Finset ℤ → ℝ} {F : ℕ → Finset ℤ → ℝ} {c c' : ℝ}
    (hc : c ≤ c')
    (h : Param.AtCounterexamples Pm Y (fun L A =>
      F L A ≤ c * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)) :
    Param.AtCounterexamples Pm Y (fun L A =>
      F L A ≤ c' * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [h] with L hL
  intro C hC hk A hA hY
  exact (hL C hC hk A hA hY).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (density_nonneg _ _))

/-- `atCex_le_mono` for bounds over the nonempty `S`. -/
theorem atCex_le_mono_S {Pm : Params} {Y : ℕ → Finset ℤ → ℝ} {ι : Type}
    {F : ℕ → Finset ℤ → Finset ι → ℝ} {c c' : ℝ} (hc : c ≤ c')
    (h : Param.AtCounterexamples Pm Y (fun L A => ∀ S : Finset ι, S ≠ ∅ →
      F L A S ≤ c * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)) :
    Param.AtCounterexamples Pm Y (fun L A => ∀ S : Finset ι, S ≠ ∅ →
      F L A S ≤ c' * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [h] with L hL
  intro C hC hk A hA hY S hS
  exact (hL C hC hk A hA hY S hS).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (density_nonneg _ _))

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
theorem chainConstEnv_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) :
    0 ≤ chainConstEnv D :=
  mul_nonneg (cdc0_nonneg D) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))

omit [DecidableEq P] in
theorem chainConstFix_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) :
    0 ≤ chainConstFix D :=
  mul_nonneg (cdc0_nonneg D) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The split of `RchSumPTEnvL` is lossless, cross part**: `RchSumPTEnvL c` implies
`CrossSumPTEnvL c` (the chain² and large parts are nonnegative). -/
theorem crossSumPTEnvL_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTEnvL hcop D hpair dec c) : CrossSumPTEnvL hcop D hpair dec c := by
  unfold RchSumPTEnvL at hR
  unfold CrossSumPTEnvL
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY
  refine le_trans ?_ (hL C hC hk A hA hY)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTEnvL_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold chainPTEnvL rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h2 : 0 ≤ largePTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold largePTEnvL rchLarge
    exact largePart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  linarith

/-- **The split of `RchSumPTEnvL` is lossless, large part**: `RchSumPTEnvL c` implies
`LargeSumPTEnvL c`. -/
theorem largeSumPTEnvL_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTEnvL hcop D hpair dec c) : LargeSumPTEnvL hcop D hpair dec c := by
  unfold RchSumPTEnvL at hR
  unfold LargeSumPTEnvL
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY
  refine le_trans ?_ (hL C hC hk A hA hY)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTEnvL_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold chainPTEnvL rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h0 : 0 ≤ crossPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold crossPTEnvL rchCross
    exact crossPart_nonneg _ _ _ _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  have h4 := mul_nonneg (Real.sqrt_nonneg (crDC D C1₀ C71₀ sigmaR L A)) h0
  linarith

/-- **The split of `RchSumPTEnvR` is lossless, cross part**: `RchSumPTEnvR c` implies
`CrossSumPTEnvR c` (the chain² and large parts are nonnegative). -/
theorem crossSumPTEnvR_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTEnvR hcop D hpair dec c) : CrossSumPTEnvR hcop D hpair dec c := by
  unfold RchSumPTEnvR at hR
  unfold CrossSumPTEnvR
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY
  refine le_trans ?_ (hL C hC hk A hA hY)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTEnvR_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold chainPTEnvR rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h2 : 0 ≤ largePTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold largePTEnvR rchLarge
    exact largePart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  linarith

/-- **The split of `RchSumPTEnvR` is lossless, large part**: `RchSumPTEnvR c` implies
`LargeSumPTEnvR c`. -/
theorem largeSumPTEnvR_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTEnvR hcop D hpair dec c) : LargeSumPTEnvR hcop D hpair dec c := by
  unfold RchSumPTEnvR at hR
  unfold LargeSumPTEnvR
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY
  refine le_trans ?_ (hL C hC hk A hA hY)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTEnvR_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold chainPTEnvR rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h0 : 0 ≤ crossPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ j := by
    unfold crossPTEnvR rchCross
    exact crossPart_nonneg _ _ _ _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  have h4 := mul_nonneg (Real.sqrt_nonneg (crDC D C1₀ C71₀ sigmaR L A)) h0
  linarith

/-- **The split of `RchSumPTFixL` is lossless, cross part**: `RchSumPTFixL c` implies
`CrossSumPTFixL c` (the chain² and large parts are nonnegative). -/
theorem crossSumPTFixL_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTFixL hcop D hpair dec c) : CrossSumPTFixL hcop D hpair dec c := by
  unfold RchSumPTFixL at hR
  unfold CrossSumPTFixL
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY S hS
  refine le_trans ?_ (hL C hC hk A hA hY S hS)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTFixL_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold chainPTFixL rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h2 : 0 ≤ largePTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold largePTFixL rchLarge
    exact largePart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  linarith

/-- **The split of `RchSumPTFixL` is lossless, large part**: `RchSumPTFixL c` implies
`LargeSumPTFixL c`. -/
theorem largeSumPTFixL_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTFixL hcop D hpair dec c) : LargeSumPTFixL hcop D hpair dec c := by
  unfold RchSumPTFixL at hR
  unfold LargeSumPTFixL
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY S hS
  refine le_trans ?_ (hL C hC hk A hA hY S hS)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTFixL_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold chainPTFixL rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h0 : 0 ≤ crossPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold crossPTFixL rchCross
    exact crossPart_nonneg _ _ _ _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  have h4 := mul_nonneg (Real.sqrt_nonneg (crDC D C1₀ C71₀ sigmaR L A)) h0
  linarith

/-- **The split of `RchSumPTFixR` is lossless, cross part**: `RchSumPTFixR c` implies
`CrossSumPTFixR c` (the chain² and large parts are nonnegative). -/
theorem crossSumPTFixR_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTFixR hcop D hpair dec c) : CrossSumPTFixR hcop D hpair dec c := by
  unfold RchSumPTFixR at hR
  unfold CrossSumPTFixR
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY S hS
  refine le_trans ?_ (hL C hC hk A hA hY S hS)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTFixR_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold chainPTFixR rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h2 : 0 ≤ largePTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold largePTFixR rchLarge
    exact largePart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  linarith

/-- **The split of `RchSumPTFixR` is lossless, large part**: `RchSumPTFixR c` implies
`LargeSumPTFixR c`. -/
theorem largeSumPTFixR_of_rchSum (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c : ℝ}
    (hR : RchSumPTFixR hcop D hpair dec c) : LargeSumPTFixR hcop D hpair dec c := by
  unfold RchSumPTFixR at hR
  unfold LargeSumPTFixR
  filter_upwards [hR] with L hL
  intro C hC hk A hA hY S hS
  refine le_trans ?_ (hL C hC hk A hA hY S hS)
  refine FiniteLaw.expect_mono _ fun Jq => FiniteLaw.expect_mono _ fun ω => ?_
  refine sum_le_sum fun f _ => sum_le_sum fun σ _ => ?_
  rw [rchPTFixR_eq_parts hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ (crDC_nonneg D L A)]
  refine sum_le_sum fun j _ => ?_
  have h1 : 0 ≤ chainPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold chainPTFixR rchChain
    exact chainPart_nonneg _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h0 : 0 ≤ crossPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ j := by
    unfold crossPTFixR rchCross
    exact crossPart_nonneg _ _ _ _ _ _ _ fun φ => choiceWeight_nonneg' D L f σ j φ
  have h3 := mul_nonneg (crDC_nonneg D L A) h1
  have h4 := mul_nonneg (Real.sqrt_nonneg (crDC D C1₀ C71₀ sigmaR L A)) h0
  linarith

end Sarkozy.SharpSums

namespace Sarkozy.SharpSums

open Sarkozy.PartV Sarkozy.JointClosing Sarkozy.BlockSpecPaper Sarkozy.MainCombined
  Sarkozy.MainCombined2 Sarkozy.SharpBase Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.CancellationSteps (PaperJ0)

/-- **The remaining inputs of SH2's four summations after SUM** (`lem:sharp-first`, the error
terms): `SF` as in `SharpBaseInputsPT`, two constants `c_X, c_L ≥ 0`, and for each of the four
summations the summed cross terms (`CrossSumPT*`, main × chain remainder,
`prop:record:density-structured`) and the summed large pieces (`LargeSumPT*`,
`lem:record:density-lp`). The chain² parts are proved (`chainSum_*_le`). 13 fields. -/
structure SharpSumInputs {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF` on the baseline route (TH's `SharpFirstBaseInputs`). *Open*: `SF.hfold`, `SF.hrem`. -/
  SF : ThetaOne.SharpFirstBaseInputs D.data
  /-- The constant of the cross sums. -/
  cX : ℝ
  /-- The constant of the large-piece sums. -/
  cL : ℝ
  hcX : 0 ≤ cX
  hcL : 0 ≤ cL
  /-- The cross terms of `Sh.fixM.hr2L`. *Open*. -/
  crossFixL : CrossSumPTFixL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cX
  /-- The large pieces of `Sh.fixM.hr2L`. *Open*. -/
  largeFixL : LargeSumPTFixL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The cross terms of `Sh.fixM.hr2R`. *Open*. -/
  crossFixR : CrossSumPTFixR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cX
  /-- The large pieces of `Sh.fixM.hr2R`. *Open*. -/
  largeFixR : LargeSumPTFixR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The cross terms of `Sh.envM.hr2L`. *Open*. -/
  crossEnvL : CrossSumPTEnvL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cX
  /-- The large pieces of `Sh.envM.hr2L`. *Open*. -/
  largeEnvL : LargeSumPTEnvL (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL
  /-- The cross terms of `Sh.envM.hr2R`. *Open*. -/
  crossEnvR : CrossSumPTEnvR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cX
  /-- The large pieces of `Sh.envM.hr2R`. *Open*. -/
  largeEnvR : LargeSumPTEnvR (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise SF.dec
    cL

/-- The constant `c₂ = c_X + c_L + chainConstEnv + chainConstFix` of the four summations. -/
noncomputable def SharpSumInputs.c₂ {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputs D) : ℝ :=
  I.cX + I.cL + (chainConstEnv D.data + chainConstFix D.data)

/-- **A constructor of SH2's `SharpBaseInputsPT`** (`lem:sharp-first`, the error-term summation):
the four summation fields from `rchSumPT*_of_parts`, at the paper's standing data (parity
`parity_blockPaperStandingAt`, `blockSel ≤ selPre` by `hsel_blockPaperStandingAt`), with
`c₂ = c_X + c_L + chainConstEnv + chainConstFix`. -/
noncomputable def SharpSumInputs.toSharpBaseInputsPT {B : Type} [Fintype B] [DecidableEq B]
    {blockOf : PaperJ0 → B} {hW : Target.Weil} {D : JointBlockDataTarget blockOf hW}
    (I : SharpSumInputs D) : SharpBaseInputsPT D where
  SF := I.SF
  c₂ := I.c₂
  hc₂ := by
    unfold SharpSumInputs.c₂
    have := chainConstEnv_nonneg D.data
    have := chainConstFix_nonneg D.data
    have := I.hcX
    have := I.hcL
    linarith
  fixL := by
    have h := rchSumPTFixL_of_parts _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.crossFixL I.largeFixL
    unfold RchSumPTFixL at h ⊢
    refine atCex_le_mono_S ?_ h
    unfold SharpSumInputs.c₂
    linarith [chainConstEnv_nonneg D.data]
  fixR := by
    have h := rchSumPTFixR_of_parts _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.crossFixR I.largeFixR
    unfold RchSumPTFixR at h ⊢
    refine atCex_le_mono_S ?_ h
    unfold SharpSumInputs.c₂
    linarith [chainConstEnv_nonneg D.data]
  envL := by
    have h := rchSumPTEnvL_of_parts _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.crossEnvL I.largeEnvL
    unfold RchSumPTEnvL at h ⊢
    refine atCex_le_mono ?_ h
    unfold SharpSumInputs.c₂
    linarith [chainConstFix_nonneg D.data]
  envR := by
    have h := rchSumPTEnvR_of_parts _ D.data paper_pairwise I.SF.dec
      TargetLedger.targetDecay_nonneg
      (DensityChain2.parity_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      (DensityChain2.hsel_blockPaperStandingAt _ _ TargetLedger.targetDecay_nonneg _)
      I.crossEnvR I.largeEnvR
    unfold RchSumPTEnvR at h ⊢
    refine atCex_le_mono ?_ h
    unfold SharpSumInputs.c₂
    linarith [chainConstFix_nonneg D.data]

end Sarkozy.SharpSums
