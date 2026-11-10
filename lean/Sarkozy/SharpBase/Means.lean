module

public import Sarkozy.SharpBase.R2

@[expose] public section

/-!
# `Sh.fixM`, `Sh.envM` at `ϑ = 1` from the summation of `rch` alone

SH2 (7 November 2026). `ThetaOne.FixMeansTheta1` and `ThetaOne.EnvMeansTheta1` (the groups
`Sh.fixM`, `Sh.envM` of `main_goal_theta1k`) have the open fields `hdiffL/R`, `hzu`, `hr2L/R`.
The constructors here fill them at the paper's `z = zBase` and `r₂ = r2EnvL/R`, `r2FixL/R`:

* `hdiffL/R` (`lem:sharp-first` for the bracket of `lem:bracket-energy`): **proved**, by DC2's
  `env/fixHdiffL/R_of_folded` with `SharpBase.hfoldOpt_env/fixL/R_paper` (DC3's chain bounds,
  re-optimized AM–GM ratio), whose moment inputs `hatomP/M` are proved at `ϑ = 1`
  (`SharpBase.hatomP_base`, `hatomM_base`), at the constants of DC1's `density_dc_block'`
  (`ε₀ = 1/100`, `σ = 4/825`);
* `hzu` (`lem:scale-conditions`): **proved** for every `L` (`scaleU_le_zBase`), with `z → 0`;
* `hr2L/R`: from the summation of the explicit `rch` (`RchSumEnvL/R`, `RchSumFixL/R`), which is
  the only remaining input (*open*, `lem:sharp-first`'s error terms).

Inputs besides `RchSum*`: the decomposition family `dec` (data; `nonempty_decFamily`), `0 ≤ a`,
the parity condition, nonempty blocks and `blockSel ≤ selPre` (proved for the paper's data,
`SharpBase.Parts`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpBase

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps Sarkozy.DensityChain2
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **`Sh.envM` at `ϑ = 1` from the summation of `rch`** (fields 30–31; `lem:envelope-energy`,
`lem:hyb:moment`, `lem:bracket-energy`, `lem:sharp-first`). `hdiffL/R` and `hzu` are proved;
`hr2L/R` come from `RchSumEnvL/R`. -/
noncomputable def envMeansBase (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hL : RchSumEnvL hcop D hpair dec c₂) (hR : RchSumEnvR hcop D hpair dec c₂) :
    ThetaOne.EnvMeansTheta1 hcop D hpair where
  z := zBase D
  hz0 := zBase_nonneg D
  hzt := tendsto_zBase D
  r2L := r2EnvL hcop D hpair dec
  r2R := r2EnvR hcop D hpair dec
  hdiffL := DensityFibre.envHdiffL_of_folded hcop D hpair (zBase D)
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) (Rerr_mul_le_zBase D)
    (fun L A Jq ω => envLambda hcop L A Jq ω) (fun L A Jq ω => envLambda_nonneg hcop L A Jq ω)
    dec (rchOptEnvL hcop D hpair dec C1₀ C71₀ sigmaR)
    (hfoldOpt_envL_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.envIncL D L b)
        (fun L b => isPositiveRecord_envIncL D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.envIncL D L b)
        (fun L b => isPositiveRecord_envIncL D L b) dec))
  hdiffR := DensityFibre.envHdiffR_of_folded hcop D hpair (zBase D)
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) (Rerr_mul_le_zBase D)
    (fun L A Jq ω => envLambda hcop L A Jq ω) (fun L A Jq ω => envLambda_nonneg hcop L A Jq ω)
    dec (rchOptEnvR hcop D hpair dec C1₀ C71₀ sigmaR)
    (hfoldOpt_envR_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.envIncR D L b)
        (fun L b => isPositiveRecord_envIncR D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.envIncR D L b)
        (fun L b => isPositiveRecord_envIncR D L b) dec))
  hzu := Eventually.of_forall (scaleU_le_zBase D)
  c₂ := c₂
  hc₂ := hc₂
  hr2L := hr2EnvL_of_rch hcop D hpair dec hL
  hr2R := hr2EnvR_of_rch hcop D hpair dec hR

/-- **`Sh.fixM` at `ϑ = 1` from the summation of `rch`** (fields 26–29; `lem:envelope-energy`,
`lem:twointerval`(ii), `lem:bracket-energy`, `lem:sharp-first`). `hdiffL/R` and `hzu` are
proved; `hr2L/R` come from `RchSumFixL/R`. -/
noncomputable def fixMeansBase (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hL : RchSumFixL hcop D hpair dec c₂) (hR : RchSumFixR hcop D hpair dec c₂) :
    ThetaOne.FixMeansTheta1 hcop D hpair where
  z := zBase D
  hz0 := zBase_nonneg D
  hzt := tendsto_zBase D
  r2L := r2FixL hcop D hpair dec
  r2R := r2FixR hcop D hpair dec
  hdiffL := DensityFibre.fixHdiffL_of_folded hcop D hpair (zBase D)
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) (Rerr_mul_le_zBase D)
    (fun L A S Jq ω => fixLambda hcop L A S 0 Jq ω)
    (fun L A S Jq ω => fixLambda_nonneg hcop L A S 0 Jq ω)
    dec (rchOptFixL hcop D hpair dec C1₀ C71₀ sigmaR)
    (hfoldOpt_fixL_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec))
  hdiffR := DensityFibre.fixHdiffR_of_folded hcop D hpair (zBase D)
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) (Rerr_mul_le_zBase D)
    (fun L A S Jq ω => fixLambda hcop L A S 1 Jq ω)
    (fun L A S Jq ω => fixLambda_nonneg hcop L A S 1 Jq ω)
    dec (rchOptFixR hcop D hpair dec C1₀ C71₀ sigmaR)
    (hfoldOpt_fixR_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec))
  hzu := Eventually.of_forall (scaleU_le_zBase D)
  c₂ := c₂
  hc₂ := hc₂
  hr2L := hr2FixL_of_rch hcop D hpair dec hL
  hr2R := hr2FixR_of_rch hcop D hpair dec hR

end Sarkozy.SharpBase
