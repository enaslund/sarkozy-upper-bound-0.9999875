module

public import Sarkozy.DensityChain2.Hfold

@[expose] public section

/-!
# Integration check: DC2's four `hdiff` constructors with DC3's `hfold`

The examples below type-check DC2's `DensityFibre.env/fixHdiffL/R_of_folded` (K2's
`Sh.envM.hdiffL/R`, `Sh.fixM.hdiffL/R`) with `hfold := hfold_env/fixL/R_paper`,
`Λ := envLambda` or `fixLambda`, `rch := rchEnv/FixL/R`, `ε := u_L`, for any `z` with
`R_err u_L ≤ z_L`. The resulting field's remainder is DC2's
`r₂ = ∑_{σ≠∅} rch + (R_err + z) K (Λ − 1)`, so the size of `rch` is what DC1's `_hr2` asks.
-/

namespace Sarkozy.DensityChain2

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **Integration check**: DC2's `DensityFibre.envHdiffL_of_folded` (K2's field 30's `hdiff`)
accepts DC3's `hfold_envL_paper`, `envLambda`, `rchEnvL`, `ε = u`. -/
example (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q)) {ε₀ C1 C71 : ℝ}
    (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.envIncL D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.envIncL D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (z : ℕ → ℝ)
    (hz : ∀ L, D.GB.Rerr * scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L
      ≤ z L) : True := by
  have := DensityFibre.envHdiffL_of_folded hcop D hpair z
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) hz (fun L A Jq ω => envLambda hcop L A Jq ω)
    (fun L A Jq ω => envLambda_nonneg hcop L A Jq ω) dec (rchEnvL hcop D hpair dec C1 C71 σ')
    (hfold_envL_paper hcop hdcb hC1 hC71 D hpair dec ha hpar hsel hne hσ' hS1 hatomP hatomM)
  trivial

/-- **Integration check**: DC2's `DensityFibre.envHdiffR_of_folded` (K2's field 31's `hdiff`)
accepts DC3's `hfold_envR_paper`, `envLambda`, `rchEnvR`, `ε = u`. -/
example (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q)) {ε₀ C1 C71 : ℝ}
    (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.envIncR D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.envIncR D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (z : ℕ → ℝ)
    (hz : ∀ L, D.GB.Rerr * scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L
      ≤ z L) : True := by
  have := DensityFibre.envHdiffR_of_folded hcop D hpair z
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) hz (fun L A Jq ω => envLambda hcop L A Jq ω)
    (fun L A Jq ω => envLambda_nonneg hcop L A Jq ω) dec (rchEnvR hcop D hpair dec C1 C71 σ')
    (hfold_envR_paper hcop hdcb hC1 hC71 D hpair dec ha hpar hsel hne hσ' hS1 hatomP hatomM)
  trivial

/-- **Integration check**: DC2's `DensityFibre.fixHdiffL_of_folded` (K2's `Sh.fixM.hdiffL`)
accepts DC3's `hfold_fixL_paper`, `fixLambda`, `rchFixL`, `ε = u`. -/
example (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q)) {ε₀ C1 C71 : ℝ}
    (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (z : ℕ → ℝ)
    (hz : ∀ L, D.GB.Rerr * scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L
      ≤ z L) : True := by
  have := DensityFibre.fixHdiffL_of_folded hcop D hpair z
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) hz (fun L A S Jq ω => fixLambda hcop L A S 0 Jq ω)
    (fun L A S Jq ω => fixLambda_nonneg hcop L A S 0 Jq ω) dec (rchFixL hcop D hpair dec C1 C71 σ')
    (hfold_fixL_paper hcop hdcb hC1 hC71 D hpair dec ha hpar hsel hne hσ' hS1 hatomP hatomM)
  trivial

/-- **Integration check**: DC2's `DensityFibre.fixHdiffR_of_folded` (K2's `Sh.fixM.hdiffR`)
accepts DC3's `hfold_fixR_paper`, `fixLambda`, `rchFixR`, `ε = u`. -/
example (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q)) {ε₀ C1 C71 : ℝ}
    (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (z : ℕ → ℝ)
    (hz : ∀ L, D.GB.Rerr * scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L
      ≤ z L) : True := by
  have := DensityFibre.fixHdiffR_of_folded hcop D hpair z
    (fun L => scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L)
    (fun L => scaleU_nonneg' _ _ _ L) hz (fun L A S Jq ω => fixLambda hcop L A S 1 Jq ω)
    (fun L A S Jq ω => fixLambda_nonneg hcop L A S 1 Jq ω) dec (rchFixR hcop D hpair dec C1 C71 σ')
    (hfold_fixR_paper hcop hdcb hC1 hC71 D hpair dec ha hpar hsel hne hσ' hS1 hatomP hatomM)
  trivial

end Sarkozy.DensityChain2
