module

public import Sarkozy.SharpBase2.Parts

@[expose] public section

/-!
# Sanity checks for the per-term route

SH2 (7 November 2026). As in `SharpBase.Sanity`: the constructors `envMeansPT`, `fixMeansPT` put
the per-term `r₂` (`r2PTEnvL/R`, `r2PTFixL/R`) in the slot read by `hdiffL/R` and by `hr2L/R`,
and TH's conversions to B9's bundles (whose `hmL/R` the endgame reads) keep it. So `hdiff` and
the mean bounds are checked jointly through one explicit `r₂` (DC2's finding 1).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpBase2

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps Sarkozy.DensityChain2
  Sarkozy.SharpBase

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
  (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
    (joinModuli m₀ (paperTail L) j))
  (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
  (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
  (hne : ∀ β, ∃ i, blk i = β) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)

/-- **One `r₂` for `hdiff` and the mean bounds of `envC`** (per-term route). -/
theorem envMeansPT_toB9 (hL : RchSumPTEnvL hcop D hpair dec c₂)
    (hR : RchSumPTEnvR hcop D hpair dec c₂) :
    (envMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).r2L = r2PTEnvL hcop D hpair dec ∧
      ((envMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toEnvMeansInputs ha hpar hne
        hsel).r2L = r2PTEnvL hcop D hpair dec ∧
      ((envMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toEnvMeansInputs ha hpar hne
        hsel).r2R = r2PTEnvR hcop D hpair dec ∧
      ((envMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toEnvMeansInputs ha hpar hne
        hsel).z = zBase D :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **One `r₂` for `hdiff` and the mean bounds of `fixC`** (per-term route). -/
theorem fixMeansPT_toB9 (hL : RchSumPTFixL hcop D hpair dec c₂)
    (hR : RchSumPTFixR hcop D hpair dec c₂) :
    (fixMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).r2L = r2PTFixL hcop D hpair dec ∧
      ((fixMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toFixMeansInputs ha hpar hne
        hsel).r2L = r2PTFixL hcop D hpair dec ∧
      ((fixMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toFixMeansInputs ha hpar hne
        hsel).r2R = r2PTFixR hcop D hpair dec ∧
      ((fixMeansPT hcop D hpair dec ha hpar hsel hne c₂ hc₂ hL hR).toFixMeansInputs ha hpar hne
        hsel).z = zBase D :=
  ⟨rfl, rfl, rfl, rfl⟩

end Sarkozy.SharpBase2
