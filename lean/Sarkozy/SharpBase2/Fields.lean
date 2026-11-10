module

public import Sarkozy.SharpBase2.HtermPT
public import Sarkozy.SharpBase.Means

@[expose] public section

/-!
# `Sh.fixM`, `Sh.envM` with the per-term remainders of `lem:sharp-first`

SH2 (7 November 2026). As `SharpBase.Hdiff`, `SharpBase.R2` and `SharpBase.Means`, with the
per-term remainders `rchPTEnvL/R`, `rchPTFixL/R` (`SharpBase2.HtermPT`) in place of the
whole-choice ones `rchOpt*`:

* `r2PTEnvL/R`, `r2PTFixL/R`: DC2's `r₂ = ∑_{σ≠∅} rch(σ) + (R_err + z) K (Λ − 1)`;
* `RchSumPTEnvL/R`, `RchSumPTFixL/R`: the summations of `rch` (*open*);
* `hr2PT*_of_rch`: `hr2L/R` from them (`E_ω Λ ≤ 1`, DC2's `expect_r2_le`);
* **`envMeansPT`**, **`fixMeansPT`**: `ThetaOne.EnvMeansTheta1`, `FixMeansTheta1` with
  `hdiffL/R` (through `hterm_*_paper` and DC2's `diff_bound_of_coupled_loc`) and `hzu` proved.

**What `RchSumPT*` asks.** Per tag, `rch` is `∑_φ w_φ pieceRem(φ)`: at a small piece the cross
terms `√(BG M₊ G₋ C) + √(G₊ C BG M₋) + √(G₊ C G₋ C)` (main × chain remainder, `C = C_dc
L^{-4/825} α`), at a large piece (`q_E > N^τ`, or an unrevealed interval) `√𝔈₊ √𝔈₋`. No main
term meets a large-piece energy, unlike the whole-choice folding (`SharpBase2.PerTerm`).
-/

namespace Sarkozy.SharpBase2

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps Sarkozy.DensityChain2
  Sarkozy.SharpBase
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-! ## The paper's remainders `r₂` with per-term geometric means -/

/-- **The remainder `r₂` of `Sh.envM.hdiffL`** (field 30): DC2's
`∑_{σ≠∅} rch(σ) + (R_err + z) K (Λ − 1)` with `rch = rchPTEnvL` (at `C₁₀`, `C₇₁₀`,
`σ = sigmaR`), `Λ = envLambda`, `z = zBase` (`lem:sharp-first`). -/
noncomputable def r2PTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) *
      (envLambda hcop L A Jq ω - 1)

/-- **The remainder `r₂` of `Sh.envM.hdiffR`** (field 31), as `r2PTEnvL` with `rchPTEnvR`. -/
noncomputable def r2PTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) *
      (envLambda hcop L A Jq ω - 1)

/-- **The remainder `r₂` of `Sh.fixM.hdiffL`**: DC2's `r₂` with `rchPTFixL`,
`Λ = fixLambda` at `t = 0`. -/
noncomputable def r2PTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
      (fixLambda hcop L A S 0 Jq ω - 1)

/-- **The remainder `r₂` of `Sh.fixM.hdiffR`**: DC2's `r₂` with `rchPTFixR`,
`Λ = fixLambda` at `t = 1`. -/
noncomputable def r2PTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
      (fixLambda hcop L A S 1 Jq ω - 1)

/-! ## The summation of `rch` (*open*) -/

/-- **The summation of the sharp-first remainders of `Sh.envM`, left** (`lem:sharp-first`, the
error terms; `lem:record:density-dc`, `lem:record:density-lp`): the explicit `rchPTEnvL`, summed
over `σ ≠ ∅` and `f`, averaged over `ω` and `𝒥`, is at most `c₂ L^{-1/825} α`. -/
def RchSumPTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summation of the sharp-first remainders of `Sh.envM`, right**: as `RchSumPTEnvL`, with
`rchPTEnvR`. -/
def RchSumPTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summation of the sharp-first remainders of `Sh.fixM`, left** (`lem:sharp-first`):
the explicit `rchPTFixL`, for every nonempty `𝒮`. -/
def RchSumPTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summation of the sharp-first remainders of `Sh.fixM`, right**: as `RchSumPTFixL`, with
`rchPTFixR`. -/
def RchSumPTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-! ## `hr2` from the summation of `rch` -/

/-- **`Sh.envM.hr2L` for the paper's `r₂`** from `RchSumPTEnvL` (DC2's `expect_r2_le` with
`E_ω envLambda ≤ 1`). -/
theorem hr2PTEnvL_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumPTEnvL hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2PTEnvL hcop D hpair dec L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
        · exact zero_le_one))
    (fun ω => envLambda hcop L A Jq ω) (expect_envLambda_le_one hcop hL1 hA.1 hα Jq)

/-- **`Sh.envM.hr2R` for the paper's `r₂`** from `RchSumPTEnvR`. -/
theorem hr2PTEnvR_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumPTEnvR hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2PTEnvR hcop D hpair dec L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
        · exact zero_le_one))
    (fun ω => envLambda hcop L A Jq ω) (expect_envLambda_le_one hcop hL1 hA.1 hα Jq)

/-- **`Sh.fixM.hr2L` for the paper's `r₂`** from `RchSumPTFixL` (DC2's `expect_r2_le` with
`E_ω fixLambda ≤ 1`). -/
theorem hr2PTFixL_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumPTFixL hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2PTFixL hcop D hpair dec L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY S hS
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY S hS)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one))
    (fun ω => fixLambda hcop L A S 0 Jq ω) (expect_fixLambda_le_one hcop hL1 hα S 0 Jq)

/-- **`Sh.fixM.hr2R` for the paper's `r₂`** from `RchSumPTFixR`. -/
theorem hr2PTFixR_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumPTFixR hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2PTFixR hcop D hpair dec L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY S hS
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY S hS)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchPTFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one))
    (fun ω => fixLambda hcop L A S 1 Jq ω) (expect_fixLambda_le_one hcop hL1 hα S 1 Jq)

/-! ## `Sh.envM`, `Sh.fixM` with the per-term remainders -/

/-- **`Sh.envM` at `ϑ = 1` with the per-term remainders** (fields 30–31; `lem:sharp-first` per
expanded term): `hdiffL/R` proved through `hterm_envL/R_paper` and DC2's
`diff_bound_of_coupled_loc`; `hzu` proved; `hr2L/R` from `RchSumPTEnvL/R`. -/
noncomputable def envMeansPT (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hL : RchSumPTEnvL hcop D hpair dec c₂) (hR : RchSumPTEnvR hcop D hpair dec c₂) :
    ThetaOne.EnvMeansTheta1 hcop D hpair where
  z := zBase D
  hz0 := zBase_nonneg D
  hzt := tendsto_zBase D
  r2L := r2PTEnvL hcop D hpair dec
  r2R := r2PTEnvR hcop D hpair dec
  hdiffL := by
    filter_upwards [hterm_envL_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.envIncL D L b)
        (fun L b => isPositiveRecord_envIncL D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.envIncL D L b)
        (fun L b => isPositiveRecord_envIncL D L b) dec)] with L hL
    intro C hC hind A hA hY Jq ω f
    have hK : 0 ≤ (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
        D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) :=
      mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
        (prod_nonneg fun b _ => by
          split_ifs
          · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
          · exact zero_le_one)
    exact DensityFibre.diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.envIncL D L) f _ hK (scaleU_nonneg' _ _ _ L)
      (envLambda_nonneg hcop L A Jq ω) (Rerr_mul_le_zBase D L) _
      (fun σ hσ0 j hj => hL C hC hind A hA hY Jq ω f σ hσ0 j hj)
  hdiffR := by
    filter_upwards [hterm_envR_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.envIncR D L b)
        (fun L b => isPositiveRecord_envIncR D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.envIncR D L b)
        (fun L b => isPositiveRecord_envIncR D L b) dec)] with L hL
    intro C hC hind A hA hY Jq ω f
    have hK : 0 ≤ (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
        D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) :=
      mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
        (prod_nonneg fun b _ => by
          split_ifs
          · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
          · exact zero_le_one)
    exact DensityFibre.diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.envIncR D L) f _ hK (scaleU_nonneg' _ _ _ L)
      (envLambda_nonneg hcop L A Jq ω) (Rerr_mul_le_zBase D L) _
      (fun σ hσ0 j hj => hL C hC hind A hA hY Jq ω f σ hσ0 j hj)
  hzu := Eventually.of_forall (scaleU_le_zBase D)
  c₂ := c₂
  hc₂ := hc₂
  hr2L := hr2PTEnvL_of_rch hcop D hpair dec hL
  hr2R := hr2PTEnvR_of_rch hcop D hpair dec hR

/-- **`Sh.fixM` at `ϑ = 1` with the per-term remainders** (fields 26–29): `hdiffL/R` proved
through `hterm_fixL/R_paper`; `hzu` proved; `hr2L/R` from `RchSumPTFixL/R`. -/
noncomputable def fixMeansPT (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) (c₂ : ℝ) (hc₂ : 0 ≤ c₂)
    (hL : RchSumPTFixL hcop D hpair dec c₂) (hR : RchSumPTFixR hcop D hpair dec c₂) :
    ThetaOne.FixMeansTheta1 hcop D hpair where
  z := zBase D
  hz0 := zBase_nonneg D
  hzt := tendsto_zBase D
  r2L := r2PTFixL hcop D hpair dec
  r2R := r2PTFixR hcop D hpair dec
  hdiffL := by
    filter_upwards [hterm_fixL_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec)] with L hL
    intro C hC hind A hA hY S hS Jq ω f
    have hK : 0 ≤ (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
        D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) :=
      mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
        (prod_nonneg fun b _ => by
          split_ifs
          · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
          · exact zero_le_one)
    exact DensityFibre.diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.wrapInc D L) f _ hK (scaleU_nonneg' _ _ _ L)
      (fixLambda_nonneg hcop L A S 0 Jq ω) (Rerr_mul_le_zBase D L) _
      (fun σ hσ0 j hj => hL C hC hind A hA hY S hS Jq ω f σ hσ0 j hj)
  hdiffR := by
    filter_upwards [hterm_fixR_paper hcop dcBlock₀ C1₀_pos C71₀_pos D hpair dec ha hpar hsel hne
      sigmaR_nonneg S1_sigmaR
      (hatomP_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec)
      (hatomM_base D (fun L b => TheoremCBlock.Structured.wrapInc D L b)
        (fun L b => isPositiveRecord_wrapInc D L b) dec)] with L hL
    intro C hC hind A hA hY S hS Jq ω f
    have hK : 0 ≤ (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
        D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) :=
      mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
        (prod_nonneg fun b _ => by
          split_ifs
          · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
          · exact zero_le_one)
    exact DensityFibre.diff_bound_of_coupled_loc D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.wrapInc D L) f _ hK (scaleU_nonneg' _ _ _ L)
      (fixLambda_nonneg hcop L A S 1 Jq ω) (Rerr_mul_le_zBase D L) _
      (fun σ hσ0 j hj => hL C hC hind A hA hY S hS Jq ω f σ hσ0 j hj)
  hzu := Eventually.of_forall (scaleU_le_zBase D)
  c₂ := c₂
  hc₂ := hc₂
  hr2L := hr2PTFixL_of_rch hcop D hpair dec hL
  hr2R := hr2PTFixR_of_rch hcop D hpair dec hR

end Sarkozy.SharpBase2
