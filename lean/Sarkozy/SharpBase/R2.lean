module

public import Sarkozy.SharpBase.Hdiff

@[expose] public section

/-!
# The `r₂` summation `hr2` reduced to the summation of `rch` (`lem:sharp-first`)

SH2 (7 November 2026). With the paper's remainders `r₂ = ∑_{σ≠∅} rch(σ) + (R_err + z) K (Λ − 1)`
of `SharpBase.Hdiff`, the summation fields `hr2L/R` of `ThetaOne.FixMeansTheta1` and
`ThetaOne.EnvMeansTheta1` follow from the summation of `rch` alone:

* `expect_envLambda_le_one`: `E_ω Λ ≤ 1` for `Λ = envLambda` (B9's `env_localDensity_mean_le`
  at `p = 2ϑ/72`; the proof of `lem:envelope-energy`: "fix `𝒥` and the intervals, then average");
* `expect_fixLambda_le_one`: `E_ω Λ ≤ 1` for `Λ = fixLambda` (B9's `fix_localDensity_mean_le`, the
  factor `K^{2ϑ/72}` per active query cancels);
* `density_pos_cex`: `α > 0` at a counterexample;
* `RchSumEnvL/R`, `RchSumFixL/R`: the summation of the explicit `rch` (*open*, see below);
* `hr2EnvL/R_of_rch`, `hr2FixL/R_of_rch`: the fields `hr2L/R` from them, by DC2's
  `expect_r2_le` (the signed local-factor correction averages to at most `0`).

**What `RchSum*` asks** (`lem:sharp-first`, the summation of the error terms):
`E_𝒥 E_ω ∑_f ∑_{σ≠∅} rch(L, A, 𝒥, ω, f, σ) ≤ c₂ L^{-1/825} α` at every least counterexample, for
`rch = rchOptEnvL/R`, `rchOptFixL/R`. Per tag, `rch` is `SharpBase.rchOpt`, at most
`√(W M₊ R₋) + √(W M₋ R₊) + (R₊ + R₋)/2` (`SharpBase.rchOpt_le_cross`), where `W M_±` are the
folded main terms and `R_±` the weighted sums of DC3's remainders:
* the chain remainders `∏_E ‖Λ_𝔟‖ C_dc L^{-4/825} α` at the small pieces
  (`lem:record:density-dc`);
* the energies `|𝔈_±|` of the large pieces `q_E > N^τ` (`lem:record:density-lp`), and of the
  depth vectors with an unrevealed interval (zero query weight);
* the main term `bpieceG · K₀ P_±` of a fold whose partner's main price vanishes (DC3's
  finding 8).
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

theorem lambdaExp_nonneg : (0 : ℝ) ≤ 2 * densityExponent / 72 := by
  rw [densityExponent_eq_one]
  norm_num

theorem lambdaExp_le_one : 2 * densityExponent / 72 ≤ (1 : ℝ) := by
  rw [densityExponent_eq_one]
  norm_num

/-- **`E_ω Λ ≤ 1` for the unfolded local factor of `envC`** (B9's `env_localDensity_mean_le`). -/
theorem expect_envLambda_le_one {L : ℕ} (hL : 1 ≤ L) {A : Finset ℤ}
    (hA : A ⊆ Icc 1 ((blockScale * L : ℕ) : ℤ)) (hα : 0 < density (blockScale * L) A)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      (fun ω => envLambda hcop L A Jq ω) ≤ 1 :=
  env_localDensity_mean_le hcop hL A hA hα lambdaExp_nonneg lambdaExp_le_one Jq

/-- **`E_ω Λ ≤ 1` for the fixed-interval local factor of `fixC`** (B9's
`fix_localDensity_mean_le`; each active query carries `K^{-2ϑ/72}` in `fixLambda`). -/
theorem expect_fixLambda_le_one {L : ℕ} (hL : 1 ≤ L) {A : Finset ℤ}
    (hα : 0 < density (blockScale * L) A) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) :
    (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
      (fun ω => fixLambda hcop L A S t Jq ω) ≤ 1 := by
  set p : ℝ := 2 * densityExponent / 72 with hp
  have hk : 0 < (blockScale : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num [blockScale]) _
  have hfac : ∀ ω, fixLambda hcop L A S t Jq ω =
      (∏ e, if e ∈ S then (fixQueryLocalDensity hcop L A t (Jq e) (ω e) /
          density (blockScale * L) A) ^ p else 1) *
        ∏ e : E, (if e ∈ S then ((blockScale : ℝ) ^ p)⁻¹ else 1) := by
    intro ω
    unfold fixLambda
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun e _ => ?_
    split_ifs
    · rw [div_eq_mul_inv]
    · rw [mul_one]
  rw [FiniteLaw.expect_congr _ hfac, FiniteLaw.expect_mul_const]
  have hc : 0 ≤ ∏ e : E, (if e ∈ S then ((blockScale : ℝ) ^ p)⁻¹ else 1) :=
    prod_nonneg fun e _ => by
      split_ifs
      · exact (inv_pos.mpr hk).le
      · exact zero_le_one
  refine le_trans (mul_le_mul_of_nonneg_right
    (fix_localDensity_mean_le hcop hL A hα lambdaExp_nonneg lambdaExp_le_one S t Jq) hc)
    (le_of_eq ?_)
  rw [← prod_mul_distrib]
  refine prod_eq_one fun e _ => ?_
  split_ifs
  · exact mul_inv_cancel₀ hk.ne'
  · exact mul_one 1

omit [DecidableEq P] in
/-- `α > 0` at a counterexample (`Y(L, ∅) = 0`). -/
theorem density_pos_cex (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) {L : ℕ}
    (hL : 1 ≤ L) {A : Finset ℤ} {C : ℝ} (hC : 1 ≤ C)
    (hY : C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
      density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent <
        D.Y L A) : 0 < density (blockScale * L) A := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hlow0 : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
      density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  have hYpos := lt_of_le_of_lt hlow0 hY
  rcases Finset.eq_empty_or_nonempty A with hA0 | hA0
  · rw [hA0, dataY_empty] at hYpos
    exact absurd hYpos (lt_irrefl 0)
  · exact density_pos_of_nonempty (Nat.mul_pos (by norm_num [blockScale]) (by omega)) hA0

/-! ## The summation of `rch` (*open*) -/

/-- **The summation of the sharp-first remainders of `Sh.envM`, left** (`lem:sharp-first`, the
error terms; `lem:record:density-dc`, `lem:record:density-lp`): the explicit `rchOptEnvL`, summed
over `σ ≠ ∅` and `f`, averaged over `ω` and `𝒥`, is at most `c₂ L^{-1/825} α`. -/
def RchSumEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchOptEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summation of the sharp-first remainders of `Sh.envM`, right**: as `RchSumEnvL`, with
`rchOptEnvR`. -/
def RchSumEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchOptEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summation of the sharp-first remainders of `Sh.fixM`, left** (`lem:sharp-first`):
the explicit `rchOptFixL`, for every nonempty `𝒮`. -/
def RchSumFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchOptFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **The summation of the sharp-first remainders of `Sh.fixM`, right**: as `RchSumFixL`, with
`rchOptFixR`. -/
def RchSumFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (c₂ : ℝ) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) =>
          σ ≠ fun _ => none),
            rchOptFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-! ## `hr2` from the summation of `rch` -/

/-- **`Sh.envM.hr2L` for the paper's `r₂`** from `RchSumEnvL` (DC2's `expect_r2_le` with
`E_ω envLambda ≤ 1`). -/
theorem hr2EnvL_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumEnvL hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2EnvL hcop D hpair dec L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
        · exact zero_le_one))
    (fun ω => envLambda hcop L A Jq ω) (expect_envLambda_le_one hcop hL1 hA.1 hα Jq)

/-- **`Sh.envM.hr2R` for the paper's `r₂`** from `RchSumEnvR`. -/
theorem hr2EnvR_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumEnvR hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2EnvR hcop D hpair dec L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
        · exact zero_le_one))
    (fun ω => envLambda hcop L A Jq ω) (expect_envLambda_le_one hcop hL1 hA.1 hα Jq)

/-- **`Sh.fixM.hr2L` for the paper's `r₂`** from `RchSumFixL` (DC2's `expect_r2_le` with
`E_ω fixLambda ≤ 1`). -/
theorem hr2FixL_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumFixL hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2FixL hcop D hpair dec L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY S hS
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY S hS)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one))
    (fun ω => fixLambda hcop L A S 0 Jq ω) (expect_fixLambda_le_one hcop hL1 hα S 0 Jq)

/-- **`Sh.fixM.hr2R` for the paper's `r₂`** from `RchSumFixR`. -/
theorem hr2FixR_of_rch (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) {c₂ : ℝ}
    (hrch : RchSumFixR hcop D hpair dec c₂) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2FixR hcop D hpair dec L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A) := by
  filter_upwards [hrch, eventually_ge_atTop 1] with L hL hL1
  intro C hC hk A hA hY S hS
  refine le_trans (FiniteLaw.expect_mono _ fun Jq => ?_) (hL C hC hk A hA hY S hS)
  have hα := density_pos_cex D hL1 hC hY
  have hY0 := Y_nonneg_of_cex D hC hY
  exact DensityFibre.expect_r2_le _
    (fun ω f => ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ)
    (add_nonneg (Rerr_nonneg D) (zBase_nonneg D L))
    (fun f => fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))
    (fun f => mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) hY0)
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one))
    (fun ω => fixLambda hcop L A S 1 Jq ω) (expect_fixLambda_le_one hcop hL1 hα S 1 Jq)

end Sarkozy.SharpBase
