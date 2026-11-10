module

public import Sarkozy.ThetaOne.Inputs
public import Sarkozy.SharpBase.HfoldOpt
public import Sarkozy.DensityChain.Sanity

@[expose] public section

/-!
# The four sharp-first differences `hdiff` and the scale condition `hzu` at `ϑ = 1`

SH2 (7 November 2026). The groups `Sh.fixM`, `Sh.envM` of `main_goal_theta1k`
(`ThetaOne.FixMeansTheta1`, `ThetaOne.EnvMeansTheta1`) carry, per side, the sharp-first
difference `hdiff` (`lem:sharp-first` for the bracket of `lem:bracket-energy`) with a free
remainder `r₂` and a free scale `z`, the scale condition `hzu` (`u_L ≤ z_L`,
`lem:scale-conditions`) and the `r₂` summation `hr2`.

Here `z` and `r₂` are fixed to the paper's values:

* `zBase D L = (1 + R_err) u_L`: `z ≥ 0`, `z → 0` (`lem:scale-conditions`, `u_L → 0`),
  `u_L ≤ z_L` (so `hzu` holds for every `L`) and `R_err u_L ≤ z_L` (DC2's `hz`);
* `C1₀`, `C71₀`: the constants of DC1's `density_dc_block'` at `ε₀ = 1/100`
  (`lem:record:density-dc`), with the dc exponent `σ = sigmaR = 4/825` ((S1): `S1_sigmaR`).
  The summation of the cross terms `√(M R)` halves the exponent, and `hr2` asks for `1/825`;
* `hatom` at `ϑ = 1` for DC2's folded laws: every non-`μ` folded piece is a positive record
  (DC2's `bpieceLp/Lm_positiveRecord`), so it has unit mixed `L^{72}`
  (`ThetaOne.mixedLp_theta_of_positiveRecord`). This removes the inputs `hatomP`, `hatomM` of
  DC3's `hfold_*_paper` and of `SharpBase.hfoldOpt_*_paper` (`lem:density:packets` is not
  needed at the baseline);
* `r2EnvL/R`, `r2FixL/R`: DC2's remainder `r₂ = ∑_{σ≠∅} rch(σ) + (R_err + z) K (Λ − 1)` with
  the re-optimized explicit `rch = rchOptEnvL/R`, `rchOptFixL/R` (`SharpBase.HfoldOpt`) and DC3's
  local factors `Λ = envLambda`, `fixLambda`.

The four `hdiff` fields at these `z`, `r₂` and `hzu` are proved in `SharpBase.Means` (DC2's
`env/fixHdiffL/R_of_folded` with `SharpBase.hfoldOpt_env/fixL/R_paper`). The same `r₂` must be
used in `hr2` (DC2's finding 1); `SharpBase.R2` reduces `hr2` for these `r₂` to the summation of
`rch` alone.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.SharpBase

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps Sarkozy.DensityChain2
open Sarkozy.Param (Params)

/-! ## The constants of `lem:record:density-dc` -/

/-- DC1's `density_dc_block'` at `ε₀ = 1/100` (`lem:record:density-dc` on the block atoms). -/
theorem dc_exists : ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧ DCBlockProp (1 / 100) C1 C71 :=
  density_dc_block' (1 / 100) (by norm_num)

/-- The constant `C₁` of `lem:record:density-dc` at `ε₀ = 1/100`. -/
noncomputable def C1₀ : ℝ := dc_exists.choose

/-- The constant `C₇₁` of `lem:record:density-dc` at `ε₀ = 1/100`. -/
noncomputable def C71₀ : ℝ := dc_exists.choose_spec.choose

theorem C1₀_pos : 0 < C1₀ := dc_exists.choose_spec.choose_spec.1

theorem C71₀_pos : 0 < C71₀ := dc_exists.choose_spec.choose_spec.2.1

theorem dcBlock₀ : DCBlockProp (1 / 100) C1₀ C71₀ := dc_exists.choose_spec.choose_spec.2.2

/-- **The dc exponent of the sharp-first remainders**: `σ = 4/825`, four times the exponent
`1/825` of the summation fields. The paper's cross terms `√(M R)` cost a halving of the dc
exponent (Cauchy–Schwarz over `ω`), so the remainders are taken at a larger `σ`; `σ` is free
below `γ/40 − ε₀/20` (DC2 §6). -/
noncomputable def sigmaR : ℝ := 4 * Sarkozy.cancellationDecay

theorem sigmaR_nonneg : (0 : ℝ) ≤ sigmaR := by
  unfold sigmaR Sarkozy.cancellationDecay
  norm_num

/-- (S1) at `ε₀ = 1/100`, `σ = 4/825` (`γ = 255/1024`). -/
theorem S1_sigmaR : (1 / 100 : ℝ) / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -sigmaR := by
  unfold sigmaR Sarkozy.AnalyticStage.γ Sarkozy.cancellationDecay
  norm_num

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-! ## The scale `z` (`lem:scale-conditions`) -/

/-- **The scale of the sharp-first fields**: `z_L = (1 + R_err) u_L`, with `u_L` the scale term
of `lem:scale-conditions` at `M₀ = modulus`, `Q_cl = Q_cl⁰` (DC3's `ε_L`). -/
noncomputable def zBase (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ) :
    ℝ :=
  (1 + D.GB.Rerr) * scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L

omit [DecidableEq P] in
theorem zBase_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ) :
    0 ≤ zBase D L :=
  mul_nonneg (by linarith [Rerr_nonneg D]) (scaleU_nonneg' _ _ _ L)

omit [DecidableEq P] in
/-- **`hzu` at every scale**: `u_L ≤ z_L` (`lem:scale-conditions`). -/
theorem scaleU_le_zBase (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ) :
    scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L ≤ zBase D L := by
  unfold zBase
  have := mul_nonneg (Rerr_nonneg D) (scaleU_nonneg' blockScale (modulus pr h)
    (cliqueConstant m₀ D.S.ep) L)
  nlinarith

omit [DecidableEq P] in
/-- DC2's condition `R_err ε_L ≤ z_L` at `ε_L = u_L`. -/
theorem Rerr_mul_le_zBase (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ) :
    D.GB.Rerr * scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L ≤
      zBase D L := by
  unfold zBase
  have := scaleU_nonneg' blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) L
  nlinarith

omit [DecidableEq P] in
/-- `z_L → 0` (`lem:scale-conditions`: `u_L → 0` at `τ = 1/201`). -/
theorem tendsto_zBase (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) :
    Tendsto (zBase D) atTop (𝓝 0) := by
  have h1 : (1 : ℕ) ≤ blockScale := by norm_num [blockScale]
  have := (tendsto_scaleU_stage (M0 := modulus pr h) (Qcl := cliqueConstant m₀ D.S.ep) h1).const_mul
    (1 + D.GB.Rerr)
  rw [mul_zero] at this
  exact this

/-! ## `hatom` of the folded laws at `ϑ = 1` -/

omit [DecidableEq P] in
/-- **Unit mixed `L^{72/ϑ}` of the plus folded laws at `ϑ = 1`**, for positive-record increments
`Q` (the input `hatomP` of `hfoldOpt_*_paper`; `lem:density:packets` is not needed). -/
theorem hatomP_base (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (Q : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQ : ∀ L b, IsPositiveRecord (Q L b)) (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) :
    ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L (Q L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1 :=
  fun L j b x hx hb => ThetaOne.mixedLp_theta_of_positiveRecord
    (DensityFibre.bpieceLp_positiveRecord D L (Q L) (dec L) (hQ L) j b x hx) hb

omit [DecidableEq P] in
/-- **Unit mixed `L^{72/ϑ}` of the minus folded laws at `ϑ = 1`** (the input `hatomM`). -/
theorem hatomM_base (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (Q : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b)
    (hQ : ∀ L b, IsPositiveRecord (Q L b)) (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) :
    ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L (Q L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1 :=
  fun L j b x hx hb => ThetaOne.mixedLp_theta_of_positiveRecord
    (DensityFibre.bpieceLm_positiveRecord D L (Q L) (dec L) (hQ L) j b x hx) hb

/-! ## The paper's remainders `r₂` -/

/-- **The remainder `r₂` of `Sh.envM.hdiffL`** (field 30): DC2's
`∑_{σ≠∅} rch(σ) + (R_err + z) K (Λ − 1)` with `rch = rchOptEnvL` (at `C₁₀`, `C₇₁₀`,
`σ = sigmaR`), `Λ = envLambda`, `z = zBase` (`lem:sharp-first`). -/
noncomputable def r2EnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptEnvL hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) *
      (envLambda hcop L A Jq ω - 1)

/-- **The remainder `r₂` of `Sh.envM.hdiffR`** (field 31), as `r2EnvL` with `rchOptEnvR`. -/
noncomputable def r2EnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptEnvR hcop D hpair dec C1₀ C71₀ sigmaR L A Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) *
      (envLambda hcop L A Jq ω - 1)

/-- **The remainder `r₂` of `Sh.fixM.hdiffL`**: DC2's `r₂` with `rchOptFixL`,
`Λ = fixLambda` at `t = 0`. -/
noncomputable def r2FixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptFixL hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
      (fixLambda hcop L A S 0 Jq ω - 1)

/-- **The remainder `r₂` of `Sh.fixM.hdiffR`**: DC2's `r₂` with `rchOptFixR`,
`Λ = fixLambda` at `t = 1`. -/
noncomputable def r2FixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (L : ℕ) (A : Finset ℤ) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (f : BlockAtom Bk PaperJt L → Bool) : ℝ :=
  (∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      rchOptFixR hcop D hpair dec C1₀ C71₀ sigmaR L A S Jq ω f σ) +
    (D.GB.Rerr + zBase D L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
      (fixLambda hcop L A S 1 Jq ω - 1)

end Sarkozy.SharpBase
