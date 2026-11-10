module

public import Sarkozy.DensityChain2.Fields
public import Sarkozy.DensityFibre.FoldedMarginals

@[expose] public section

/-!
# At `ϑ = 1` the per-atom moment inputs `hatom` are proved (fields 28–31)

TH (7 November 2026). DC3's constructors of K2's fields 28–31 (`Sh.fixM.hmL/R`,
`Sh.envM.hmL/R`; `DensityChain2.envMeanBoundL/R_paperFinal`, `fixMeanBound_paperFinal`) take
two per-atom inputs, `_hmixQ` and `_hmixR`: unit mixed `L^{72/ϑ}` of the normalized increments
(`envIncL`, `envIncR`, `wrapInc`) and of the reserved records `Ñ₀ − μ = ∑ κu`
(`lem:density:packets`). At the upgraded `ϑ = 1014587/10⁶` these are genuine Part V obligations
(DC3 §3, `DensityChain2.not_mixedLp_theta_diag`).

Since 7 November 2026 the endgame runs at `ϑ = densityExponent = 1`. There `72/ϑ = 72`, and a
positive record (nonnegative, uniform one-slot marginals) has unit mixed `L^{72}` by Hölder
(`mixedLpBound_of_uniform_marginals`; DC2's `DensityFibre.mixedLp_one_of_positiveRecord`). The
increments and the reserved records are positive records (DC1's
`DensityChain.isPositiveRecord_envIncL/R`, `isPositiveRecord_wrapInc`,
`isPositiveRecord_recLaw`). So both inputs are **proved**, and:

* `envMeanBoundL_theta1`, `envMeanBoundR_theta1`, `fixMeanBound_theta1`: DC3's constructors with
  `_hmixQ`, `_hmixR` removed. What remains: `z_L ≥ u_L` eventually (`lem:scale-conditions`),
  the paper-data facts (parity `paperEP_parity`, nonempty blocks, `blockSel ≤ selPre`), and DC2's
  `r₂` summation `_hr2` (`lem:sharp-first`).
-/

namespace Sarkozy.ThetaOne

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps Sarkozy.DensityChain2
open Sarkozy.Param (Params)

/-- **Unit mixed `L^{72/ϑ}` of a positive record at `ϑ = 1`** (`lem:density:packets` is not
needed at the baseline). -/
theorem mixedLp_theta_of_positiveRecord {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    {κ : SlotMeasure X} (hκ : IsPositiveRecord κ) (hb : 0 < totalVariation (lawDensity κ)) :
    MixedLpBound (variationLaw (lawDensity κ) hb) (72 / densityExponent) 1 := by
  rw [densityExponent_eq_one]
  exact DensityFibre.mixedLp_one_of_positiveRecord hκ hb

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Field 30 (`Sh.envM.hmL`) at `ϑ = 1`**: DC3's `envMeanBoundL_paperFinal` with the per-atom
moment inputs `_hmixQ`, `_hmixR` proved. -/
theorem envMeanBoundL_theta1 :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (z : ℕ → ℝ)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) →
        (BlockAtom Bk PaperJt L → Bool) → ℝ)
    (_ha : 0 ≤ a)
    (_hz : ∀ᶠ L in atTop,
      scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L ≤ z L)
    (_hpar : ParityCondition D.S.ep) (_hne : ∀ β, ∃ i, blk i = β)
    (_hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂)
      (fun L => TheoremCBlock.Structured.envIncL D L)
      (fun L => TheoremCBlock.Structured.envPriceL D L)
      D.index.u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundL_paperFinal (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha hz hpar hne hsel c₂ hr2
  exact hmain D hpair z r2 ha hz hpar hne hsel c₂ hr2
    (Eventually.of_forall fun L b hb =>
      mixedLp_theta_of_positiveRecord (isPositiveRecord_envIncL D L b) hb)
    (Eventually.of_forall fun L b hb =>
      mixedLp_theta_of_positiveRecord (isPositiveRecord_recLaw D L b) hb)

/-- **Field 31 (`Sh.envM.hmR`) at `ϑ = 1`**: DC3's `envMeanBoundR_paperFinal` with the per-atom
moment inputs `_hmixQ`, `_hmixR` proved. -/
theorem envMeanBoundR_theta1 :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (z : ℕ → ℝ)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) →
        (BlockAtom Bk PaperJt L → Bool) → ℝ)
    (_ha : 0 ≤ a)
    (_hz : ∀ᶠ L in atTop,
      scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L ≤ z L)
    (_hpar : ParityCondition D.S.ep) (_hne : ∀ β, ∃ i, blk i = β)
    (_hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂)
      (fun L => TheoremCBlock.Structured.envIncR D L)
      (fun L => TheoremCBlock.Structured.envPriceR D L)
      D.index.w r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundR_paperFinal (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha hz hpar hne hsel c₂ hr2
  exact hmain D hpair z r2 ha hz hpar hne hsel c₂ hr2
    (Eventually.of_forall fun L b hb =>
      mixedLp_theta_of_positiveRecord (isPositiveRecord_envIncR D L b) hb)
    (Eventually.of_forall fun L b hb =>
      mixedLp_theta_of_positiveRecord (isPositiveRecord_recLaw D L b) hb)

/-- **Fields 28–29 (`Sh.fixM.hmL/R`) at `ϑ = 1`**: DC3's `fixMeanBound_paperFinal` with the
per-atom moment inputs `_hmixQ`, `_hmixR` proved. -/
theorem fixMeanBound_theta1 :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (z : ℕ → ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
    (r2 : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk PaperJt L → Bool) → ℝ)
    (_ha : 0 ≤ a)
    (_hz : ∀ᶠ L in atTop,
      scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L ≤ z L)
    (_hu : Injective u)
    (_hpar : ParityCondition D.S.ep) (_hne : ∀ β, ∃ i, blk i = β)
    (_hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)),
    FixMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * (D.CL.S + D.CL.A) + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂) u t r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := fixMeanBound_paperFinal (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z u t r2 ha hz hu hpar hne hsel c₂ hr2
  exact hmain D hpair z u t r2 ha hz hu hpar hne hsel c₂ hr2
    (Eventually.of_forall fun L b hb =>
      mixedLp_theta_of_positiveRecord (isPositiveRecord_wrapInc D L b) hb)
    (Eventually.of_forall fun L b hb =>
      mixedLp_theta_of_positiveRecord (isPositiveRecord_recLaw D L b) hb)

end Sarkozy.ThetaOne
