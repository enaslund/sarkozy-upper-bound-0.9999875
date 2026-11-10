module

public import Sarkozy.ThetaOne.Hatom
public import Sarkozy.MainFinal2.Bundles

@[expose] public section

/-!
# B9's mean-bound inputs of `fixC`, `envC` at `ϑ = 1` (fields 28–31 reduced)

TH (7 November 2026). `MainFinal2.FixMeansInputs` and `EnvMeansInputs` (the `Sh.fixM`, `Sh.envM`
groups of the main statement) carry, per side, the sharp-first difference `hdiff` and the mean
bound `hm` (`FixMeanBound`, `EnvMeanBound`: K2's fields 28–31). At `ϑ = 1` DC3's constructors
of `hm`, with the per-atom moment inputs proved (`ThetaOne.Hatom`), leave only:
* `hzu`: `u_L ≤ z_L` eventually (`lem:scale-conditions`);
* the parity condition, nonempty blocks (`def:construction`(b)) and `blockSel ≤ selPre`:
  arguments of the conversions, proved for the paper's data
  (`DensityChain2.parity_blockPaperStandingAt`, `hsel_blockPaperStandingAt`,
  `ThetaOne.paperAtomMap_paperBlockOf_surjective`; `ThetaOne.SharpPartsBase.toSharpParts2` and
  `MainFinalObligationsT1.toGP` supply them);
* `c₂`, `hr2L`, `hr2R`: DC2's summation of the sharp-first remainders `r₂` (`lem:sharp-first`),
  with the **same** `r₂` as in `hdiff` (DC2's finding 1).

* **`FixMeansTheta1`**, **`EnvMeansTheta1`**: these inputs, with `z`, `r2L`, `r2R`, `hdiffL`,
  `hdiffR` verbatim from B9's bundles, on the paper's tail `p = paperTail`;
* **`toFixMeansInputs`**, **`toEnvMeansInputs`**: B9's bundles, with `c` the constant of DC3's
  constructors plus `c₂`, and `hmL`, `hmR` proved.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ThetaOne

open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps Sarkozy.DensityChain2
open Sarkozy.MainFinal2 (FixMeansInputs EnvMeansInputs)
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

theorem remainder_mono {c c' : ℝ} (hcc : c ≤ c') (L : ℕ) (A : Finset ℤ) :
    remainder c L A ≤ remainder c' L A := by
  unfold remainder
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcc (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (density_nonneg _ _)

theorem envMeanBound_mono {D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j)}
    {z : ℕ → ℝ} {c c' : ℝ} (hcc : c ≤ c')
    {Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk paperTail L b}
    {price : ∀ L, BlockAtom Bk PaperJt L → ℝ} {u : E → reservedCut.Half}
    {r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) →
        (BlockAtom Bk PaperJt L → Bool) → ℝ}
    (hm : EnvMeanBound hcop D hpair z c Qb price u r2) :
    EnvMeanBound hcop D hpair z c' Qb price u r2 := by
  unfold EnvMeanBound at hm ⊢
  filter_upwards [hm] with L hL
  intro C hC hk A hA hY
  obtain ⟨ρ, h1, h2⟩ := hL C hC hk A hA hY
  exact ⟨ρ, h1, h2.trans (remainder_mono hcc L A)⟩

/-- **B9's inputs of `fixC` at `ϑ = 1`, with the mean bounds reduced** (fields 28–29;
`lem:envelope-energy`, `lem:twointerval`(ii), `lem:bracket-energy`). The fields `z`, `r2L`, `r2R`,
`hdiffL`, `hdiffR` are those of `MainFinal2.FixMeansInputs`; `hmL`, `hmR` are replaced by the
inputs of DC3's `fixMeanBound_paperFinal` that `ϑ = 1` leaves (`fixMeanBound_theta1`). -/
structure FixMeansTheta1 (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  r2L : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk PaperJt L → Bool) → ℝ
  r2R : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk PaperJt L → Bool) → ℝ
  hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
    (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
    (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
    r2L L A S Jq ω f)
  hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
    (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
    (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
    r2R L A S Jq ω f)
  /-- `u_L ≤ z_L` eventually (`lem:scale-conditions`). *Open*. -/
  hzu : ∀ᶠ L in atTop,
    scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L ≤ z L
  /-- The constant of the `r₂` summation. -/
  c₂ : ℝ
  hc₂ : 0 ≤ c₂
  /-- **The summation of the sharp-first remainders, left** (`lem:sharp-first`). *Open*. -/
  hr2L : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, r2L L A S Jq ω f)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)
  /-- **The summation of the sharp-first remainders, right** (`lem:sharp-first`). *Open*. -/
  hr2R : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, r2R L A S Jq ω f)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

/-- **B9's inputs of `envC` at `ϑ = 1`, with the mean bounds reduced** (fields 30–31;
`lem:envelope-energy`, `lem:hyb:moment`, `lem:bracket-energy`). The fields `z`, `r2L`, `r2R`,
`hdiffL`, `hdiffR` are those of `MainFinal2.EnvMeansInputs`; `hmL`, `hmR` are replaced by the
inputs of DC3's `envMeanBoundL/R_paperFinal` that `ϑ = 1` leaves (`envMeanBoundL/R_theta1`). -/
structure EnvMeansTheta1 (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  r2L : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk PaperJt L → Bool) → ℝ
  r2R : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk PaperJt L → Bool) → ℝ
  hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
    (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N₀ L b))
    (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) +
    r2L L A Jq ω f)
  hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
    (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N₀ L b))
    (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) +
    r2R L A Jq ω f)
  /-- `u_L ≤ z_L` eventually (`lem:scale-conditions`). *Open*. -/
  hzu : ∀ᶠ L in atTop,
    scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L ≤ z L
  /-- The constant of the `r₂` summation. -/
  c₂ : ℝ
  hc₂ : 0 ≤ c₂
  /-- **The summation of the sharp-first remainders, left** (`lem:sharp-first`). *Open*. -/
  hr2L : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, r2L L A Jq ω f)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)
  /-- **The summation of the sharp-first remainders, right** (`lem:sharp-first`). *Open*. -/
  hr2R : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, r2R L A Jq ω f)) ≤
      c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A)

variable {hcop}

omit [DecidableEq P] in
theorem meanConst_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {C1 C71 Clp T : ℝ} (hC1 : 0 < C1) (hC71 : 0 < C71) (hClp : 0 < Clp) :
    0 ≤ dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * Real.exp T +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) := by
  have h1 := dcConstant_nonneg (C' := (prefixConductor (m₀ := m₀) blk D.R.P5 : ℝ))
    (γ := Sarkozy.AnalyticStage.γ) (X := (Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ))
    (Nat.cast_nonneg _) (Nat.cast_nonneg (modulus pr h)) hC1.le hC71.le
  have h2 : 0 ≤ lpConst m₀ blk (modulus pr h) Clp := by
    unfold lpConst
    have := hClp.le
    positivity
  exact add_nonneg (mul_nonneg h1 (Real.exp_nonneg T))
    (mul_nonneg h2 (Real.exp_nonneg (2 * D.SM.bound)))

/-- **B9's `fixC` inputs from the reduced ones at `ϑ = 1`**: `c` is the constant of DC3's
`fixMeanBound_paperFinal` plus `c₂`, and `hmL`, `hmR` are `fixMeanBound_theta1` at
`(u, t) = (Q.u, 0)` and `(Q.w, 1)`. -/
noncomputable def FixMeansTheta1.toFixMeansInputs
    {D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j)}
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep) (hne : ∀ β, ∃ i, blk i = β)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (M : FixMeansTheta1 hcop D hpair) : FixMeansInputs hcop D hpair := by
  let H := fixMeanBound_theta1 (a := a) (m₀ := m₀) (blk := blk) (pr := pr) (h := h) (E := E) hcop
  let C1 := H.choose
  let C71 := H.choose_spec.choose
  let Clp := H.choose_spec.choose_spec.choose
  have hs := H.choose_spec.choose_spec.choose_spec
  exact
    { z := M.z
      hz0 := M.hz0
      hzt := M.hzt
      c := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
            (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            Real.exp (2 * (D.CL.S + D.CL.A) + D.GB.U₀) +
          lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + M.c₂
      hc := add_nonneg (meanConst_nonneg D hs.1 hs.2.1 hs.2.2.1) M.hc₂
      r2L := M.r2L
      r2R := M.r2R
      hdiffL := M.hdiffL
      hdiffR := M.hdiffR
      hmL := hs.2.2.2 D hpair M.z D.S.Q.u 0 M.r2L ha M.hzu D.S.Q.hu hpar hne hsel M.c₂
        M.hr2L
      hmR := hs.2.2.2 D hpair M.z D.S.Q.w 1 M.r2R ha M.hzu D.S.Q.hw hpar hne hsel M.c₂
        M.hr2R }

/-- **B9's `envC` inputs from the reduced ones at `ϑ = 1`**: `c` is the sum of the constants of
DC3's `envMeanBoundL/R_paperFinal` plus `c₂`; `hmL`, `hmR` are `envMeanBoundL/R_theta1`, each
raised to the common constant (`envMeanBound_mono`). -/
noncomputable def EnvMeansTheta1.toEnvMeansInputs
    {D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j)}
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep) (hne : ∀ β, ∃ i, blk i = β)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (M : EnvMeansTheta1 hcop D hpair) : EnvMeansInputs hcop D hpair := by
  let HL := envMeanBoundL_theta1 (a := a) (m₀ := m₀) (blk := blk) (pr := pr) (h := h) (E := E)
    hcop
  let HR := envMeanBoundR_theta1 (a := a) (m₀ := m₀) (blk := blk) (pr := pr) (h := h) (E := E)
    hcop
  have hL := HL.choose_spec.choose_spec.choose_spec
  have hR := HR.choose_spec.choose_spec.choose_spec
  let KL := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
      (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) HL.choose
      HL.choose_spec.choose * Real.exp (2 * D.ME.T + D.GB.U₀) +
    lpConst m₀ blk (modulus pr h) HL.choose_spec.choose_spec.choose * Real.exp (2 * D.SM.bound)
  let KR := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
      (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) HR.choose
      HR.choose_spec.choose * Real.exp (2 * D.ME.T + D.GB.U₀) +
    lpConst m₀ blk (modulus pr h) HR.choose_spec.choose_spec.choose * Real.exp (2 * D.SM.bound)
  have hKL : 0 ≤ KL := meanConst_nonneg D hL.1 hL.2.1 hL.2.2.1
  have hKR : 0 ≤ KR := meanConst_nonneg D hR.1 hR.2.1 hR.2.2.1
  exact
    { z := M.z
      hz0 := M.hz0
      hzt := M.hzt
      c := KL + KR + M.c₂
      hc := add_nonneg (add_nonneg hKL hKR) M.hc₂
      r2L := M.r2L
      r2R := M.r2R
      hdiffL := M.hdiffL
      hdiffR := M.hdiffR
      hmL := envMeanBound_mono hcop (by linarith)
        (hL.2.2.2 D hpair M.z M.r2L ha M.hzu hpar hne hsel M.c₂ M.hr2L)
      hmR := envMeanBound_mono hcop (by linarith)
        (hR.2.2.2 D hpair M.z M.r2R ha M.hzu hpar hne hsel M.c₂ M.hr2R) }

end Sarkozy.ThetaOne
