module

public import Sarkozy.DensityChain2.Summability
public import Sarkozy.EnvelopeInputs.GroupFacts

@[expose] public section

/-!
# Fields 28–31 on the paper's tail: restoration, the factorization and `_hselF` discharged

DC1's `envMeanBoundL/R_paper_restoration` and `fixMeanBound_of_restoration` (`DensityChain`)
reduce K2's fields 30–31 (`Sh.envM.hmL/R`) and 28–29 (`Sh.fixM.hmL/R`) to per-term restoration and
`hatom`, DC2's `r₂` summation, and frame facts. Here, for comparison data on the paper's tail
`p = paperTail` (`𝒯_N`), these are discharged:

* restoration (`lem:record:fibre-scale`(c)), by `envHrest_paper`, `fixHrest_paper`;
* `D_𝔟 = q_𝔟 c_𝔟` with `q_𝔟` squarefree, `c_𝔟` a nonzero square coprime to `q_𝔟`, `∏ c_𝔟 ≤ Q_cl`,
  `D_𝔟 ≥ 2` (`def:record:structured-energy`(a)), by `Factorization`, from the **parity condition**
  `e_p ∈ {1} ∪ 2ℕ` (a hypothesis here; `paperEP_parity` for the paper), nonempty blocks, and
  `Q_cl⁰ = ∏_{e_p ≠ 1} p^{e_p} ≤ Q_cl`;
* `_hselF` (`sq(D_𝔟)^a ≤ sel_𝔟`), by `hselF_of_parity`, given `blockSel ≤ selPre` (equality for
  the paper's selection factors);
* `hatom` per term, by `hatom_of_atoms`, from per-atom bounds for the increments and the reserved
  records (`lem:density:packets`);
* for `fixC`: the wrapping price rows `‖wrapInc‖ sq^a ≤ wrapPrice` (`wrapInc_price_le`) and
  `∑_𝔟 wrapPrice ≤ S + A` (`wrapPrice_total`, from `CL.S_total`, `CL.A_total`).

**What remains** (all labelled): the scale conditions `_hsc` and `u_L ≤ z_L`
(`lem:scale-conditions`),
`M₀^{index} ∣ M₀` (`def:cp0`(d)), the `q^{1/4}`-weighted price summability `_hW` (`def:cp8`(c),
with `q_𝔟 = atomQ`), (S1), (S4), DC2's `r₂` summation `_hr2` (`lem:sharp-first`), and the per-atom
unit mixed `L^{72/ϑ}` bounds (`lem:density:packets`) of the increments and the reserved records.
-/

namespace Sarkozy.DensityChain2

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor Sarkozy.CancellationSteps
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Field 30 (`Sh.envM.hmL`) on the paper's tail**: DC1's
`envMeanBoundL_paper_restoration` with restoration, the factorization, `_hselF` and the per-term
`hatom` discharged (see the module docstring for what remains). -/
theorem envMeanBoundL_blocks (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (z : ℕ → ℝ)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) →
        (BlockAtom Bk PaperJt L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hMod : modulus pr h ∣ M0)
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hpar : ParityCondition D.S.ep) (_hne : ∀ β, ∃ i, blk i = β)
    (_hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (_hQcl : cliqueConstant m₀ D.S.ep ≤ Qcl)
    {W : ℝ}
    (_hW : ∀ L, ∑ b, ((atomQ blk paperTail D.S.pp D.S.ep L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
      (2 * TheoremCBlock.Structured.envPriceL D L b + D.GB.uprice L b) ≤ W)
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncL D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂)
      (fun L => TheoremCBlock.Structured.envIncL D L)
      (fun L => TheoremCBlock.Structured.envPriceL D L)
      D.index.u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundL_paper_restoration (a := a)
    (m₀ := m₀) (blk := blk) (p := paperTail) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hMod hz hpar hne hsel hQcl W hW σ hσc hS1 hS4
    c₂ hr2 hmixQ hmixR
  have h0 := prefix_pairwise (hpair 0)
  refine hmain D hpair z r2 ha hM0 hsc hMod hz (hselF_of_parity D h0 hpar hsel)
    (atomQ blk paperTail D.S.pp D.S.ep) (atomC m₀ blk D.S.ep)
    (crtModuli_eq_atomQ_mul_atomC D.S.m₀_eq)
    (squarefree_atomQ D.S.m₀_eq D.S.pp_prime D.S.ep_pos h0 D.S.p_prime)
    (isSquare_atomC D.S.m₀_eq hpar) (atomC_ne_zero D.S.ep)
    (coprime_atomQ_atomC D.S.m₀_eq D.S.ep_pos h0)
    (fun L => (prod_atomC_eq D.S.ep L).trans_le hQcl)
    (two_le_crtModuli D.S.m₀_eq D.S.pp_prime D.S.ep_pos hne D.S.p_prime) hW hσc hS1 hS4 c₂ hr2 ?_
  filter_upwards [hmixQ, hmixR] with L hQ hR
  intro C hC hk A hA hY Jq hJq f g hg
  exact ⟨envHrest_paper hcop D hpair D.index.u L Jq f g, hatom_of_atoms D L _ hQ hR f g⟩

/-- **Field 31 (`Sh.envM.hmR`) on the paper's tail**: DC1's
`envMeanBoundR_paper_restoration` with restoration, the factorization, `_hselF` and the per-term
`hatom` discharged (see the module docstring for what remains). -/
theorem envMeanBoundR_blocks (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (z : ℕ → ℝ)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) →
        (BlockAtom Bk PaperJt L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hMod : modulus pr h ∣ M0)
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hpar : ParityCondition D.S.ep) (_hne : ∀ β, ∃ i, blk i = β)
    (_hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (_hQcl : cliqueConstant m₀ D.S.ep ≤ Qcl)
    {W : ℝ}
    (_hW : ∀ L, ∑ b, ((atomQ blk paperTail D.S.pp D.S.ep L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
      (2 * TheoremCBlock.Structured.envPriceR D L b + D.GB.uprice L b) ≤ W)
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncR D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂)
      (fun L => TheoremCBlock.Structured.envIncR D L)
      (fun L => TheoremCBlock.Structured.envPriceR D L)
      D.index.w r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundR_paper_restoration (a := a)
    (m₀ := m₀) (blk := blk) (p := paperTail) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hMod hz hpar hne hsel hQcl W hW σ hσc hS1 hS4
    c₂ hr2 hmixQ hmixR
  have h0 := prefix_pairwise (hpair 0)
  refine hmain D hpair z r2 ha hM0 hsc hMod hz (hselF_of_parity D h0 hpar hsel)
    (atomQ blk paperTail D.S.pp D.S.ep) (atomC m₀ blk D.S.ep)
    (crtModuli_eq_atomQ_mul_atomC D.S.m₀_eq)
    (squarefree_atomQ D.S.m₀_eq D.S.pp_prime D.S.ep_pos h0 D.S.p_prime)
    (isSquare_atomC D.S.m₀_eq hpar) (atomC_ne_zero D.S.ep)
    (coprime_atomQ_atomC D.S.m₀_eq D.S.ep_pos h0)
    (fun L => (prod_atomC_eq D.S.ep L).trans_le hQcl)
    (two_le_crtModuli D.S.m₀_eq D.S.pp_prime D.S.ep_pos hne D.S.p_prime) hW hσc hS1 hS4 c₂ hr2 ?_
  filter_upwards [hmixQ, hmixR] with L hQ hR
  intro C hC hk A hA hY Jq hJq f g hg
  exact ⟨envHrest_paper hcop D hpair D.index.w L Jq f g, hatom_of_atoms D L _ hQ hR f g⟩

/-- **Fields 28–29 (`Sh.fixM.hmL/R`) on the paper's tail**: DC1's `fixMeanBound_of_restoration`
with restoration, the factorization, `_hselF`, the per-term `hatom`, the wrapping price rows and
the price totals (`T_Q = S + A`, `U₀`) discharged. DC1's integration note: `u = D.S.Q.u` or
`D.S.Q.w`, `t = 0` or `1`. -/
theorem fixMeanBound_blocks (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (z : ℕ → ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
    (r2 : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk PaperJt L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hMod : modulus pr h ∣ M0)
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hu : Injective u)
    (_hpar : ParityCondition D.S.ep) (_hne : ∀ β, ∃ i, blk i = β)
    (_hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (_hQcl : cliqueConstant m₀ D.S.ep ≤ Qcl)
    {W : ℝ}
    (_hW : ∀ L, ∑ b, ((atomQ blk paperTail D.S.pp D.S.ep L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
      (2 * TheoremCBlock.Structured.wrapPrice D L b + D.GB.uprice L b) ≤ W)
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.wrapInc D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    FixMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * (D.CL.S + D.CL.A) + D.GB.U₀) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂) u t r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := fixMeanBound_of_restoration (a := a)
    (m₀ := m₀) (blk := blk) (p := paperTail) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z u t r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hMod hz hu hpar hne hsel hQcl W hW σ hσc
    hS1 hS4 c₂ hr2 hmixQ hmixR
  have h0 := prefix_pairwise (hpair 0)
  have hselF := hselF_of_parity D h0 hpar hsel
  refine hmain D hpair z u t r2 ha hM0 hsc D.S.p_prime D.S.p_inj hMod (hcopM_of_data D) hz hu
    (fun L b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L b => recLaw_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (wrapPrice_total D) (fun L => D.GB.U₀_total L)
    (atomQ blk paperTail D.S.pp D.S.ep) (atomC m₀ blk D.S.ep)
    (crtModuli_eq_atomQ_mul_atomC D.S.m₀_eq)
    (squarefree_atomQ D.S.m₀_eq D.S.pp_prime D.S.ep_pos h0 D.S.p_prime)
    (isSquare_atomC D.S.m₀_eq hpar) (atomC_ne_zero D.S.ep)
    (coprime_atomQ_atomC D.S.m₀_eq D.S.ep_pos h0)
    (fun L => (prod_atomC_eq D.S.ep L).trans_le hQcl)
    (two_le_crtModuli D.S.m₀_eq D.S.pp_prime D.S.ep_pos hne D.S.p_prime) hW hσc hS1 hS4 c₂ hr2 ?_
  filter_upwards [hmixQ, hmixR] with L hQ hR
  intro C hC hk A hA hY S hS Jq f g hg
  exact ⟨fixHrest_paper hcop D hpair u L S t Jq f g, hatom_of_atoms D L _ hQ hR f g⟩

/-- **`envMeanBoundL_blocks` with the frame facts discharged**: `M₀ = modulus pr h`
(so `M₀^{index} ∣ M₀`),
`Q_cl = Q_cl⁰ = ∏_{e_p ≠ 1} p^{e_p}`, the scale conditions by `eventually_scaleConditions`
(`lem:scale-conditions`), and `_hW` from (CP8)(c) (`hW_envL_of_summable`, `W = 2 · bound`). -/
theorem envMeanBoundL_final (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
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
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncL D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂)
      (fun L => TheoremCBlock.Structured.envIncL D L)
      (fun L => TheoremCBlock.Structured.envPriceL D L)
      D.index.u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundL_blocks (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha hz hpar hne hsel σ hσc hS1 hS4 c₂ hr2 hmixQ hmixR
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  exact hmain D hpair z r2 ha (M0 := modulus pr h) (Qpre := 1) (N0 := 0) (N0' := 0) hM0
    (eventually_scaleConditions _ _ _ _ _ _ (by norm_num [blockScale]) hM0 hQ1) dvd_rfl hz hpar hne
    hsel le_rfl (hW_envL_of_summable D) hσc hS1 hS4 c₂ hr2 hmixQ hmixR

/-- **`envMeanBoundR_blocks` with the frame facts discharged**: `M₀ = modulus pr h`
(so `M₀^{index} ∣ M₀`),
`Q_cl = Q_cl⁰ = ∏_{e_p ≠ 1} p^{e_p}`, the scale conditions by `eventually_scaleConditions`
(`lem:scale-conditions`), and `_hW` from (CP8)(c) (`hW_envR_of_summable`, `W = 2 · bound`). -/
theorem envMeanBoundR_final (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
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
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncR D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂)
      (fun L => TheoremCBlock.Structured.envIncR D L)
      (fun L => TheoremCBlock.Structured.envPriceR D L)
      D.index.w r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundR_blocks (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha hz hpar hne hsel σ hσc hS1 hS4 c₂ hr2 hmixQ hmixR
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  exact hmain D hpair z r2 ha (M0 := modulus pr h) (Qpre := 1) (N0 := 0) (N0' := 0) hM0
    (eventually_scaleConditions _ _ _ _ _ _ (by norm_num [blockScale]) hM0 hQ1) dvd_rfl hz hpar hne
    hsel le_rfl (hW_envR_of_summable D) hσc hS1 hS4 c₂ hr2 hmixQ hmixR

/-- **`fixMeanBound_blocks` with the frame facts discharged**: `M₀ = modulus pr h`
(so `M₀^{index} ∣ M₀`),
`Q_cl = Q_cl⁰ = ∏_{e_p ≠ 1} p^{e_p}`, the scale conditions by `eventually_scaleConditions`
(`lem:scale-conditions`), and `_hW` from (CP8)(c) (`hW_fix_of_summable`, `W = 2 · bound`). -/
theorem fixMeanBound_final (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
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
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.wrapInc D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    FixMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * (D.CL.S + D.CL.A) + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂) u t r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := fixMeanBound_blocks (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z u t r2 ha hz hu hpar hne hsel σ hσc hS1 hS4 c₂ hr2 hmixQ hmixR
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  exact hmain D hpair z u t r2 ha (M0 := modulus pr h) (Qpre := 1) (N0 := 0) (N0' := 0) hM0
    (eventually_scaleConditions _ _ _ _ _ _ (by norm_num [blockScale]) hM0 hQ1) dvd_rfl hz hu hpar
    hne hsel le_rfl (hW_fix_of_summable D) hσc hS1 hS4 c₂ hr2 hmixQ hmixR

/-- (S4) at `ε' = 1/2000`: `ε'/20 − τ/4 ≤ −1/825` (`τ = 1/201`). -/
theorem S4_at_small : (1 / 2000 : ℝ) / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay := by
  unfold stageTau Sarkozy.cancellationDecay
  norm_num

/-- **`envMeanBoundL_final` at `ε = 1/10`, `ε' = 1/2000`, `σ = 1/825`** ((S1) by DC1's
`S1_at_cancellationDecay`, (S4) by `S4_at_small`). What remains: `z_L ≥ u_L` eventually, the
paper-data facts (parity, nonempty blocks, `blockSel ≤ selPre`), DC2's `r₂` summation `_hr2`,
and the per-atom unit mixed `L^{72/ϑ}` bounds `_hmixQ`, `_hmixR` (`lem:density:packets`). -/
theorem envMeanBoundL_paperFinal :
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
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncL D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂)
      (fun L => TheoremCBlock.Structured.envIncL D L)
      (fun L => TheoremCBlock.Structured.envPriceL D L)
      D.index.u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundL_final (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop (1 / 10) (1 / 2000) (by norm_num) (by norm_num)
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha hz hpar hne hsel c₂ hr2 hmixQ hmixR
  exact hmain D hpair z r2 ha hz hpar hne hsel le_rfl S1_at_cancellationDecay S4_at_small c₂ hr2
    hmixQ hmixR

/-- **`envMeanBoundR_final` at `ε = 1/10`, `ε' = 1/2000`, `σ = 1/825`** ((S1) by DC1's
`S1_at_cancellationDecay`, (S4) by `S4_at_small`). What remains: `z_L ≥ u_L` eventually, the
paper-data facts (parity, nonempty blocks, `blockSel ≤ selPre`), DC2's `r₂` summation `_hr2`,
and the per-atom unit mixed `L^{72/ϑ}` bounds `_hmixQ`, `_hmixR` (`lem:density:packets`). -/
theorem envMeanBoundR_paperFinal :
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
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.envIncR D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂)
      (fun L => TheoremCBlock.Structured.envIncR D L)
      (fun L => TheoremCBlock.Structured.envPriceR D L)
      D.index.w r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBoundR_final (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop (1 / 10) (1 / 2000) (by norm_num) (by norm_num)
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha hz hpar hne hsel c₂ hr2 hmixQ hmixR
  exact hmain D hpair z r2 ha hz hpar hne hsel le_rfl S1_at_cancellationDecay S4_at_small c₂ hr2
    hmixQ hmixR

/-- **`fixMeanBound_final` at `ε = 1/10`, `ε' = 1/2000`, `σ = 1/825`** ((S1) by DC1's
`S1_at_cancellationDecay`, (S4) by `S4_at_small`). What remains: `z_L ≥ u_L` eventually, the
paper-data facts (parity, nonempty blocks, `blockSel ≤ selPre`), DC2's `r₂` summation `_hr2`,
and the per-atom unit mixed `L^{72/ϑ}` bounds `_hmixQ`, `_hmixR` (`lem:density:packets`). -/
theorem fixMeanBound_paperFinal :
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
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hmixQ : ∀ᶠ L in atTop, ∀ b,
      ∀ hb : 0 < totalVariation (lawDensity (TheoremCBlock.Structured.wrapInc D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (_hmixR : ∀ᶠ L in atTop, ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
        MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1),
    FixMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * (D.CL.S + D.CL.A) + D.GB.U₀) +
        lpConst m₀ blk (modulus pr h) Clp * Real.exp (2 * D.SM.bound) + c₂) u t r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := fixMeanBound_final (a := a) (m₀ := m₀)
    (blk := blk) (pr := pr) (h := h) (E := E) hcop (1 / 10) (1 / 2000) (by norm_num) (by norm_num)
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z u t r2 ha hz hu hpar hne hsel c₂ hr2 hmixQ hmixR
  exact hmain D hpair z u t r2 ha hz hu hpar hne hsel le_rfl S1_at_cancellationDecay S4_at_small c₂
    hr2 hmixQ hmixR

end Sarkozy.DensityChain2
