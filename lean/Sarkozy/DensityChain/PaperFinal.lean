module

public import Sarkozy.DensityChain.Final
public import Sarkozy.DensityChain.Paper

@[expose] public section

/-!
# Fields 30–31 at the paper's data, reduced to restoration and `hatom`

`envMeanBound_of_restoration` (`Final`) instantiated at the two envelope sides of K0's comparison
data, with the data facts discharged as in `Paper` (prime distinct tails, injective sources, the
index modulus coprime to the block moduli, positive increments, the price inequalities from
`sq(D_𝔟)^a ≤ q_𝔟^{2a}`, the price totals `T`, `U₀`).
-/

namespace Sarkozy.DensityChain

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Field 30 (`Sh.envM.hmL`) at the paper's data, reduced to restoration and
`hatom`** (`envMeanBound_of_restoration` with the data facts discharged as in
`envMeanBoundL_paper`). -/
theorem envMeanBoundL_paper_restoration (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hMod : modulus pr h ∣ M0)
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hselF : ∀ L b, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b)
    {W : ℝ}
    (wq cq : ∀ L, BlockAtom Bk J L → ℕ)
    (_hfac : ∀ L b, crtModuli m₀ blk p L b = wq L b * cq L b)
    (_hwq : ∀ L b, Squarefree (wq L b)) (_hcq : ∀ L b, IsSquare (cq L b))
    (_hcq0 : ∀ L b, cq L b ≠ 0) (_hwcq : ∀ L b, (wq L b).Coprime (cq L b))
    (_hQcl : ∀ L, ∏ b, cq L b ≤ Qcl) (_hm2 : ∀ L b, 2 ≤ crtModuli m₀ blk p L b)
    (_hW : ∀ L, ∑ b, ((wq L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
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
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L _ =>
      ∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
        (∀ ω v, ∀ B : Finset ℤ,
          B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
            (envSlots hcop D.index.u L Jq ω v).1
            (envSlots hcop D.index.u L Jq ω v).2.2.1 : ℕ) : ℤ) →
          referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise (hpair L)) D.R.μ₀
              D.R.μp L))
              (child (crtModuli m₀ blk p L) (termSet f g)
                (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
                  (envSlots hcop D.index.u L Jq ω v).1 (envSlots hcop D.index.u L Jq ω v).2.2.1)) B
                (blockScale * stepEll (crtModuli m₀ blk p L)
                (termSet f g) (envSlots hcop D.index.u L Jq ω v).1
                (envSlots hcop D.index.u L Jq ω v).2.2.1)) ≤
            D.Y (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop D.index.u L Jq ω v).1
              (envSlots hcop D.index.u L Jq ω v).2.2.1) B) ∧
        (∀ b ∈ termSet f g,
          ∀ hb : 0 < totalVariation (lawDensity
            (BracketEnergy.termLaw D L (TheoremCBlock.Structured.envIncL D L) f g b)),
          MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1))),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂)
      (fun L => TheoremCBlock.Structured.envIncL D L)
      (fun L => TheoremCBlock.Structured.envPriceL D L)
      D.index.u r2  := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBound_of_restoration (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hMod hz hselF W wq cq hfac hwq hcq hcq0 hwcq
    hQcl hm2 hW σ hσc hS1 hS4 c₂ hr2 hterms
  exact hmain D hpair z (fun L => TheoremCBlock.Structured.envIncL D L)
    (fun L => TheoremCBlock.Structured.envPriceL D L) D.index.u r2 ha hM0 hsc D.S.p_prime
    D.S.p_inj hMod (hcopM_of_data D) hz D.index.hu
    (fun L b => TheoremCBlock.Structured.envPriceL_nonneg D L b)
    (fun L b => isPositiveRecord_envIncL D L b)
    (fun L b => envIncL_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L b => recLaw_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L => D.ME.TL_total L) (fun L => D.GB.U₀_total L) wq cq hfac hwq hcq hcq0 hwcq hQcl hm2
    hW hσc hS1 hS4 c₂ hr2 hterms

/-- **Field 31 (`Sh.envM.hmR`) at the paper's data, reduced to restoration and
`hatom`** (`envMeanBound_of_restoration` with the data facts discharged as in
`envMeanBoundR_paper`). -/
theorem envMeanBoundR_paper_restoration (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hMod : modulus pr h ∣ M0)
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hselF : ∀ L b, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b)
    {W : ℝ}
    (wq cq : ∀ L, BlockAtom Bk J L → ℕ)
    (_hfac : ∀ L b, crtModuli m₀ blk p L b = wq L b * cq L b)
    (_hwq : ∀ L b, Squarefree (wq L b)) (_hcq : ∀ L b, IsSquare (cq L b))
    (_hcq0 : ∀ L b, cq L b ≠ 0) (_hwcq : ∀ L b, (wq L b).Coprime (cq L b))
    (_hQcl : ∀ L, ∏ b, cq L b ≤ Qcl) (_hm2 : ∀ L b, 2 ≤ crtModuli m₀ blk p L b)
    (_hW : ∀ L, ∑ b, ((wq L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
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
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L _ =>
      ∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
        (∀ ω v, ∀ B : Finset ℤ,
          B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
            (envSlots hcop D.index.w L Jq ω v).1
            (envSlots hcop D.index.w L Jq ω v).2.2.1 : ℕ) : ℤ) →
          referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise (hpair L)) D.R.μ₀
              D.R.μp L))
              (child (crtModuli m₀ blk p L) (termSet f g)
                (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
                  (envSlots hcop D.index.w L Jq ω v).1 (envSlots hcop D.index.w L Jq ω v).2.2.1)) B
                (blockScale * stepEll (crtModuli m₀ blk p L)
                (termSet f g) (envSlots hcop D.index.w L Jq ω v).1
                (envSlots hcop D.index.w L Jq ω v).2.2.1)) ≤
            D.Y (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop D.index.w L Jq ω v).1
              (envSlots hcop D.index.w L Jq ω v).2.2.1) B) ∧
        (∀ b ∈ termSet f g,
          ∀ hb : 0 < totalVariation (lawDensity
            (BracketEnergy.termLaw D L (TheoremCBlock.Structured.envIncR D L) f g b)),
          MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1))),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂)
      (fun L => TheoremCBlock.Structured.envIncR D L)
      (fun L => TheoremCBlock.Structured.envPriceR D L)
      D.index.w r2  := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hmain⟩ := envMeanBound_of_restoration (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hMod hz hselF W wq cq hfac hwq hcq hcq0 hwcq
    hQcl hm2 hW σ hσc hS1 hS4 c₂ hr2 hterms
  exact hmain D hpair z (fun L => TheoremCBlock.Structured.envIncR D L)
    (fun L => TheoremCBlock.Structured.envPriceR D L) D.index.w r2 ha hM0 hsc D.S.p_prime
    D.S.p_inj hMod (hcopM_of_data D) hz D.index.hw
    (fun L b => TheoremCBlock.Structured.envPriceR_nonneg D L b)
    (fun L b => isPositiveRecord_envIncR D L b)
    (fun L b => envIncR_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L b => recLaw_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L => D.ME.TR_total L) (fun L => D.GB.U₀_total L) wq cq hfac hwq hcq hcq0 hwcq hQcl hm2
    hW hσc hS1 hS4 c₂ hr2 hterms

end Sarkozy.DensityChain
