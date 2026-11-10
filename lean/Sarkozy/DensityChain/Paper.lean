module

public import Sarkozy.DensityChain.Summable
public import Sarkozy.BracketEnergy.PriceMatch

@[expose] public section

/-!
# Fields 30–31 at the paper's data

`envMeanBound_of_summable` instantiated at the left envelope side of K0's comparison data
(`Q_𝔟 = envIncL`, `u_𝔟 = envPriceL`, `u = D.index.u`), with every data fact discharged from `D`:

* distinct prime tail moduli (`D.S.p_prime`, `D.S.p_inj`), injective sources (`D.index.hu`);
* the index modulus is coprime to the block moduli (`D.S.modulus_coprime`, `hcopM_of_data`);
* the increments and records are positive records (`isPositiveRecord_envIncL`, `Records`);
* the price inequalities `‖Q_𝔟‖ sq(D_𝔟)^a ≤ u_𝔟`, `‖Ñ₀ − μ‖ sq(D_𝔟)^a ≤ u'_𝔟` from the per-atom
  selection inequality `sq(D_𝔟)^a ≤ q_𝔟^{2a}` (`hselF`; B9's `envIncL_price_le`,
  `recLaw_price_le`);
* the price totals `∑ u ≤ T` (`D.ME.TL_total`) and `∑ u' ≤ U₀` (`D.GB.U₀_total`).

**`envMeanBoundL_paper`** is B9's field `hmL` of `EnvelopeBracketInputs.ofMeans` (K2's field 30).
The right side (field 31) is the same with `envIncR`, `envPriceR`, `D.index.w`, `TR_total`.
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

omit [DecidableEq P] in
/-- The index modulus is coprime to the block moduli (from `StandingData.modulus_coprime`). -/
theorem hcopM_of_data (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (k : BlockAtom Bk J L) : (modulus pr h).Coprime (crtModuli m₀ blk p L k) := by
  rcases k with β | j
  · exact Nat.Coprime.prod_right fun i _ => D.S.modulus_coprime L (Sum.inl i.1)
  · exact D.S.modulus_coprime L (Sum.inr j)

/-- **Field 30 (`Sh.envM.hmL`) at the paper's data.** -/
theorem envMeanBoundL_paper (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
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
    {W : ℝ} (w : ∀ L, BlockAtom Bk J L → ℝ) (_hw : ∀ L b, 0 ≤ w L b)
    (_hW : ∀ L, ∑ b, w L b ^ ((1 : ℝ) / 4) *
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
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
        EnvChainTerm hcop D (hpair L) (TheoremCBlock.Structured.envIncL D L) D.index.u Qcl Jq f g ∨
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
            (fun ω => envTermEnergy hcop D hpair (fun L => TheoremCBlock.Structured.envIncL D L)
              D.index.u L A Jq ω f g) ≤
          (1 + z L) * envTermPrice D (fun L => TheoremCBlock.Structured.envPriceL D L) L A Jq f g +
            (∏ b, termWeight D L (TheoremCBlock.Structured.envIncL D L) b (f b) (g b)) *
              (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
        ((blockScale * L : ℕ) : ℝ) ^ stageTau <
          ∏ b, (if (f b || g b) = true then w L b else 1))),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) + lpConst m₀ blk M0 Clp * Real.exp W + c₂)
      (fun L => TheoremCBlock.Structured.envIncL D L)
      (fun L => TheoremCBlock.Structured.envPriceL D L) D.index.u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := envMeanBound_of_summable (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hMod hz hselF W w hw hW σ hσc hS1 hS4 c₂
    hr2 hterms
  exact hmain D hpair z (fun L => TheoremCBlock.Structured.envIncL D L)
    (fun L => TheoremCBlock.Structured.envPriceL D L) D.index.u r2 ha hM0 hsc D.S.p_prime
    D.S.p_inj hMod (hcopM_of_data D) hz D.index.hu
    (fun L b => TheoremCBlock.Structured.envPriceL_nonneg D L b)
    (fun L b => isPositiveRecord_envIncL D L b)
    (fun L b => envIncL_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L b => recLaw_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L => D.ME.TL_total L) (fun L => D.GB.U₀_total L) w hw hW hσc hS1 hS4 c₂ hr2 hterms

/-- **Field 31 (`Sh.envM.hmR`) at the paper's data.** -/
theorem envMeanBoundR_paper (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
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
    {W : ℝ} (w : ∀ L, BlockAtom Bk J L → ℝ) (_hw : ∀ L b, 0 ≤ w L b)
    (_hW : ∀ L, ∑ b, w L b ^ ((1 : ℝ) / 4) *
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
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
        EnvChainTerm hcop D (hpair L) (TheoremCBlock.Structured.envIncR D L) D.index.w Qcl Jq f g ∨
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
            (fun ω => envTermEnergy hcop D hpair (fun L => TheoremCBlock.Structured.envIncR D L)
              D.index.w L A Jq ω f g) ≤
          (1 + z L) * envTermPrice D (fun L => TheoremCBlock.Structured.envPriceR D L) L A Jq f g +
            (∏ b, termWeight D L (TheoremCBlock.Structured.envIncR D L) b (f b) (g b)) *
              (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
        ((blockScale * L : ℕ) : ℝ) ^ stageTau <
          ∏ b, (if (f b || g b) = true then w L b else 1))),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
          Real.exp (2 * D.ME.T + D.GB.U₀) + lpConst m₀ blk M0 Clp * Real.exp W + c₂)
      (fun L => TheoremCBlock.Structured.envIncR D L)
      (fun L => TheoremCBlock.Structured.envPriceR D L) D.index.w r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := envMeanBound_of_summable (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hMod hz hselF W w hw hW σ hσc hS1 hS4 c₂
    hr2 hterms
  exact hmain D hpair z (fun L => TheoremCBlock.Structured.envIncR D L)
    (fun L => TheoremCBlock.Structured.envPriceR D L) D.index.w r2 ha hM0 hsc D.S.p_prime
    D.S.p_inj hMod (hcopM_of_data D) hz D.index.hw
    (fun L b => TheoremCBlock.Structured.envPriceR_nonneg D L b)
    (fun L b => isPositiveRecord_envIncR D L b)
    (fun L b => envIncR_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L b => recLaw_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF L b))
    (fun L => D.ME.TR_total L) (fun L => D.GB.U₀_total L) w hw hW hσc hS1 hS4 c₂ hr2 hterms

end Sarkozy.DensityChain
