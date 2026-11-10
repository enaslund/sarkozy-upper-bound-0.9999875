module

public import Sarkozy.DensityChain.Summable
public import Sarkozy.DensityChain.Moduli

@[expose] public section

/-!
# Fields 28–31 reduced to restoration, `hatom` and the `μ`-term

`envMeanBound_of_summable`, `fixMeanBound_of_summable` (`Summable`) ask, per term, the chain's
per-term inputs, or the direct bound of the `μ`-term, or largeness. With a per-atom factorization
`D_𝔟 = q_𝔟 c_𝔟` (`q_𝔟` squarefree, `c_𝔟` a nonzero square, coprime; `∏ c_𝔟 ≤ Q_cl`; every
`D_𝔟 ≥ 2`), the modulus conditions and the large/small dichotomy are proved (`moduli_dichotomy`)
and the Rankin weights are `w_𝔟 = q_𝔟`. What remains per term is:

* the `μ`-term (`f = g = ∅`): its direct first bound (B9's `env_first_mean_le_query`, with
  `hun`), or
* for a nonempty `f ∪ g`: restoration (`hrest`) and the moments of the selected laws (`hatom`).

**`envMeanBound_of_reduced`** (fields 30–31) and **`fixMeanBound_of_reduced`** (fields 28–29).
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

/-- The selected set as a choice function: `𝔟 ∈ f ∪ g` iff `f 𝔟 || g 𝔟`. -/
theorem prod_termSet_cast {L : ℕ} (w : BlockAtom Bk J L → ℕ) (f g : BlockAtom Bk J L → Bool) :
    ∏ b, ((if b ∈ termSet f g then w b else 1 : ℕ) : ℝ) =
      ∏ b, (if (f b || g b) = true then (w b : ℝ) else 1) := by
  apply prod_congr rfl
  intro b _
  unfold termSet
  simp only [mem_filter, mem_univ, true_and, Bool.or_eq_true]
  split_ifs <;> simp

/-- **Fields 30–31 (`EnvMeanBound`) reduced to restoration, `hatom` and the `μ`-term.** -/
theorem envMeanBound_of_reduced (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : ∀ L, BlockAtom Bk J L → ℝ) (u : E → reservedCut.Half)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hp : ∀ L j, (p L j).Prime) (_hinj : ∀ L, Injective (p L))
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ L k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hu : Injective u) (_hprice : ∀ L b, 0 ≤ price L b)
    (_hQpos : ∀ L b, IsPositiveRecord (Qb L b))
    (_hQ : ∀ L b, (∑ x, |lawDensity (Qb L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ price L b)
    (_hR : ∀ L b, (∑ x, |lawDensity (recLaw D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b)
    {TQ U0 W : ℝ} (_hTQ : ∀ L, ∑ b, price L b ≤ TQ) (_hU0 : ∀ L, ∑ b, D.GB.uprice L b ≤ U0)
    (wq cq : ∀ L, BlockAtom Bk J L → ℕ)
    (_hfac : ∀ L b, crtModuli m₀ blk p L b = wq L b * cq L b)
    (_hwq : ∀ L b, Squarefree (wq L b)) (_hcq : ∀ L b, IsSquare (cq L b))
    (_hcq0 : ∀ L b, cq L b ≠ 0) (_hwcq : ∀ L b, (wq L b).Coprime (cq L b))
    (_hQcl : ∀ L, ∏ b, cq L b ≤ Qcl) (_hm2 : ∀ L b, 2 ≤ crtModuli m₀ blk p L b)
    (_hW : ∀ L, ∑ b, ((wq L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) * (2 * price L b + D.GB.uprice L b) ≤ W)
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
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
            (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) ≤
          (1 + z L) * envTermPrice D price L A Jq f g +
            (∏ b, termWeight D L (Qb L) b (f b) (g b)) *
              (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
        ((termSet f g).Nonempty ∧
          (∀ ω v, ∀ B : Finset ℤ,
            B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
              (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
            referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise (hpair L)) D.R.μ₀
                D.R.μp L))
                (child (crtModuli m₀ blk p L) (termSet f g)
                  (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
                    (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1)) B
                  (blockScale * stepEll (crtModuli m₀ blk p L)
                  (termSet f g) (envSlots hcop u L Jq ω v).1
                  (envSlots hcop u L Jq ω v).2.2.1)) ≤
              D.Y (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop u L Jq ω v).1
                (envSlots hcop u L Jq ω v).2.2.1) B) ∧
          (∀ b ∈ termSet f g,
            ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L (Qb L) f g b)),
            MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)))),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * Real.exp (2 * TQ + U0) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂) Qb price u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := envMeanBound_of_summable (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, ?_⟩
  intro D hpair z Qb price u r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hprice
    hQpos hQ hR TQ U0 W hTQ hU0 wq cq hfac hwq hcq hcq0 hwcq hQcl hm2 hW σ hσc hS1 hS4 c₂ hr2
    hterms
  apply hmain D hpair z Qb price u r2 ha hM0 hsc hp hinj hMod hcopM hz hu hprice hQpos hQ hR
    hTQ hU0 (fun L b => (wq L b : ℝ)) (fun L b => Nat.cast_nonneg _) hW hσc hS1 hS4 c₂ hr2
  filter_upwards [hterms] with L hL
  intro C hC hk A hA hY Jq hJq f g hg
  rcases hL C hC hk A hA hY Jq hJq f g hg with hdir | ⟨hne, hrest, hatom⟩
  · exact Or.inr (Or.inl hdir)
  · rcases moduli_dichotomy (crtModuli m₀ blk p L) (wq L) (cq L) (hfac L) (hwq L) (hcq L)
      (hcq0 L) (hwcq L) (crtModuli_pairwise blk (hpair L)) (hQcl L)
      (((blockScale * L : ℕ) : ℝ) ^ stageTau) (termSet f g) with hmod | hlarge
    · exact Or.inl ⟨hmod, prod_ne_one_of_nonempty _ (hm2 L) hne, hrest, hatom⟩
    · refine Or.inr (Or.inr ?_)
      rw [← prod_termSet_cast]
      exact hlarge

/-- **Fields 28–29 (`FixMeanBound`) reduced to restoration, `hatom` and the `μ`-term.** -/
theorem fixMeanBound_of_reduced (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
    (r2 : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hp : ∀ L j, (p L j).Prime) (_hinj : ∀ L, Injective (p L))
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ L k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hu : Injective u)
    (_hQ : ∀ L b, (∑ x, |lawDensity (TheoremCBlock.Structured.wrapInc D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
        TheoremCBlock.Structured.wrapPrice D L b)
    (_hR : ∀ L b, (∑ x, |lawDensity (recLaw D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b)
    {TQ U0 W : ℝ} (_hTQ : ∀ L, ∑ b, TheoremCBlock.Structured.wrapPrice D L b ≤ TQ)
    (_hU0 : ∀ L, ∑ b, D.GB.uprice L b ≤ U0)
    (wq cq : ∀ L, BlockAtom Bk J L → ℕ)
    (_hfac : ∀ L b, crtModuli m₀ blk p L b = wq L b * cq L b)
    (_hwq : ∀ L b, Squarefree (wq L b)) (_hcq : ∀ L b, IsSquare (cq L b))
    (_hcq0 : ∀ L b, cq L b ≠ 0) (_hwcq : ∀ L b, (wq L b).Coprime (cq L b))
    (_hQcl : ∀ L, ∏ b, cq L b ≤ Qcl) (_hm2 : ∀ L b, 2 ≤ crtModuli m₀ blk p L b)
    (_hW : ∀ L, ∑ b, ((wq L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
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
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ S : Finset E, S ≠ ∅ → ∀ Jq, ∀ f, ∀ g ∈ validChoices f,
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
            (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) ≤
          (1 + z L) * fixTermPrice D L A S Jq f g +
            (∏ b, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b (f b) (g b)) *
              (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
        ((termSet f g).Nonempty ∧
          (∀ ω v, ∀ B : Finset ℤ,
            B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
              (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
            referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise (hpair L)) D.R.μ₀
                D.R.μp L))
                (child (crtModuli m₀ blk p L) (termSet f g)
                  (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
                    (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1)) B
                  (blockScale * stepEll (crtModuli m₀ blk p L)
                  (termSet f g) (fixSlots hcop u L S t Jq ω v).1
                  (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
              D.Y (stepEll (crtModuli m₀ blk p L) (termSet f g) (fixSlots hcop u L S t Jq ω v).1
                (fixSlots hcop u L S t Jq ω v).2.2.1) B) ∧
          (∀ b ∈ termSet f g,
            ∀ hb : 0 < totalVariation (lawDensity
              (BracketEnergy.termLaw D L (TheoremCBlock.Structured.wrapInc D L) f g b)),
            MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)))),
    FixMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * Real.exp (2 * TQ + U0) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂) u t r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := fixMeanBound_of_summable (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, ?_⟩
  intro D hpair z u t r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hQ hR TQ U0 W
    hTQ hU0 wq cq hfac hwq hcq hcq0 hwcq hQcl hm2 hW σ hσc hS1 hS4 c₂ hr2 hterms
  apply hmain D hpair z u t r2 ha hM0 hsc hp hinj hMod hcopM hz hu hQ hR hTQ hU0
    (fun L b => (wq L b : ℝ)) (fun L b => Nat.cast_nonneg _) hW hσc hS1 hS4 c₂ hr2
  filter_upwards [hterms] with L hL
  intro C hC hk A hA hY S hS Jq f g hg
  rcases hL C hC hk A hA hY S hS Jq f g hg with hdir | ⟨hne, hrest, hatom⟩
  · exact Or.inr (Or.inl hdir)
  · rcases moduli_dichotomy (crtModuli m₀ blk p L) (wq L) (cq L) (hfac L) (hwq L) (hcq L)
      (hcq0 L) (hwcq L) (crtModuli_pairwise blk (hpair L)) (hQcl L)
      (((blockScale * L : ℕ) : ℝ) ^ stageTau) (termSet f g) with hmod | hlarge
    · exact Or.inl ⟨hmod, prod_ne_one_of_nonempty _ (hm2 L) hne, hrest, hatom⟩
    · refine Or.inr (Or.inr ?_)
      rw [← prod_termSet_cast]
      exact hlarge

end Sarkozy.DensityChain
