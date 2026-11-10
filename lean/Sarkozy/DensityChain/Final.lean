module

public import Sarkozy.DensityChain.Reduced
public import Sarkozy.DensityChain.MuTerm

@[expose] public section

/-!
# Fields 30–31 reduced to restoration and `hatom`

`envMeanBound_of_reduced` (`Reduced`) still allowed the `μ`-term (`f = g = ∅`) to be supplied by
its direct first bound. `env_mu_chain_of` (`MuTerm`) proves that bound from restoration at the
query slots, with the same constants `C₁, C₇₁` (`DCBlockProp`). So:

**`envMeanBound_of_restoration`** (K2's fields 30–31, `Sh.envM.hmL/R`): B9's `EnvMeanBound` with
an explicit constant, from
* per term `(f, g)` of positive weight: restoration at the child scales with the paper's cutoffs
  (`lem:record:fibre-scale`(c),(d)) and the unit mixed `L^{72/ϑ}` moments of the selected laws
  (`lem:density:coupled`, `lem:density:packets`; vacuous for the `μ`-term);
* DC2's `r₂` summation (`lem:sharp-first`);
* frame facts: the scale conditions, the per-atom factorization `D_𝔟 = q_𝔟 c_𝔟`, the index
  modulus, `u_L ≤ z_L`; the price inequalities, the price totals and the `q^{1/4}`-weighted
  summability (`def:cp8`(c)); (S1), (S4).

`lem:record:density-dc`, `lem:record:density-lp`, condition (b) of
`def:record:structured-energy`, the modulus conditions, the `μ`-term's `hun` and the summation are
all proved.
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

/-- **Fields 30–31 (`EnvMeanBound`) reduced to restoration and `hatom`** (see the module
docstring). -/
theorem envMeanBound_of_restoration (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
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
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L _ =>
      ∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
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
          MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1))),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * Real.exp (2 * TQ + U0) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂) Qb price u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := envMeanBound_of_reduced (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z Qb price u r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hprice
    hQpos hQ hR TQ U0 W hTQ hU0 wq cq hfac hwq hcq hcq0 hwcq hQcl hm2 hW σ hσc hS1 hS4 c₂ hr2
    hterms
  have hσ : 0 ≤ σ := le_trans (by norm_num [Sarkozy.cancellationDecay]) hσc
  apply hmain D hpair z Qb price u r2 ha hM0 hsc hp hinj hMod hcopM hz hu hprice hQpos hQ hR
    hTQ hU0 wq cq hfac hwq hcq hcq0 hwcq hQcl hm2 hW hσc hS1 hS4 c₂ hr2
  have hL2 : ∀ᶠ L : ℕ in atTop, 2 ≤ L := eventually_ge_atTop 2
  filter_upwards [hterms, hsc, hz, hL2] with L hL hscL hzL hL2L
  intro C hC hk A hA hY Jq hJq f g hg
  obtain ⟨hrest, hatom⟩ := hL C hC hk A hA hY Jq hJq f g hg
  by_cases hne : (termSet f g).Nonempty
  · exact Or.inr ⟨hne, hrest, hatom⟩
  · left
    have hT : termSet f g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hfg : ∀ b, f b = false ∧ g b = false := by
      intro b
      have hb : b ∉ termSet f g := by rw [hT]; exact notMem_empty b
      unfold termSet at hb
      simp only [mem_filter, mem_univ, true_and, not_or, Bool.not_eq_true] at hb
      exact hb
    have hf : f = fun _ => false := funext fun b => (hfg b).1
    have hg' : g = fun _ => false := funext fun b => (hfg b).2
    subst hf hg'
    have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
      ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
    have hJ : ∀ e, (Jq e none : ℕ) ≠ 0 := by
      intro e h0
      exact hJq (queryLaw_weight_eq_zero D Jq e h0)
    have hQcl1 : 1 ≤ Qcl := le_trans (Nat.one_le_iff_ne_zero.mpr
      (prod_ne_zero_iff.mpr fun b _ => hcq0 L b)) (hQcl L)
    rw [termSet_false] at hrest
    have key := env_mu_chain_of hcop ε C1 C71 hdcb D (hpair L) hcex ha (zero_le_one.trans hC)
      hL2L hscL hM0 hQcl1 (hp L) (hinj L) (Qb L) Jq hJ u hu hMod (hcopM L) hσ hS1 hrest
      (price L) (hQ L) (hR L)
    have hYpos : 0 ≤ D.Y L A := le_trans (by
      exact mul_nonneg (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)) hcex.lower.le
    have hK : 0 ≤ envTermPrice D price L A Jq (fun _ => false) (fun _ => false) := by
      unfold envTermPrice
      simp only [Bool.false_eq_true, ↓reduceIte, prod_const_one, mul_one]
      exact mul_nonneg (conductorPrice_nonneg pr h _ _) hYpos
    have hprice_eq : conductorPrice pr h (2 * a / 72) Jq * D.Y L A *
        ((∏ b, if (fun _ => false : BlockAtom Bk J L → Bool) b then price L b else 1) *
          ∏ b, (if (fun _ => false : BlockAtom Bk J L → Bool) b then D.GB.uprice L b else 1)) =
        envTermPrice D price L A Jq (fun _ => false) (fun _ => false) := by
      unfold envTermPrice EnvelopeInputsBlock.priceExponent
      ring
    rw [hprice_eq] at key
    have hmono : (1 + scaleU blockScale M0 Qcl stageTau L) *
        envTermPrice D price L A Jq (fun _ => false) (fun _ => false) ≤
        (1 + z L) * envTermPrice D price L A Jq (fun _ => false) (fun _ => false) :=
      mul_le_mul_of_nonneg_right (by linarith) hK
    refine le_trans key ?_
    linarith [hmono]

/-- **Fields 28–29 (`FixMeanBound`) reduced to restoration and `hatom`** (as
`envMeanBound_of_restoration`). -/
theorem fixMeanBound_of_restoration (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧
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
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L _ =>
      ∀ S : Finset E, S ≠ ∅ → ∀ Jq, ∀ f, ∀ g ∈ validChoices f,
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
          MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1))),
    FixMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * Real.exp (2 * TQ + U0) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂) u t r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := fixMeanBound_of_reduced (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, ?_⟩
  intro D hpair z u t r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hQ hR TQ U0 W
    hTQ hU0 wq cq hfac hwq hcq hcq0 hwcq hQcl hm2 hW σ hσc hS1 hS4 c₂ hr2 hterms
  have hσ : 0 ≤ σ := le_trans (by norm_num [Sarkozy.cancellationDecay]) hσc
  apply hmain D hpair z u t r2 ha hM0 hsc hp hinj hMod hcopM hz hu hQ hR hTQ hU0 wq cq hfac hwq
    hcq hcq0 hwcq hQcl hm2 hW hσc hS1 hS4 c₂ hr2
  have hL2 : ∀ᶠ L : ℕ in atTop, 2 ≤ L := eventually_ge_atTop 2
  filter_upwards [hterms, hsc, hz, hL2] with L hL hscL hzL hL2L
  intro C hC hk A hA hY S hS Jq f g hg
  obtain ⟨hrest, hatom⟩ := hL C hC hk A hA hY S hS Jq f g hg
  by_cases hne : (termSet f g).Nonempty
  · exact Or.inr ⟨hne, hrest, hatom⟩
  · left
    have hT : termSet f g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hfg : ∀ b, f b = false ∧ g b = false := by
      intro b
      have hb : b ∉ termSet f g := by rw [hT]; exact notMem_empty b
      unfold termSet at hb
      simp only [mem_filter, mem_univ, true_and, not_or, Bool.not_eq_true] at hb
      exact hb
    have hf : f = fun _ => false := funext fun b => (hfg b).1
    have hg' : g = fun _ => false := funext fun b => (hfg b).2
    subst hf hg'
    have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
      ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
    have hQcl1 : 1 ≤ Qcl := le_trans (Nat.one_le_iff_ne_zero.mpr
      (prod_ne_zero_iff.mpr fun b _ => hcq0 L b)) (hQcl L)
    rw [termSet_false] at hrest
    have key := fix_mu_chain_of hcop ε C1 C71 hdcb D (hpair L) hcex ha (zero_le_one.trans hC)
      hL2L hscL hM0 hQcl1 (hp L) (hinj L) (TheoremCBlock.Structured.wrapInc D L) S t Jq u hu
      hMod (hcopM L) hσ hS1 hrest (TheoremCBlock.Structured.wrapPrice D L) (hQ L) (hR L)
    have hYpos : 0 ≤ D.Y L A := le_trans (by
      exact mul_nonneg (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)) hcex.lower.le
    have hK : 0 ≤ fixTermPrice D L A S Jq (fun _ => false) (fun _ => false) := by
      unfold fixTermPrice
      simp only [Bool.false_eq_true, ↓reduceIte, prod_const_one, mul_one]
      exact mul_nonneg (fixedPrice_nonneg pr h _ _ _) hYpos
    have hprice_eq : fixedPrice pr h (2 * a / 72) S Jq * D.Y L A *
        ((∏ b, if (fun _ => false : BlockAtom Bk J L → Bool) b then
            TheoremCBlock.Structured.wrapPrice D L b else 1) *
          ∏ b, (if (fun _ => false : BlockAtom Bk J L → Bool) b then D.GB.uprice L b else 1)) =
        fixTermPrice D L A S Jq (fun _ => false) (fun _ => false) := by
      unfold fixTermPrice EnvelopeInputsBlock.priceExponent
      ring
    rw [hprice_eq] at key
    have hmono : (1 + scaleU blockScale M0 Qcl stageTau L) *
        fixTermPrice D L A S Jq (fun _ => false) (fun _ => false) ≤
        (1 + z L) * fixTermPrice D L A S Jq (fun _ => false) (fun _ => false) :=
      mul_le_mul_of_nonneg_right (by linarith) hK
    refine le_trans key ?_
    linarith [hmono]

end Sarkozy.DensityChain
