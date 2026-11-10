module

public import Sarkozy.DensityChain.EnvChain
public import Sarkozy.DensityChain.FixChain
public import Sarkozy.DensityChain.LargeTerms

@[expose] public section

/-!
# Fields 28–31 with `lem:record:density-dc` and `lem:record:density-lp` both discharged

`envMeanBound_of_chain` and `fixMeanBound_of_chain` (`EnvChain`, `FixChain`) allow, for a term not
covered by the chain, a bound of the form of `lem:record:density-lp`. `env_term_lp`,
`fix_term_lp` (`LargeTerms`) prove that bound for **every** term, with
`B = M₀^{72} |X₀|^{72} C Q^{ε'} K α`. So here the large alternative is only the combinatorial
condition `T < ∏_{𝔟 ∈ f ∪ g} w_𝔟` (in the paper `T = N^τ`, `w_𝔟 = q_𝔟`):

* **`envMeanBound_of_chain_lp`** (fields 30–31, `Sh.envM.hmL/R`);
* **`fixMeanBound_of_chain_lp`** (fields 28–29, `Sh.fixM.hmL/R`).

What remains per term is the chain's per-term input (`EnvChainTerm`, `FixChainTerm`: the modulus
conditions, `D_{f∪g} ≠ 1`, restoration, `hatom`), or the direct first bound of the `μ`-term, or
largeness; and per counterexample one inequality between explicit constants.
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

/-- The bound `B = M₀^{72} |X₀|^{72} C Q(KL)^{ε'} K α` of `lem:record:density-lp` per term. -/
noncomputable def lpBound (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (blk : J₀ → Bk) (M0 : ℕ)
    (C ε' : ℝ) (L : ℕ) (A : Finset ℤ) : ℝ :=
  (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
    paperCutoff (blockScale * L) ^ ε' * ((blockScale : ℝ) * density (blockScale * L) A))

omit [DecidableEq J₀] in
theorem lpBound_nonneg (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (blk : J₀ → Bk) (M0 : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (ε' : ℝ) (L : ℕ) (A : Finset ℤ) : 0 ≤ lpBound m₀ blk M0 C ε' L A := by
  unfold lpBound
  have h1 : 0 ≤ paperCutoff (blockScale * L) ^ ε' := by
    unfold paperCutoff
    exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
  have h2 := density_nonneg (blockScale * L) A
  have h3 : (0 : ℝ) ≤ blockScale := by norm_num [blockScale]
  positivity

/-- **Fields 30–31 (`EnvMeanBound`) with density-dc and density-lp discharged.** -/
theorem envMeanBound_of_chain_lp (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b)
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
    {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∃ (w : BlockAtom Bk J L → ℝ) (T : ℝ), (∀ b, 0 ≤ w b) ∧ 0 < T ∧
        (∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
          EnvChainTerm hcop D (hpair L) (Qb L) u Qcl Jq f g ∨
          (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) ≤
            (1 + z L) * envTermPrice D price L A Jq f g +
              (∏ b, termWeight D L (Qb L) b (f b) (g b)) *
                (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                  (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                  (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
          T < ∏ b, (if (f b || g b) = true then w b else 1)) ∧
        dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A *
            ∏ b, ∑ x, ∑ y, termWeight D L (Qb L) b x y +
          lpBound m₀ blk M0 Clp ε' L A * (T ^ (-((1 : ℝ) / 4)) *
            ∏ b, ∑ x, ∑ y, termWeight D L (Qb L) b x y *
              (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) +
          (queryLaw D.index.C D.index.t).expect (fun Jq =>
            (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => ∑ f, r2 L A Jq ω f)) ≤ remainder c L A)),
    EnvMeanBound hcop D hpair z c Qb price u r2 := by
  obtain ⟨C1, C71, hC1, hC71, hdcb, hchain⟩ := envMeanBound_of_chain (a := a) (m₀ := m₀)
    (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε hε
  obtain ⟨Clp, hClp, hlp⟩ := env_term_lp (a := a) (m₀ := m₀) (blk := blk) (p := p) (pr := pr)
    (h := h) (E := E) hcop ε' hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, ?_⟩
  intro D hpair z c Qb price u r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hprice
    hQpos hQ hR σ hσ hS1 hterms
  apply hchain D hpair z c Qb price u r2 ha hM0 hsc hp hinj hMod hcopM hz hu hprice hQpos hQ hR
    hσ hS1
  have hL1 : ∀ᶠ L : ℕ in atTop, 1 ≤ L := eventually_ge_atTop 1
  filter_upwards [hterms, hsc, hL1] with L hL hscL hL1L
  intro C hC hk A hA hY
  obtain ⟨w, T, hw, hT, hterm, hsum⟩ := hL C hC hk A hA hY
  refine ⟨w, T, lpBound m₀ blk M0 Clp ε' L A, hw, hT, lpBound_nonneg m₀ blk M0 hClp.le ε' L A,
    ?_, hsum⟩
  intro Jq hJq f g hg
  rcases hterm Jq hJq f g hg with hch | hdir | hlg
  · exact Or.inl hch
  · exact Or.inr (Or.inl hdir)
  · refine Or.inr (Or.inr ⟨?_, hlg⟩)
    have hJ : ∀ e, (Jq e none : ℕ) ≠ 0 := by
      intro e h0
      exact hJq (queryLaw_weight_eq_zero D Jq e h0)
    exact hlp D hpair Qb u hscL hL1L hM0 (hp L) (hinj L) hMod (hQpos L) Jq hJ f g

/-- **Fields 28–29 (`FixMeanBound`) with density-dc and density-lp discharged.** -/
theorem fixMeanBound_of_chain_lp (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
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
    {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ S : Finset E, S ≠ ∅ →
      ∃ (w : BlockAtom Bk J L → ℝ) (T : ℝ), (∀ b, 0 ≤ w b) ∧ 0 < T ∧
        (∀ Jq, ∀ f, ∀ g ∈ validChoices f,
          FixChainTerm hcop D (hpair L) (TheoremCBlock.Structured.wrapInc D L) u Qcl S t Jq f g ∨
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) ≤
            (1 + z L) * fixTermPrice D L A S Jq f g +
              (∏ b, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b (f b) (g b)) *
                (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                  (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                  (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
          T < ∏ b, (if (f b || g b) = true then w b else 1)) ∧
        dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A *
            ∏ b, ∑ x, ∑ y, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b x y +
          lpBound m₀ blk M0 Clp ε' L A * (T ^ (-((1 : ℝ) / 4)) *
            ∏ b, ∑ x, ∑ y, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b x y *
              (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) +
          (queryLaw (fun (_ : E) => coordChain blockScale pr h)
            (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
            (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => ∑ f, r2 L A S Jq ω f)) ≤ remainder c L A)),
    FixMeanBound hcop D hpair z c u t r2 := by
  obtain ⟨C1, C71, hC1, hC71, hdcb, hchain⟩ := fixMeanBound_of_chain (a := a) (m₀ := m₀)
    (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε hε
  obtain ⟨Clp, hClp, hlp⟩ := fix_term_lp (a := a) (m₀ := m₀) (blk := blk) (p := p) (pr := pr)
    (h := h) (E := E) hcop ε' hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, ?_⟩
  intro D hpair z c u t r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hQ hR σ hσ hS1
    hterms
  apply hchain D hpair z c u t r2 ha hM0 hsc hp hinj hMod hcopM hz hu hQ hR hσ hS1
  have hL1 : ∀ᶠ L : ℕ in atTop, 1 ≤ L := eventually_ge_atTop 1
  filter_upwards [hterms, hsc, hL1] with L hL hscL hL1L
  intro C hC hk A hA hY S hS
  obtain ⟨w, T, hw, hT, hterm, hsum⟩ := hL C hC hk A hA hY S hS
  refine ⟨w, T, lpBound m₀ blk M0 Clp ε' L A, hw, hT, lpBound_nonneg m₀ blk M0 hClp.le ε' L A,
    ?_, hsum⟩
  intro Jq f g hg
  rcases hterm Jq f g hg with hch | hdir | hlg
  · exact Or.inl hch
  · exact Or.inr (Or.inl hdir)
  · exact Or.inr (Or.inr ⟨hlp D hpair u t hscL hL1L hM0 (hp L) (hinj L) hMod S Jq f g, hlg⟩)

end Sarkozy.DensityChain
