module

public import Sarkozy.DensityChain.EnvChain

@[expose] public section

/-!
# Fields 28–29: `FixMeanBound` from the density chain

**`fixMeanBound_of_chain`** proves B9's `FixMeanBound` (K2's fields 28–29, `Sh.fixM.hmL/R`) for one
side of `fixC`, for every nonempty set `𝒮` of active queries, in the same form as
`envMeanBound_of_chain` (`DensityChain.EnvChain`): per-term chain inputs (`FixChainTerm`) with
`lem:record:density-dc` and condition (b) (`isPositiveRecord_wrapInc`) discharged by
`density_dc_block` through `fix_term_chain`, or a direct first bound (the `μ`-term), or a bound
of the form of `lem:record:density-lp`; the summation is
proved; one inequality between the constants remains per counterexample. At fixed intervals the
price of an active query is `K^{2ϑ/72}` times its conductor price (`fixedPrice`, B9's
`fix_first_mean_le`), and every depth vector is allowed.
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

/-- **The per-term inputs of a chain-covered term of `fixC`** (as `EnvChainTerm`, with the slot
data `fixSlots` of the active queries `𝒮` at the fixed interval `t`). -/
def FixChainTerm (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {L : ℕ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (u : E → reservedCut.Half) (Qcl : ℕ)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f g : BlockAtom Bk J L → Bool) : Prop :=
  (∃ qE cE : ℕ, ∏ b ∈ termSet f g, crtModuli m₀ blk p L b = qE * cE ∧ Squarefree qE ∧
    IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ Qcl ∧ qE.Coprime cE ∧
    (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau) ∧
  ∏ j ∈ termSet f g, crtModuli m₀ blk p L j ≠ 1 ∧
  (∀ ω v, ∀ B : Finset ℤ,
    B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
      (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1 : ℕ) : ℤ) →
    referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (child (crtModuli m₀ blk p L) (termSet f g)
          (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
            (fixSlots hcop u L S t Jq ω v).1 (fixSlots hcop u L S t Jq ω v).2.2.1)) B
          (blockScale * stepEll (crtModuli m₀ blk p L)
          (termSet f g) (fixSlots hcop u L S t Jq ω v).1
          (fixSlots hcop u L S t Jq ω v).2.2.1)) ≤
      D.Y (stepEll (crtModuli m₀ blk p L) (termSet f g) (fixSlots hcop u L S t Jq ω v).1
        (fixSlots hcop u L S t Jq ω v).2.2.1) B) ∧
  (∀ b ∈ termSet f g,
    ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f g b)),
    MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)

/-- **Fields 28–29: `FixMeanBound` from the density chain** (see the module docstring). -/
theorem fixMeanBound_of_chain (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧ DCBlockProp ε C1 C71 ∧
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
      ∃ (w : BlockAtom Bk J L → ℝ) (T B : ℝ), (∀ b, 0 ≤ w b) ∧ 0 < T ∧ 0 ≤ B ∧
        (∀ Jq, ∀ f, ∀ g ∈ validChoices f,
          FixChainTerm hcop D (hpair L) (TheoremCBlock.Structured.wrapInc D L) u Qcl S t Jq f g ∨
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) ≤
            (1 + z L) * fixTermPrice D L A S Jq f g +
              (∏ b, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b (f b) (g b)) *
                (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                  (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                  (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
          ((FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) ≤
              (∏ b, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b (f b) (g b)) * B ∧
            T < ∏ b, (if (f b || g b) = true then w b else 1))) ∧
        dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A *
            ∏ b, ∑ x, ∑ y, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b x y +
          B * (T ^ (-((1 : ℝ) / 4)) *
            ∏ b, ∑ x, ∑ y, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b x y *
              (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) +
          (queryLaw (fun (_ : E) => coordChain blockScale pr h)
            (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
            (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => ∑ f, r2 L A S Jq ω f)) ≤ remainder c L A)),
    FixMeanBound hcop D hpair z c u t r2 := by
  obtain ⟨C1, C71, hC1, hC71, hdcb, hchain⟩ := fix_term_chain (a := a) (m₀ := m₀) (blk := blk)
    (p := p)
    (pr := pr) (h := h) (E := E) hcop ε hε
  refine ⟨C1, C71, hC1, hC71, hdcb, ?_⟩
  intro D hpair z c u t r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hQ hR σ hσ hS1
    hterms
  apply fixMeanBound_of_terms
  have hL2 : ∀ᶠ L : ℕ in atTop, 2 ≤ L := eventually_ge_atTop 2
  filter_upwards [hterms, hsc, hz, hL2] with L hL hscL hzL hL2L
  intro C hC hk A hA hY S hS
  obtain ⟨w, T, B, hw, hT, hB, hterm, hsum⟩ := hL C hC hk A hA hY S hS
  set Cdc := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 with hCdc
  have hCdc0 : 0 ≤ Cdc := dcConstant_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC1.le
    hC71.le
  have hα := density_nonneg (blockScale * L) A
  have hR₁ : 0 ≤ Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg hCdc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hα
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hθ := densityExponent_facts
  have hY0 : D.Y L ∅ ≤ 0 := by
    rw [dataY_empty D L]
  have hYpos : 0 ≤ D.Y L A := le_trans (by
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)) hcex.lower.le
  have hz0 : 0 ≤ z L := (scaleU_nonneg _ _ _ _ _).trans hzL
  refine ⟨termWeight D L (TheoremCBlock.Structured.wrapInc D L), w, T,
    Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A, B,
    termWeight_nonneg D L _, hw, hT, hR₁, hB, ?_, ?_⟩
  · intro Jq f g hg
    have hK : 0 ≤ fixTermPrice D L A S Jq f g := by
      unfold fixTermPrice
      apply mul_nonneg (mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ _ _) hYpos)
        (prod_nonneg fun b _ => by
          split_ifs
          exacts [TheoremCBlock.Structured.wrapPrice_nonneg D L b, zero_le_one]))
      exact prod_nonneg fun b _ => by
        split_ifs
        exacts [TheoremCBlock.Structured.uprice_nonneg D L b, zero_le_one]
    rcases hterm Jq f g hg with hch | hdir | hlg
    · left
      obtain ⟨⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩, hne, hrest, hatom⟩ := hch
      have key := hchain D (hpair L) hcex hθ.1 hθ.2 rfl ha (zero_le_one.trans hC) hL2L hY0 hscL
        hM0 (hp L) (hinj L) (TheoremCBlock.Structured.wrapInc D L) f g hg hDE hqE hcE hcE0 hcQ
        hcopE hqN S t Jq u hu hMod (hcopM L) hne
        (hsel_of_positive D L (prefix_pairwise (hpair L)) _ (isPositiveRecord_wrapInc D L) f g)
        hσ hS1 hrest hatom
        (TheoremCBlock.Structured.wrapPrice D L) (hQ L) (hR L)
      have hprice_eq : fixedPrice pr h (2 * a / 72) S Jq * D.Y L A *
          ((∏ b, if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) *
            ∏ b, (if g b then D.GB.uprice L b else 1)) =
          fixTermPrice D L A S Jq f g := by
        unfold fixTermPrice EnvelopeInputsBlock.priceExponent
        ring
      rw [hprice_eq] at key
      have hmono : (1 + scaleU blockScale M0 Qcl stageTau L) * fixTermPrice D L A S Jq f g ≤
          (1 + z L) * fixTermPrice D L A S Jq f g :=
        mul_le_mul_of_nonneg_right (by linarith) hK
      refine le_trans key ?_
      linarith [hmono]
    · left
      refine hdir.trans (le_of_eq ?_)
      ring
    · right
      refine ⟨?_, hlg.2⟩
      have h1 : 0 ≤ (1 + z L) * fixTermPrice D L A S Jq f g :=
        mul_nonneg (by linarith) hK
      linarith [hlg.1]
  · refine le_trans (le_of_eq ?_) hsum
    ring

end Sarkozy.DensityChain
