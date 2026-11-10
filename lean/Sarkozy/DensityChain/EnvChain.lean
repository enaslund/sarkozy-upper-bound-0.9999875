module

public import Sarkozy.DensityChain.ChainTerms
public import Sarkozy.DensityChain.Records

@[expose] public section

/-!
# Fields 30–31: `EnvMeanBound` from the density chain

**`envMeanBound_of_chain`** proves B9's `EnvMeanBound` (K2's fields 30–31, `Sh.envM.hmL/R`) for one
side of `envC` from:

* the chain's per-term inputs of every chain-covered term (`EnvChainTerm`: the modulus conditions
  of `def:record:structured-energy` on `D_{f∪g}`, `D_{f∪g} ≠ 1`, restoration `hrest` at the
  paper's child cutoffs, and the moments `hatom` of the selected laws).
  **`lem:record:density-dc` is not an input**: it is `density_dc_block`, through
  `env_term_chain`. **Condition (b) is not an input either**: it follows from the increments
  being positive records (`hQpos`; for the data's `envIncL`, `envIncR` this is
  `isPositiveRecord_envIncL`, `_envIncR`) by `hsel_of_positive`;
* for the remaining terms either a direct first bound of the chain's form (the `μ`-term
  `f = g = ∅`, covered by B9's `env_first_mean_le_query` with `hun`) or a bound of the form of
  `lem:record:density-lp` (`E_ω |E| ≤ ∏_{f∪g} ‖Λ_𝔟‖ · B` and `T < ∏_{f∪g} w_𝔟`);
* the frame facts (prime distinct tail moduli, `ScaleConditionsAt`, the index modulus divides
  `M₀` and is coprime to the atom moduli, `u_L ≤ z_L`), the price inequalities of the selected
  laws (`‖Q_𝔟‖ sq(D_𝔟)^a ≤ u_𝔟`, `‖Ñ₀ − μ‖ sq(D_𝔟)^a ≤ u'_𝔟`), (S1) for `σ`;
* **one inequality between the constants** at each counterexample:
  `C_dc L^{-σ} α ∏_𝔟 ∑_{x,y} G + B T^{-1/4} ∏_𝔟 ∑_{x,y} G w^{[x∨y]/4} + E_𝒥 E_ω ∑_f r₂ ≤
  c L^{-1/825} α`, with `G = termWeight` (`‖Q_𝔟‖, ‖Ñ₀ − μ‖, 1`). Its products are bounded by
  `exp(2∑‖Q‖ + ∑‖Ñ₀ − μ‖)` and the `w^{1/4}`-weighted version (`prod_one_add_le_exp`), i.e. by
  the summability (c) of `def:cp8` the paper uses for `Π_H`.

The summation over the terms is proved (`mean_excess_sum_le`); the constant `C_dc` is uniform.
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

/-- **The per-term inputs of a chain-covered term of `envC`** (`def:record:structured-energy`,
`prop:record:density-structured`): the modulus conditions on `D_{f∪g} = q_E c_E` (`q_E`
squarefree, `q_E ≤ N^τ`, `c_E` a nonzero square `≤ Q_cl`, coprime), `D_{f∪g} ≠ 1`, restoration
at the child scales with the paper's cutoffs (`lem:record:fibre-scale`(c),(d)), and the unit
mixed `L^{72/ϑ}` moments of the selected laws (`lem:density:coupled`, `lem:density:packets`). -/
def EnvChainTerm (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {L : ℕ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (u : E → reservedCut.Half) (Qcl : ℕ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (f g : BlockAtom Bk J L → Bool) : Prop :=
  (∃ qE cE : ℕ, ∏ b ∈ termSet f g, crtModuli m₀ blk p L b = qE * cE ∧ Squarefree qE ∧
    IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ Qcl ∧ qE.Coprime cE ∧
    (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau) ∧
  ∏ j ∈ termSet f g, crtModuli m₀ blk p L j ≠ 1 ∧
  (∀ ω v, ∀ B : Finset ℤ,
    B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
      (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1 : ℕ) : ℤ) →
    referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
        (child (crtModuli m₀ blk p L) (termSet f g)
          (paperCutoff (blockScale * stepEll (crtModuli m₀ blk p L) (termSet f g)
            (envSlots hcop u L Jq ω v).1 (envSlots hcop u L Jq ω v).2.2.1)) B
          (blockScale * stepEll (crtModuli m₀ blk p L)
          (termSet f g) (envSlots hcop u L Jq ω v).1
          (envSlots hcop u L Jq ω v).2.2.1)) ≤
      D.Y (stepEll (crtModuli m₀ blk p L) (termSet f g) (envSlots hcop u L Jq ω v).1
        (envSlots hcop u L Jq ω v).2.2.1) B) ∧
  (∀ b ∈ termSet f g,
    ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f g b)),
    MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)

theorem densityExponent_facts : 0 < densityExponent ∧ 2 * (densityExponent / 72) ≤ 1 := by
  unfold densityExponent
  constructor <;> norm_num

omit [DecidableEq P] in
/-- The reference energy of the empty set vanishes. -/
theorem dataY_empty (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) :
    D.Y L ∅ = 0 := by
  unfold TheoremCBlock.ComparisonData.Y
  rw [energyFirst_eq_diagonalIntegral]
  have h0 : blockLift m₀ blk p L ∅ = fun _ => 0 := by
    funext x
    simp [blockLift, atomLift, wholeLift, lift, liftOn, intervalCoeff, indicator]
  rw [h0]
  unfold diagonalIntegral multilinearIntegral
  have h1 : (fun z : Slot → ∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b =>
      ∏ _v : Slot, (fun _ => (0 : ℝ)) (z _v)) = 0 := by
    funext z
    simp
  rw [h1, map_zero]

/-- **Fields 30–31: `EnvMeanBound` from the density chain** (see the module docstring). -/
theorem envMeanBound_of_chain (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧ DCBlockProp ε C1 C71 ∧
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
      ∃ (w : BlockAtom Bk J L → ℝ) (T B : ℝ), (∀ b, 0 ≤ w b) ∧ 0 < T ∧ 0 ≤ B ∧
        (∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
          EnvChainTerm hcop D (hpair L) (Qb L) u Qcl Jq f g ∨
          (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) ≤
            (1 + z L) * envTermPrice D price L A Jq f g +
              (∏ b, termWeight D L (Qb L) b (f b) (g b)) *
                (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                  (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                  (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
          ((FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) ≤
              (∏ b, termWeight D L (Qb L) b (f b) (g b)) * B ∧
            T < ∏ b, (if (f b || g b) = true then w b else 1))) ∧
        dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A *
            ∏ b, ∑ x, ∑ y, termWeight D L (Qb L) b x y +
          B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, ∑ x, ∑ y, termWeight D L (Qb L) b x y *
            (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) +
          (queryLaw D.index.C D.index.t).expect (fun Jq =>
            (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => ∑ f, r2 L A Jq ω f)) ≤ remainder c L A)),
    EnvMeanBound hcop D hpair z c Qb price u r2 := by
  obtain ⟨C1, C71, hC1, hC71, hdcb, hchain⟩ := env_term_chain (a := a) (m₀ := m₀) (blk := blk)
    (p := p)
    (pr := pr) (h := h) (E := E) hcop ε hε
  refine ⟨C1, C71, hC1, hC71, hdcb, ?_⟩
  intro D hpair z c Qb price u r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hprice
    hQpos hQ hR σ hσ hS1 hterms
  apply envMeanBound_of_terms
  have hL2 : ∀ᶠ L : ℕ in atTop, 2 ≤ L := eventually_ge_atTop 2
  filter_upwards [hterms, hsc, hz, hL2] with L hL hscL hzL hL2L
  intro C hC hk A hA hY
  obtain ⟨w, T, B, hw, hT, hB, hterm, hsum⟩ := hL C hC hk A hA hY
  set Cdc := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 with hCdc
  have hCdc0 : 0 ≤ Cdc := dcConstant_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) hC1.le
    hC71.le
  have hα := density_nonneg (blockScale * L) A
  have hR₁ : 0 ≤ Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg hCdc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hα
  -- the least counterexample
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hθ := densityExponent_facts
  have hY0 : D.Y L ∅ ≤ 0 := by
    rw [dataY_empty D L]
  have hYpos : 0 ≤ D.Y L A := le_trans (by
    exact mul_nonneg (mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)) hcex.lower.le
  have hz0 : 0 ≤ z L := (scaleU_nonneg _ _ _ _ _).trans hzL
  refine ⟨termWeight D L (Qb L), w, T, Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A, B,
    termWeight_nonneg D L (Qb L), hw, hT, hR₁, hB, ?_, ?_⟩
  · intro Jq hJq f g hg
    have hK : 0 ≤ envTermPrice D price L A Jq f g := by
      unfold envTermPrice
      apply mul_nonneg (mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ _) hYpos)
        (prod_nonneg fun b _ => by split_ifs; exacts [hprice L b, zero_le_one]))
      exact prod_nonneg fun b _ => by
        split_ifs
        exacts [TheoremCBlock.Structured.uprice_nonneg D L b, zero_le_one]
    rcases hterm Jq hJq f g hg with hch | hdir | hlg
    · left
      obtain ⟨⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩, hne, hrest, hatom⟩ := hch
      have hJ : ∀ e, (Jq e none : ℕ) ≠ 0 := by
        intro e h0
        exact hJq (queryLaw_weight_eq_zero D Jq e h0)
      have key := hchain D (hpair L) hcex hθ.1 hθ.2 ha (zero_le_one.trans hC) hL2L hY0 hscL
        hM0 (hp L) (hinj L) (Qb L) f g hg hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ u hu hMod
        (hcopM L) hne (hsel_of_positive D L (prefix_pairwise (hpair L)) (Qb L) (hQpos L) f g)
        hσ hS1 hrest hatom (price L) (hQ L) (hR L)
      have hprice_eq : conductorPrice pr h (2 * a / 72) Jq * D.Y L A *
          ((∏ b, if f b then price L b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1)) =
          envTermPrice D price L A Jq f g := by
        unfold envTermPrice EnvelopeInputsBlock.priceExponent
        ring
      rw [hprice_eq] at key
      have hmono : (1 + scaleU blockScale M0 Qcl stageTau L) * envTermPrice D price L A Jq f g ≤
          (1 + z L) * envTermPrice D price L A Jq f g :=
        mul_le_mul_of_nonneg_right (by linarith) hK
      refine le_trans key ?_
      linarith [hmono]
    · left
      refine hdir.trans (le_of_eq ?_)
      ring
    · right
      refine ⟨?_, hlg.2⟩
      have h1 : 0 ≤ (1 + z L) * envTermPrice D price L A Jq f g :=
        mul_nonneg (by linarith) hK
      linarith [hlg.1]
  · refine le_trans (le_of_eq ?_) hsum
    ring

end Sarkozy.DensityChain
