module

public import Sarkozy.BracketEnergy.FixAssembly
public import Sarkozy.DensityChain.Summation

@[expose] public section

/-!
# `EnvMeanBound` and `FixMeanBound` from per-term bounds and the summation

K2's fields 28–31 (`Sh.fixM.hmL/R`, `Sh.envM.hmL/R`) are B9's `FixMeanBound` and `EnvMeanBound`
(`BracketEnergy/FixAssembly.lean`, `BracketEnergy/Assembly.lean`). Each asks, at every least
counterexample of a large scale, a bound `ρ` on the residue-averaged excess of every term
`(f, g)` of the bracket expansion (`g ⊥ f`), and the summation
`E_𝒥 (∑_f ∑_{g ⊥ f} ρ + E_ω ∑_f r₂) ≤ c L^{-σ} α`.

The paper (proof of `lem:envelope-energy`, with `lem:bracket-energy`) bounds each term in one of
two ways:
* **chain-covered terms** (`q_{f∪g} ≤ N^τ`): `prop:record:density-structured` with
  `lem:record:density-dc`, averaged over the residues (B9's `env_first_mean_le`,
  `fix_first_mean_le`), gives `E_ω |E| ≤ (1 + u_L) K + ∏_{f∪g} ‖Λ_𝔟‖ C_dc L^{-σ} α`;
* **large unions** (`q_{f∪g} > N^τ`): `lem:record:density-lp` gives
  `E_ω |E| ≤ ∏_{f∪g} ‖Λ_𝔟‖ · B` with `B = C_ε N^ε α`, and Rankin's trick sums them.

This file proves the summation, so that fields 28–31 reduce to the per-term bounds and one
inequality between the constants:

* **`mean_excess_sum_le`** (abstract): if every term is chain-covered (excess at most
  `∏ G · R₁`) or large (excess at most `∏ G · B` and `T < ∏_{f ∪ g} w`), the index average of the
  summed excesses is at most `R₁ ∏_𝔟 ∑_{x,y} G + B T^{-1/4} ∏_𝔟 ∑_{x,y} G w^{[x∨y]/4}`
  (`sum_choice_prod_le`, `sum_choice_large_le`).
* **`envMeanBound_of_terms`**, **`fixMeanBound_of_terms`**: `EnvMeanBound` and `FixMeanBound`
  from these per-term bounds at the energies of `envC`, `fixC` and the constants inequality
  `R₁ Π + B T^{-1/4} Π_H + E_𝒥 E_ω ∑_f r₂ ≤ c L^{-σ} α`.

The per-term chain bound with `hdc` discharged is in `DensityChain.ChainTerms`.
-/

namespace Sarkozy.DensityChain

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic

/-- **The summation of the first bounds over the terms of the bracket expansion** (abstract form;
see the module docstring). Each term `(f, g)` with `g ⊥ f` at a depth vector of positive weight is
either chain-covered, `E_ω Eng ≤ (1 + z) K + ∏_𝔟 G · R₁`, or large,
`E_ω Eng − (1 + z) K ≤ ∏_𝔟 G · B` with `T < ∏_{𝔟 ∈ f ∪ g} w_𝔟`. -/
theorem mean_excess_sum_le {ι Θ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Θ] [Fintype Ω]
    (Pq : FiniteLaw Θ) (Pω : FiniteLaw Ω)
    (Eng : Θ → Ω → (ι → Bool) → (ι → Bool) → ℝ) (K : Θ → (ι → Bool) → (ι → Bool) → ℝ)
    (z : ℝ) (G : ι → Bool → Bool → ℝ) (hG : ∀ b x y, 0 ≤ G b x y) (w : ι → ℝ)
    (hw : ∀ b, 0 ≤ w b) {T R₁ B : ℝ} (hT : 0 < T) (hR₁ : 0 ≤ R₁) (hB : 0 ≤ B)
    (hterm : ∀ J, Pq.weight J ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
      Pω.expect (fun ω => Eng J ω f g) ≤ (1 + z) * K J f g + (∏ b, G b (f b) (g b)) * R₁ ∨
      (Pω.expect (fun ω => Eng J ω f g) - (1 + z) * K J f g ≤ (∏ b, G b (f b) (g b)) * B ∧
        T < ∏ b, (if (f b || g b) = true then w b else 1))) :
    Pq.expect (fun J => ∑ f, ∑ g ∈ validChoices f,
        Pω.expect (fun ω => Eng J ω f g - (1 + z) * K J f g)) ≤
      R₁ * ∏ b, ∑ x, ∑ y, G b x y +
        B * (T ^ (-((1 : ℝ) / 4)) *
          ∏ b, ∑ x, ∑ y, G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) := by
  classical
  refine le_trans (expect_le_of_support Pq _ (fun _ => R₁ * ∏ b, ∑ x, ∑ y, G b x y +
        B * (T ^ (-((1 : ℝ) / 4)) *
          ∏ b, ∑ x, ∑ y, G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1))) ?_)
    (le_of_eq (FiniteLaw.expect_const _ _))
  intro J hJ
  set NΛ : (ι → Bool) → (ι → Bool) → ℝ := fun f g => ∏ b, G b (f b) (g b) with hNΛ
  have hN0 : ∀ f g, 0 ≤ NΛ f g := fun f g => prod_nonneg fun b _ => hG _ _ _
  set X : (ι → Bool) → (ι → Bool) → ℝ := fun f g =>
    Pω.expect (fun ω => Eng J ω f g - (1 + z) * K J f g) with hX
  have hXe : ∀ f g, X f g = Pω.expect (fun ω => Eng J ω f g) - (1 + z) * K J f g := by
    intro f g
    simp only [hX]
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  set chain : (ι → Bool) → (ι → Bool) → Prop := fun f g =>
    Pω.expect (fun ω => Eng J ω f g) ≤ (1 + z) * K J f g + NΛ f g * R₁ with hchain
  have hsplit : ∀ f, ∑ g ∈ validChoices f, X f g ≤
      ∑ g ∈ validChoices f, NΛ f g * R₁ +
        ∑ g ∈ (validChoices f).filter (fun g => ¬ chain f g), NΛ f g * B := by
    intro f
    rw [← sum_filter_add_sum_filter_not (validChoices f) (chain f)]
    apply add_le_add
    · calc ∑ g ∈ (validChoices f).filter (chain f), X f g
          ≤ ∑ g ∈ (validChoices f).filter (chain f), NΛ f g * R₁ := by
            apply sum_le_sum
            intro g hg
            rw [mem_filter] at hg
            rw [hXe]
            have := hg.2
            simp only [hchain] at this
            linarith
        _ ≤ ∑ g ∈ validChoices f, NΛ f g * R₁ :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              fun g _ _ => mul_nonneg (hN0 f g) hR₁
    · apply sum_le_sum
      intro g hg
      rw [mem_filter] at hg
      rcases hterm J hJ f g hg.1 with h1 | h2
      · exact absurd h1 hg.2
      · rw [hXe]
        exact h2.1
  have hlarge : ∀ f, ∀ g ∈ (validChoices f).filter (fun g => ¬ chain f g),
      T < ∏ b, (if (f b || g b) = true then w b else 1) := by
    intro f g hg
    rw [mem_filter] at hg
    rcases hterm J hJ f g hg.1 with h1 | h2
    · exact absurd h1 hg.2
    · exact h2.2
  have hA := sum_choice_prod_le G hG validChoices
  have hB' := sum_choice_large_le G hG w hw hT
    (fun f => (validChoices f).filter (fun g => ¬ chain f g)) hlarge
  calc ∑ f, ∑ g ∈ validChoices f, X f g
      ≤ ∑ f, (∑ g ∈ validChoices f, NΛ f g * R₁ +
          ∑ g ∈ (validChoices f).filter (fun g => ¬ chain f g), NΛ f g * B) :=
        sum_le_sum fun f _ => hsplit f
    _ = R₁ * ∑ f, ∑ g ∈ validChoices f, NΛ f g +
          B * ∑ f, ∑ g ∈ (validChoices f).filter (fun g => ¬ chain f g), NΛ f g := by
        rw [sum_add_distrib, mul_sum, mul_sum]
        congr 1
        · apply sum_congr rfl; intro f _; rw [mul_sum]
          exact sum_congr rfl fun g _ => mul_comm _ _
        · apply sum_congr rfl; intro f _; rw [mul_sum]
          exact sum_congr rfl fun g _ => mul_comm _ _
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hA hR₁) (mul_le_mul_of_nonneg_left hB' hB)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The energy of the term `(f, g)` of one side of `envC` (the first summand of `envExcess`). -/
noncomputable def envTermEnergy (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b) (u : E → reservedCut.Half) (L : ℕ)
    (A : Finset ℤ) (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (f g : BlockAtom Bk J L → Bool) : ℝ :=
  |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
      if f b then Qb L b else if g b then recLaw D L b else muLaw D L b))
      (pairInputs u u (revealedInputCRT blk hcop D L A Jq) (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|

/-- The price of the term `(f, g)` of one side of `envC` (without the factor `1 + z`). -/
noncomputable def envTermPrice (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (price : ∀ L, BlockAtom Bk J L → ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (f g : BlockAtom Bk J L → Bool) : ℝ :=
  (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
    ∏ b, (if f b then price L b else 1)) * ∏ b, (if g b then D.GB.uprice L b else 1)

/-- **Fields 30–31 (`EnvMeanBound`, `Sh.envM.hmL/R`) from per-term bounds.** At every least
counterexample of a large scale there are per-atom weights `G` (in the application
`G 𝔟 x y = ‖Q_𝔟‖` if `x`, `‖Ñ_{0,𝔟} − μ_𝔟‖` if `y`, `1` otherwise), Rankin weights `w`, a threshold
`T` (`N^τ`), and constants `R₁` (`C_dc L^{-σ} α`) and `B` (`C_ε N^ε α`) such that every term of
positive weight is chain-covered or large (`mean_excess_sum_le`), and
`R₁ Π + B T^{-1/4} Π_H + E_𝒥 E_ω ∑_f r₂ ≤ c L^{-σ} α`. -/
theorem envMeanBound_of_terms (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : ∀ L, BlockAtom Bk J L → ℝ) (u : E → reservedCut.Half)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∃ (G : BlockAtom Bk J L → Bool → Bool → ℝ) (w : BlockAtom Bk J L → ℝ) (T R₁ B : ℝ),
        (∀ b x y, 0 ≤ G b x y) ∧ (∀ b, 0 ≤ w b) ∧ 0 < T ∧ 0 ≤ R₁ ∧ 0 ≤ B ∧
        (∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
          (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) ≤
            (1 + z L) * envTermPrice D price L A Jq f g + (∏ b, G b (f b) (g b)) * R₁ ∨
          ((FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) -
              (1 + z L) * envTermPrice D price L A Jq f g ≤ (∏ b, G b (f b) (g b)) * B ∧
            T < ∏ b, (if (f b || g b) = true then w b else 1))) ∧
        R₁ * ∏ b, ∑ x, ∑ y, G b x y +
          B * (T ^ (-((1 : ℝ) / 4)) *
            ∏ b, ∑ x, ∑ y, G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) +
          (queryLaw D.index.C D.index.t).expect (fun Jq =>
            (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
              (fun ω => ∑ f, r2 L A Jq ω f)) ≤ remainder c L A)) :
    EnvMeanBound hcop D hpair z c Qb price u r2 := by
  filter_upwards [hterms] with L hL
  intro C hC hk A hA hY
  obtain ⟨G, w, T, R₁, B, hG, hw, hT, hR₁, hB, hterm, hsum⟩ := hL C hC hk A hA hY
  set Pω := FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
  set Pq := queryLaw D.index.C D.index.t
  refine ⟨fun Jq f g => Pω.expect (fun ω => envExcess hcop D hpair z Qb price u L A Jq ω f g),
    fun _ _ _ _ _ => le_rfl, ?_⟩
  have hex : ∀ Jq ω f g, envExcess hcop D hpair z Qb price u L A Jq ω f g =
      envTermEnergy hcop D hpair Qb u L A Jq ω f g -
        (1 + z L) * envTermPrice D price L A Jq f g := by
    intro Jq ω f g
    unfold envExcess envTermEnergy envTermPrice
    ring
  have hmain := mean_excess_sum_le Pq Pω
    (fun Jq ω f g => envTermEnergy hcop D hpair Qb u L A Jq ω f g)
    (fun Jq f g => envTermPrice D price L A Jq f g) (z L) G hG w hw hT hR₁ hB hterm
  have hrw : (fun Jq => ∑ f, ∑ g ∈ validChoices f,
      Pω.expect (fun ω => envExcess hcop D hpair z Qb price u L A Jq ω f g)) =
      fun Jq => ∑ f, ∑ g ∈ validChoices f, Pω.expect (fun ω =>
        envTermEnergy hcop D hpair Qb u L A Jq ω f g -
          (1 + z L) * envTermPrice D price L A Jq f g) := by
    funext Jq
    exact sum_congr rfl fun f _ => sum_congr rfl fun g _ =>
      FiniteLaw.expect_congr _ fun ω => hex Jq ω f g
  rw [FiniteLaw.expect_add, hrw]
  linarith

/-- The energy of the term `(f, g)` of one side of `fixC` (the first summand of `fixExcess`). -/
noncomputable def fixTermEnergy (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (u : E → reservedCut.Half) (t : ZMod blockScale) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (f g : BlockAtom Bk J L → Bool) : ℝ :=
  |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
      if f b then TheoremCBlock.Structured.wrapInc D L b else
        if g b then recLaw D L b else muLaw D L b))
      (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
        (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
        (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)|

/-- The price of the term `(f, g)` of one side of `fixC` (without the factor `1 + z`). -/
noncomputable def fixTermPrice (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f g : BlockAtom Bk J L → Bool) : ℝ :=
  (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
    ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
    ∏ b, (if g b then D.GB.uprice L b else 1)

/-- **Fields 28–29 (`FixMeanBound`, `Sh.fixM.hmL/R`) from per-term bounds**, for every nonempty
set `𝒮` of active queries (as `envMeanBound_of_terms`). -/
theorem fixMeanBound_of_terms (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
    (r2 : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∃ (G : BlockAtom Bk J L → Bool → Bool → ℝ) (w : BlockAtom Bk J L → ℝ) (T R₁ B : ℝ),
        (∀ b x y, 0 ≤ G b x y) ∧ (∀ b, 0 ≤ w b) ∧ 0 < T ∧ 0 ≤ R₁ ∧ 0 ≤ B ∧
        (∀ Jq, ∀ f, ∀ g ∈ validChoices f,
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) ≤
            (1 + z L) * fixTermPrice D L A S Jq f g + (∏ b, G b (f b) (g b)) * R₁ ∨
          ((FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) -
              (1 + z L) * fixTermPrice D L A S Jq f g ≤ (∏ b, G b (f b) (g b)) * B ∧
            T < ∏ b, (if (f b || g b) = true then w b else 1))) ∧
        R₁ * ∏ b, ∑ x, ∑ y, G b x y +
          B * (T ^ (-((1 : ℝ) / 4)) *
            ∏ b, ∑ x, ∑ y, G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) +
          (queryLaw (fun (_ : E) => coordChain blockScale pr h)
            (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
            (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
              (fun ω => ∑ f, r2 L A S Jq ω f)) ≤ remainder c L A)) :
    FixMeanBound hcop D hpair z c u t r2 := by
  filter_upwards [hterms] with L hL
  intro C hC hk A hA hY S hS
  obtain ⟨G, w, T, R₁, B, hG, hw, hT, hR₁, hB, hterm, hsum⟩ := hL C hC hk A hA hY S hS
  set Pω := FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)
  set Pq := queryLaw (fun (_ : E) => coordChain blockScale pr h)
    (fun e => coordTails blockScale pr h (D.S.index.t e))
  refine ⟨fun Jq f g => Pω.expect (fun ω => fixExcess hcop D hpair z u t L A S Jq ω f g),
    fun _ _ _ _ => le_rfl, ?_⟩
  have hex : ∀ Jq ω f g, fixExcess hcop D hpair z u t L A S Jq ω f g =
      fixTermEnergy hcop D hpair u t L A S Jq ω f g -
        (1 + z L) * fixTermPrice D L A S Jq f g := by
    intro Jq ω f g
    unfold fixExcess fixTermEnergy fixTermPrice
    ring
  have hmain := mean_excess_sum_le Pq Pω
    (fun Jq ω f g => fixTermEnergy hcop D hpair u t L A S Jq ω f g)
    (fun Jq f g => fixTermPrice D L A S Jq f g) (z L) G hG w hw hT hR₁ hB
    (fun Jq _ f g hg => hterm Jq f g hg)
  have hrw : (fun Jq => ∑ f, ∑ g ∈ validChoices f,
      Pω.expect (fun ω => fixExcess hcop D hpair z u t L A S Jq ω f g)) =
      fun Jq => ∑ f, ∑ g ∈ validChoices f, Pω.expect (fun ω =>
        fixTermEnergy hcop D hpair u t L A S Jq ω f g -
          (1 + z L) * fixTermPrice D L A S Jq f g) := by
    funext Jq
    exact sum_congr rfl fun f _ => sum_congr rfl fun g _ =>
      FiniteLaw.expect_congr _ fun ω => hex Jq ω f g
  rw [FiniteLaw.expect_add, hrw]
  linarith

end Sarkozy.DensityChain
