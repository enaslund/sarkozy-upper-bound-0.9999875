module

public import Sarkozy.BracketEnergy.EnvMean

@[expose] public section

/-!
# `envC` from per-depth mean bounds

`EnvelopeBracketInputs` (and through `toCRT` B5's `envC`) asks per-index first bounds `hfirst`
with signed remainders and their summation `hrem`. The paper bounds each term at a fixed depth
vector **after** the average over the residues. This file builds the bundle from such averaged
bounds, which is the form `env_first_mean_le` proves from the chain:

* `queryLaw_weight_eq_zero`: depth vectors that do not reveal some interval coordinate have
  weight `0` (its tail is `Tails.bernoulli 1`);
* `expect_le_of_support`: an expectation inequality needs the pointwise one only on the support;
* **`EnvelopeBracketInputs.ofMeans`**: the bundle from, per side and per scale, mean bounds
  `E_ω (|E_{f,g}(𝒥, ω)| − (1 + z) Π_𝒥 Y ∏_f u ∏_g u') ≤ ρ(𝒥, f, g)` at the depth vectors of
  positive weight, and the summation `E_𝒥 (∑_f ∑_{g ⊥ f} ρ + E_ω ∑_f r₂) ≤ c L^{-σ} α`.
  The first remainders are `r₁ = |E| − (1 + z) Π Y ∏ u ∏ u'`.

With `env_first_mean_le` (all slots changed) and `env_first_mean_le_query` (query slots only), a
term `(f, g)` whose selected moduli satisfy the chain's conditions has
`ρ = ∏_{f∪g} ‖Λ_𝔟‖ C_dc L^{-σ} α` for `z ≥ u_L`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic

/-- An expectation inequality from the pointwise inequality on the support. -/
theorem expect_le_of_support {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (F G : Ω → ℝ)
    (h : ∀ ω, P.weight ω ≠ 0 → F ω ≤ G ω) : P.expect F ≤ P.expect G := by
  unfold FiniteLaw.expect
  apply sum_le_sum
  intro ω _
  by_cases hw : P.weight ω = 0
  · rw [hw, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h ω hw) (P.nonneg ω)

/-- The expectation of a double sum plus a sum. -/
theorem expect_sum_sum {Ω I : Type*} [Fintype Ω] (P : FiniteLaw Ω) (s : Finset I)
    {K : I → Type*} (t : ∀ i, Finset (K i)) (X : Ω → ∀ i, K i → ℝ) (Y : Ω → I → ℝ) :
    P.expect (fun ω => ∑ i ∈ s, (∑ k ∈ t i, X ω i k + Y ω i)) =
      ∑ i ∈ s, ∑ k ∈ t i, P.expect (fun ω => X ω i k) + P.expect (fun ω => ∑ i ∈ s, Y ω i) := by
  unfold FiniteLaw.expect
  simp only [sum_add_distrib, mul_add, mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  exact sum_comm

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Depth vectors that do not reveal an interval have weight `0`**: the interval coordinate
has the tail `Tails.bernoulli 1`, so its depth is `1` almost surely. -/
theorem queryLaw_weight_eq_zero (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) (e : E)
    (hJ : (Jq e none : ℕ) = 0) : (queryLaw D.index.C D.index.t).weight Jq = 0 := by
  unfold queryLaw IndexSupport.depthLaw
  change (∏ e', ∏ j, (D.index.t e' j).law.weight (Jq e' j)) = 0
  apply prod_eq_zero (mem_univ e)
  apply prod_eq_zero (mem_univ none)
  have h0 : Jq e none = 0 := Fin.ext hJ
  rw [h0]
  change (Tails.bernoulli 1 zero_le_one le_rfl).ext 0 -
    (Tails.bernoulli 1 zero_le_one le_rfl).ext (0 + 1) = 0
  simp [Tails.ext, Tails.bernoulli]

/-- The first remainder of the minimal choice: `|E| − (1 + z) Π Y ∏_f u ∏_g u'`. -/
noncomputable def envExcess (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : ∀ L, BlockAtom Bk J L → ℝ) (u : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (f g : BlockAtom Bk J L → Bool) : ℝ :=
  |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
      if f b then Qb L b else if g b then recLaw D L b else muLaw D L b))
      (pairInputs u u (revealedInputCRT blk hcop D L A Jq) (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| -
    ((1 + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
      ∏ b, (if f b then price L b else 1)) * ∏ b, (if g b then D.GB.uprice L b else 1))

/-- The mean-bound hypothesis of one side of `ofMeans`. -/
def EnvMeanBound (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : ∀ L, BlockAtom Bk J L → ℝ) (u : E → reservedCut.Half)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∃ ρ : (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
        (BlockAtom Bk J L → Bool) → (BlockAtom Bk J L → Bool) → ℝ,
      (∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => envExcess hcop D hpair z Qb price u L A Jq ω f g) ≤ ρ Jq f g) ∧
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        ∑ f, ∑ g ∈ validChoices f, ρ Jq f g +
          (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
            (fun ω => ∑ f, r2 L A Jq ω f)) ≤ remainder c L A)

/-- The summation `hrem` from the mean bounds. -/
theorem hrem_of_meanBound (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : ∀ L, BlockAtom Bk J L → ℝ) (u : E → reservedCut.Half)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (hm : EnvMeanBound hcop D hpair z c Qb price u r2) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, (∑ g ∈ validChoices f, envExcess hcop D hpair z Qb price u L A Jq ω f g +
            r2 L A Jq ω f))) ≤ remainder c L A) := by
  filter_upwards [hm] with L hL
  intro C hC hk A hA hY
  obtain ⟨ρ, hρ, hsum⟩ := hL C hC hk A hA hY
  refine le_trans ?_ hsum
  apply expect_le_of_support
  intro Jq hJq
  rw [expect_sum_sum]
  have h1 : ∑ f, ∑ g ∈ validChoices f,
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => envExcess hcop D hpair z Qb price u L A Jq ω f g) ≤
      ∑ f, ∑ g ∈ validChoices f, ρ Jq f g :=
    sum_le_sum fun f _ => sum_le_sum fun g hg => hρ Jq hJq f g hg
  linarith

/-- **`envC`'s bracket inputs from per-depth mean bounds**: the first remainders are the
excesses `|E| − (1 + z) Π Y ∏ u ∏ u'` (`envExcess`), so `hfirst` holds by definition, and `hrem`
follows from the mean bounds (`hrem_of_meanBound`). -/
noncomputable def EnvelopeBracketInputs.ofMeans (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) (c : ℝ) (hc : 0 ≤ c)
    (r2L r2R : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
            (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
          multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N₀ L b))
            (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) +
            r2L L A Jq ω f))
    (hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
            (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
          multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N₀ L b))
            (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) +
            r2R L A Jq ω f))
    (hmL : EnvMeanBound hcop D hpair z c (fun L => TheoremCBlock.Structured.envIncL D L)
      (fun L => TheoremCBlock.Structured.envPriceL D L) D.index.u r2L)
    (hmR : EnvMeanBound hcop D hpair z c (fun L => TheoremCBlock.Structured.envIncR D L)
      (fun L => TheoremCBlock.Structured.envPriceR D L) D.index.w r2R) :
    EnvelopeBracketInputs hcop D hpair where
  z := z
  hz0 := hz0
  hzt := hzt
  c := c
  hc := hc
  r1L := fun L A Jq ω f g => envExcess hcop D hpair z
    (fun L => TheoremCBlock.Structured.envIncL D L)
    (fun L => TheoremCBlock.Structured.envPriceL D L) D.index.u L A Jq ω f g
  r1R := fun L A Jq ω f g => envExcess hcop D hpair z
    (fun L => TheoremCBlock.Structured.envIncR D L)
    (fun L => TheoremCBlock.Structured.envPriceR D L) D.index.w L A Jq ω f g
  r2L := r2L
  r2R := r2R
  hfirstL := Eventually.of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ => by
    unfold envExcess
    linarith
  hfirstR := Eventually.of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ => by
    unfold envExcess
    linarith
  hdiffL := hdiffL
  hdiffR := hdiffR
  hremL := hrem_of_meanBound hcop D hpair z c _ _ D.index.u r2L hmL
  hremR := hrem_of_meanBound hcop D hpair z c _ _ D.index.w r2R hmR

/-- **From the chain's mean bound to the mean-bound hypothesis**: if `E_ω |E| ≤ (1 + u) K + ρ`
(`env_first_mean_le`, with `K = Π_𝒥 Y ∏ u ∏ u'`) and `z ≥ u`, `K ≥ 0`, then the mean excess
`E_ω (|E| − (1 + z) K)` is at most `ρ`. -/
theorem mean_excess_le {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (F : Ω → ℝ) {u z K ρ : ℝ}
    (hzu : u ≤ z) (hK : 0 ≤ K) (h : P.expect F ≤ (1 + u) * K + ρ) :
    P.expect (fun ω => F ω - (1 + z) * K) ≤ ρ := by
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  nlinarith

end Sarkozy.BracketEnergy
