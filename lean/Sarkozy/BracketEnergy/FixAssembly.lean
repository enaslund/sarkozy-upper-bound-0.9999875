module

public import Sarkozy.BracketEnergy.Assembly
public import Sarkozy.BracketEnergy.FixMean

@[expose] public section

/-!
# `fixC` from per-depth mean bounds

The fixed-interval analogue of `Assembly`: **`FixedBracketInputs.ofMeans`** builds the bracket
inputs of `fixC` from the sharp-first differences `hdiff` and, per side, mean bounds
`E_ω (|E_{f,g}(𝒮, 𝒥, ω)| − (1 + z) Π_𝒮 Y ∏_f u ∏_g u') ≤ ρ(𝒮, 𝒥, f, g)` with their summation
(`FixMeanBound`). `fix_first_mean_le` supplies `ρ = ∏ ‖Λ‖ C_dc L^{-σ} α` for the chain-covered
terms, at every depth vector (`mean_excess_le`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The first remainder of the minimal choice at fixed intervals. -/
noncomputable def fixExcess (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (f g : BlockAtom Bk J L → Bool) : ℝ :=
  |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
      if f b then TheoremCBlock.Structured.wrapInc D L b else
        if g b then recLaw D L b else muLaw D L b))
      (pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
        (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
        (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| -
    ((1 + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
      ∏ b, (if g b then D.GB.uprice L b else 1))

/-- The mean-bound hypothesis of one side of `FixedBracketInputs.ofMeans`. -/
def FixMeanBound (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
    (r2 : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∃ ρ : (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
        (BlockAtom Bk J L → Bool) → (BlockAtom Bk J L → Bool) → ℝ,
      (∀ Jq, ∀ f, ∀ g ∈ validChoices f,
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => fixExcess hcop D hpair z u t L A S Jq ω f g) ≤ ρ Jq f g) ∧
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        ∑ f, ∑ g ∈ validChoices f, ρ Jq f g +
          (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
            (fun ω => ∑ f, r2 L A S Jq ω f)) ≤ remainder c L A)

/-- The summation `hrem` of `fixC` from the mean bounds. -/
theorem fix_hrem_of_meanBound (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (c : ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
    (r2 : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (hm : FixMeanBound hcop D hpair z c u t r2) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, (∑ g ∈ validChoices f, fixExcess hcop D hpair z u t L A S Jq ω f g +
            r2 L A S Jq ω f))) ≤ remainder c L A) := by
  filter_upwards [hm] with L hL
  intro C hC hk A hA hY S hS
  obtain ⟨ρ, hρ, hsum⟩ := hL C hC hk A hA hY S hS
  refine le_trans ?_ hsum
  apply FiniteLaw.expect_mono
  intro Jq
  rw [expect_sum_sum]
  have h1 : ∑ f, ∑ g ∈ validChoices f,
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => fixExcess hcop D hpair z u t L A S Jq ω f g) ≤
      ∑ f, ∑ g ∈ validChoices f, ρ Jq f g :=
    sum_le_sum fun f _ => sum_le_sum fun g hg => hρ Jq f g hg
  linarith

/-- **`fixC`'s bracket inputs from per-depth mean bounds**: the first remainders are the
excesses (`fixExcess`), `hfirst` holds by definition and `hrem` follows from the mean bounds. -/
noncomputable def FixedBracketInputs.ofMeans (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) (c : ℝ) (hc : 0 ≤ c)
    (r2L r2R : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : BlockAtom Bk J L → Bool),
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
            (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
          multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
            (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
            r2L L A S Jq ω f))
    (hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : BlockAtom Bk J L → Bool),
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
            (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
          multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
            (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
            r2R L A S Jq ω f))
    (hmL : FixMeanBound hcop D hpair z c D.S.Q.u 0 r2L)
    (hmR : FixMeanBound hcop D hpair z c D.S.Q.w 1 r2R) :
    FixedBracketInputs hcop D hpair where
  z := z
  hz0 := hz0
  hzt := hzt
  c := c
  hc := hc
  r1L := fun L A S Jq ω f g => fixExcess hcop D hpair z D.S.Q.u 0 L A S Jq ω f g
  r1R := fun L A S Jq ω f g => fixExcess hcop D hpair z D.S.Q.w 1 L A S Jq ω f g
  r2L := r2L
  r2R := r2R
  hfirstL := Eventually.of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
    unfold fixExcess
    linarith
  hfirstR := Eventually.of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
    unfold fixExcess
    linarith
  hdiffL := hdiffL
  hdiffR := hdiffR
  hremL := fix_hrem_of_meanBound hcop D hpair z c D.S.Q.u 0 r2L hmL
  hremR := fix_hrem_of_meanBound hcop D hpair z c D.S.Q.w 1 r2R hmR

end Sarkozy.BracketEnergy
