module

public import Sarkozy.DensityFibre.SharpDiff
public import Sarkozy.DensityFibre.ChoiceExpansion

@[expose] public section

/-!
# The four sharp-first differences from the per-term coupled bounds

K2's fields `Sh.fixM.hdiffL/R` (26–27) and `Sh.envM.hdiffL/R` (30–31), from **per-term** bounds
of the coupled expansion (`DensityFibre.ChoiceExpansion`). For every nonempty choice `σ`, tag `j`
and piece choice `φ` with nonzero coefficients, the hypothesis is
`|E_φ| ≤ (∏_𝔟 g_{φ_𝔟})(1 + ε_L) K Y + r_φ` with `r_φ ≥ 0`. This is `lem:density:coupled` for one
term,
with the revealed inputs of the bundle, used as hypothesis. The field's remainder is then
`r₂ = ∑_{σ ≠ ∅} ∑_j ∑_φ ∏|c| r_φ`, and its `z` is any `z_L ≥ R_err ε_L`.

Chain: per-term bound → `choice_bound_all_tags` (expansion and weights) →
`*_of_choices` (B9's `diff_bound_of_coupled`, the tag series with the data's `R_err`) → field.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame Sarkozy.RecordExpansion
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

/-- **K2's field `Sh.envM.hdiffL` from the per-term coupled bounds** (`envC`, source side;
`lem:sharp-first` with `lem:density:coupled` for one term with revealed inputs as hypothesis
`hterm`, nonnegative remainders `rt`, relative error `ε_L` with `z_L ≥ R_err ε_L`). -/
theorem envHdiffL_of_terms (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (rt : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (σ : ∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, HPiece D L b) → ℝ)
    (hrt0 : ∀ L A Jq ω f σ j φ, 0 ≤ rt L A Jq ω f σ j φ)
    (hterm : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∀ φ : (∀ b, HPiece D L b), (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            hpieceK D L (TheoremCBlock.Structured.envIncL D L) b (φ b)))
          (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (∏ b, hpieceG D L b (φ b)) * ((1 + ε L) * (conductorPrice pr h
              (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))) + rt L A Jq ω f σ
                j φ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
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
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ j', ∑ φ : (∀ b, HPiece D L b),
                (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A Jq ω f σ j' φ) := by
  refine envHdiffL_of_choices hcop D hpair z ε hε hz (fun L A Jq ω f σ => ∑ j', ∑ φ : (∀ b, HPiece
      D L b),
      (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A Jq ω f σ j' φ) ?_
  filter_upwards [hterm] with L hL
  intro C hC hind A hA hY Jq ω f σ hσ0 j hj
  have hK : 0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) :=
    mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
        · exact zero_le_one)
  exact choice_bound_all_tags blk D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.envIncL D L) f σ _ (mul_nonneg (by linarith [hε L]) hK) _ (fun j' φ
        => hrt0 _ _ _ _ _ _ j' φ) j
    (fun φ hφ => hL C hC hind A hA hY Jq ω f σ hσ0 j hj φ hφ)

/-- **K2's field `Sh.envM.hdiffR` from the per-term coupled bounds** (`envC`, target side;
`lem:sharp-first` with `lem:density:coupled` for one term with revealed inputs as hypothesis
`hterm`, nonnegative remainders `rt`, relative error `ε_L` with `z_L ≥ R_err ε_L`). -/
theorem envHdiffR_of_terms (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (rt : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (σ : ∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, HPiece D L b) → ℝ)
    (hrt0 : ∀ L A Jq ω f σ j φ, 0 ≤ rt L A Jq ω f σ j φ)
    (hterm : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∀ φ : (∀ b, HPiece D L b), (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            hpieceK D L (TheoremCBlock.Structured.envIncR D L) b (φ b)))
          (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (∏ b, hpieceG D L b (φ b)) * ((1 + ε L) * (conductorPrice pr h
              (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1))) + rt L A Jq ω f σ
                j φ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
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
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ j', ∑ φ : (∀ b, HPiece D L b),
                (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A Jq ω f σ j' φ) := by
  refine envHdiffR_of_choices hcop D hpair z ε hε hz (fun L A Jq ω f σ => ∑ j', ∑ φ : (∀ b, HPiece
      D L b),
      (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A Jq ω f σ j' φ) ?_
  filter_upwards [hterm] with L hL
  intro C hC hind A hA hY Jq ω f σ hσ0 j hj
  have hK : 0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) :=
    mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
        · exact zero_le_one)
  exact choice_bound_all_tags blk D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.envIncR D L) f σ _ (mul_nonneg (by linarith [hε L]) hK) _ (fun j' φ
        => hrt0 _ _ _ _ _ _ j' φ) j
    (fun φ hφ => hL C hC hind A hA hY Jq ω f σ hσ0 j hj φ hφ)

/-- **K2's field `Sh.fixM.hdiffL` from the per-term coupled bounds** (`fixC`, source side;
`lem:sharp-first` with `lem:density:coupled` for one term with revealed inputs as hypothesis
`hterm`, nonnegative remainders `rt`, relative error `ε_L` with `z_L ≥ R_err ε_L`). -/
theorem fixHdiffL_of_terms (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (rt : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (σ : ∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, HPiece D L b) → ℝ)
    (hrt0 : ∀ L A S Jq ω f σ j φ, 0 ≤ rt L A S Jq ω f σ j φ)
    (hterm : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option
          (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∀ φ : (∀ b, HPiece D L b), (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            hpieceK D L (TheoremCBlock.Structured.wrapInc D L) b (φ b)))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (∏ b, hpieceG D L b (φ b)) * ((1 + ε L) * (fixedPrice pr h
              (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))) + rt L A S Jq ω f
                σ j φ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
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
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            ∑ j', ∑ φ : (∀ b, HPiece D L b),
                (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A S Jq ω f σ j' φ) := by
  refine fixHdiffL_of_choices hcop D hpair z ε hε hz (fun L A S Jq ω f σ => ∑ j', ∑ φ : (∀ b,
      HPiece D L b),
      (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A S Jq ω f σ j' φ) ?_
  filter_upwards [hterm] with L hL
  intro C hC hind A hA hY S hS Jq ω f σ hσ0 j hj
  have hK : 0 ≤ fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) :=
    mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one)
  exact choice_bound_all_tags blk D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.wrapInc D L) f σ _ (mul_nonneg (by linarith [hε L]) hK) _ (fun j' φ
        => hrt0 _ _ _ _ _ _ _ j' φ) j
    (fun φ hφ => hL C hC hind A hA hY S hS Jq ω f σ hσ0 j hj φ hφ)

/-- **K2's field `Sh.fixM.hdiffR` from the per-term coupled bounds** (`fixC`, target side;
`lem:sharp-first` with `lem:density:coupled` for one term with revealed inputs as hypothesis
`hterm`, nonnegative remainders `rt`, relative error `ε_L` with `z_L ≥ R_err ε_L`). -/
theorem fixHdiffR_of_terms (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (rt : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (σ : ∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, HPiece D L b) → ℝ)
    (hrt0 : ∀ L A S Jq ω f σ j φ, 0 ≤ rt L A S Jq ω f σ j φ)
    (hterm : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option
          (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        ∀ φ : (∀ b, HPiece D L b), (∀ b, hpieceCoef D L f σ j b (φ b) ≠ 0) →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
            hpieceK D L (TheoremCBlock.Structured.wrapInc D L) b (φ b)))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          (∏ b, hpieceG D L b (φ b)) * ((1 + ε L) * (fixedPrice pr h
              (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))) + rt L A S Jq ω f
                σ j φ)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
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
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            ∑ j', ∑ φ : (∀ b, HPiece D L b),
                (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A S Jq ω f σ j' φ) := by
  refine fixHdiffR_of_choices hcop D hpair z ε hε hz (fun L A S Jq ω f σ => ∑ j', ∑ φ : (∀ b,
      HPiece D L b),
      (∏ b, |hpieceCoef D L f σ j' b (φ b)|) * rt L A S Jq ω f σ j' φ) ?_
  filter_upwards [hterm] with L hL
  intro C hC hind A hA hY S hS Jq ω f σ hσ0 j hj
  have hK : 0 ≤ fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) :=
    mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one)
  exact choice_bound_all_tags blk D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.wrapInc D L) f σ _ (mul_nonneg (by linarith [hε L]) hK) _ (fun j' φ
        => hrt0 _ _ _ _ _ _ _ j' φ) j
    (fun φ hφ => hL C hC hind A hA hY S hS Jq ω f σ hσ0 j hj φ hφ)

end Sarkozy.DensityFibre
