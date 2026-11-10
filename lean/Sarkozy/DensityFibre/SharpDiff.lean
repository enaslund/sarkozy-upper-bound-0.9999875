module

public import Sarkozy.BracketEnergy.Bundles
public import Sarkozy.BracketEnergy.SharpDiff

@[expose] public section

/-!
# `Sh.fixM.hdiffL/R`, `Sh.envM.hdiffL/R`: the sharp-first differences from the per-choice terms

K2's fields 26–27 and 30–31 (`FixMeansInputs.hdiffL/R`, `EnvMeansInputs.hdiffL/R`) are the
arguments `hdiffL`, `hdiffR` of B9's `FixedBracketInputs.ofMeans` and
`EnvelopeBracketInputs.ofMeans`. Each says, at every least counterexample, depth vector `𝒥`,
index `ω` and set `f` of atoms carrying the selected increments `Q` (and, for `fixC`, every
nonempty set `𝒮` of fixed queries):
`|E_{f ? Q : Ñ} − E_{f ? Q : Ñ₀}| ≤ (R_err + z_L) K_{𝒥,f} Y + r₂(L, A, 𝒥, ω, f)`,
with the revealed inputs of the bundle and the price `K = Π_𝒥 ∏_f u_𝔟`.

This file proves all four fields from the **per-choice coupled terms** of `lem:sharp-first`,
through B9's `diff_bound_of_coupled`. For every nonempty choice `σ` of first-stage differences and
every tag `j` present in `σ`, the hypothesis is
`|E_σ| ≤ K Y wt_j(σ) + r_σ`. Here `E_σ` is the revealed-input energy of the law `sharpPiece`:
* `κ'_i − κ_i` at the atoms where `σ` picks `i`;
* `Q` on `f`;
* `Ñ₀ = μ + ∑ κu` elsewhere.

The weight `wt_j(σ)` has the sharp prices `d`, the variation prices `v` and `p_𝔟 = u'_𝔟` off `f`.
This is `lem:density:coupled` with revealed inputs, used as a hypothesis. The conclusion is the
field with the **explicit** remainder `r₂ = ∑_{σ ≠ ∅} r_σ`, and the constant is the data's
`R_err` exactly.

* `envHdiffL_of_choices`, `envHdiffR_of_choices`: fields 30–31.
* `fixHdiffL_of_choices`, `fixHdiffR_of_choices`: fields 26–27.
* **Finding** (`envHdiffL_free`; the other three sides are the same): taken alone, each `hdiff`
  field is satisfiable
  by its own remainder `r₂ := |E_{Ñ} − E_{Ñ₀}|`, because `r₂` is free data of the bundle. The
  content of `lem:sharp-first` sits in the summation fields `hm` (28–29, 32–33), through the
  shared data `r₂`. So `hdiff` and `hm` must be discharged with the same `r₂`. The constructors
  here supply the paper's `r₂ = ∑_σ r_σ`, whose summation is density-linear when each `r_σ` is
  the dc error of its choice.
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

/-! ## The relative error of the per-choice bounds -/

omit [DecidableEq P] in
/-- **`diff_bound_of_coupled` with a relative error**: per-choice bounds
`|E_σ| ≤ (1 + ε) K wt_j(σ) + r_σ` give `|E_Ñ − E_{Ñ₀}| ≤ (R_err + z) K + ∑_σ r_σ` for every
`z ≥ R_err ε` (B9's lemma at the price `(1 + ε) K` and `z = 0`). The factor `1 + ε_L` is that of
the fibre moments (`CoupledFibreMoment`, `ε_L → 0`). -/
theorem diff_bound_of_coupled_eps (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (f : BlockAtom Bk J L → Bool)
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) {K z ε : ℝ} (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hz : D.GB.Rerr * ε ≤ z) (r : (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
      |multilinearIntegral (tensorLaw (crtLaws blk h0 L (sharpPiece D L Qb f σ))) G| ≤
        ((1 + ε) * K) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if f b then 0 else D.GB.uprice L b) j σ + r σ) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N L b)) G -
        multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N₀ L b)) G| ≤
      (D.GB.Rerr + z) * K +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none), r σ := by
  have hK' : 0 ≤ (1 + ε) * K := mul_nonneg (by linarith) hK
  have hb := diff_bound_of_coupled blk D L h0 Qb f G hK' (le_refl 0) r hterm
  have hR := Rerr_nonneg D
  have h1 : (D.GB.Rerr + 0) * ((1 + ε) * K) ≤ (D.GB.Rerr + z) * K := by
    have := mul_le_mul_of_nonneg_right hz hK
    nlinarith
  linarith

/-! ## `envC` (fields 30–31) -/

/-- **`Sh.envM.hdiffL` from the per-choice coupled terms** (`lem:sharp-first` for the selected
bracket with the revealed inputs of `envC`, source side). The per-choice bounds are
`lem:density:coupled` with revealed inputs, used as hypothesis `hch`. The remainder of the field
is `r₂ = ∑_{σ ≠ ∅} r_σ`. -/
theorem envHdiffL_of_choices (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (r : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hch : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.envIncL D L) f σ)))
          (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          ((1 + ε L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))) *
            tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ + r L A Jq ω f σ)) :
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
              r L A Jq ω f σ) := by
  filter_upwards [hch] with L hL
  intro C hC hind A hA hY Jq ω f
  have hK : 0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) :=
    mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
        · exact zero_le_one)
  exact diff_bound_of_coupled_eps D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.envIncL D L) f _ hK (hε L) (hz L) (r L A Jq ω f)
    (hL C hC hind A hA hY Jq ω f)

/-- **`Sh.envM.hdiffR` from the per-choice coupled terms** (target side; as
`envHdiffL_of_choices`). -/
theorem envHdiffR_of_choices (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (r : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hch : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.envIncR D L) f σ)))
          (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          ((1 + ε L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1))) *
            tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ + r L A Jq ω f σ)) :
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
              r L A Jq ω f σ) := by
  filter_upwards [hch] with L hL
  intro C hC hind A hA hY Jq ω f
  have hK : 0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) :=
    mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
        · exact zero_le_one)
  exact diff_bound_of_coupled_eps D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.envIncR D L) f _ hK (hε L) (hz L) (r L A Jq ω f)
    (hL C hC hind A hA hY Jq ω f)

/-! ## `fixC` (fields 26–27) -/

/-- **`Sh.fixM.hdiffL` from the per-choice coupled terms** (`lem:sharp-first` for the selected
bracket with the revealed inputs of `fixC`: fixed intervals on the nonempty set `𝒮` of queries,
source side). The remainder of the field is `r₂ = ∑_{σ ≠ ∅} r_σ`. -/
theorem fixHdiffL_of_choices (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (r : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hch : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk J L → Bool)
        (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.wrapInc D L) f σ)))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          ((1 + ε L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))) *
            tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ + r L A S Jq ω f σ)) :
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
            r L A S Jq ω f σ) := by
  filter_upwards [hch] with L hL
  intro C hC hind A hA hY S hS Jq ω f
  have hK : 0 ≤ fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) :=
    mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one)
  exact diff_bound_of_coupled_eps D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.wrapInc D L) f _ hK (hε L) (hz L) (r L A S Jq ω f)
    (hL C hC hind A hA hY S hS Jq ω f)

/-- **`Sh.fixM.hdiffR` from the per-choice coupled terms** (target side; as
`fixHdiffL_of_choices`). -/
theorem fixHdiffR_of_choices (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z ε : ℕ → ℝ) (hε : ∀ L, 0 ≤ ε L) (hz : ∀ L, D.GB.Rerr * ε L ≤ z L)
    (r : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
        (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hch : Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk J L → Bool)
        (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j →
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.wrapInc D L) f σ)))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
          ((1 + ε L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
            ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))) *
            tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ + r L A S Jq ω f σ)) :
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
            r L A S Jq ω f σ) := by
  filter_upwards [hch] with L hL
  intro C hC hind A hA hY S hS Jq ω f
  have hK : 0 ≤ fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) :=
    mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
        · exact zero_le_one)
  exact diff_bound_of_coupled_eps D L (prefix_pairwise (hpair L))
    (TheoremCBlock.Structured.wrapInc D L) f _ hK (hε L) (hz L) (r L A S Jq ω f)
    (hL C hC hind A hA hY S hS Jq ω f)

/-! ## Finding: the `hdiff` fields alone are satisfiable by their own remainder -/

/-- **`hdiffL` of `envC` holds with `r₂ := |E_Ñ − E_{Ñ₀}|`**, for every `z ≥ 0`. The field has no
content of its own; `lem:sharp-first` enters only through the summation `hm`, which shares `r₂`. -/
theorem envHdiffL_free (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) :
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
            |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
              if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
              (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
                (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
            multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
              if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N₀ L b))
              (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
                (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L)
                ω ω)|) := by
  filter_upwards with L
  intro C hC _ A _ hY Jq ω f
  have hK : 0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) :=
    mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) (Y_nonneg_of_cex D hC hY))
      (prod_nonneg fun b _ => by
        split_ifs
        · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
        · exact zero_le_one)
  have := mul_nonneg (add_nonneg (Rerr_nonneg D) (hz0 L)) hK
  linarith

end Sarkozy.DensityFibre
