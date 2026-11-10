module

public import Sarkozy.MainFinalF1b.E1

@[expose] public section

/-!
# K2's uniform (E1) inputs give the aggregate ones (F1P)

`E1InputsAgg.ofUniform`: K2's `MainFinal2.E1Inputs` (per-term remainders
`(∏ masses) c₁ L^{-σ} α`, `(∏ m) c₁ L^{-σ} α`) gives `E1InputsAgg`, with `hrem` from G1's summation
of the uniform remainders (`uniform_rem_le`, the second half of the proof of
`envelopeBoundNonneg_of_coupledPieces_uniform`, verbatim) and `sum_selection_remainder_le`.
So the aggregate form is **weaker** than the uniform one: the correction of FA2's P1 only removes
hypotheses.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1b

open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The per-selection sum of the uniform remainders** (G1, second half of the proof of
`envelopeBoundNonneg_of_coupledPieces_uniform`): at every scale and selection,
`∑_f (∏ masses) rem + ∑_{σ ≠ ∅} ∑_j ∑_f ∏|c| (∏ m) rem ≤ K L^{-σ} α` with
`K = e^{U₀}(1 + |Tag| e^{∑(d_T + v_T)}) c₁`. -/
theorem uniform_rem_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (ha : 0 ≤ a)
    {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) :
    ∑ f : BlockAtom Bk J L → Bool,
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A +
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
          ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A) ≤
      remainder (Real.exp D.GB.U₀ * (1 + (Fintype.card D.FS.Tag : ℝ) *
        Real.exp (∑ j, (D.FS.dT j + D.FS.vT j))) * c₁) L A := by
  have hrem0 : ∀ L A, 0 ≤ remainder c₁ L A := fun L A => by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  set rem := remainder c₁ L A
  have hr := hrem0 L A
  have hsub_rem := TheoremCBlock.Structured.sum_subset_remainder_le D ha L A ω hc₁
  have hterm : ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j,
      ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
          ((∏ b, ecpieceM D L b (f b)) * rem) ≤
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ * rem := by
    intro σ j
    have h1 : ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
          ((∏ b, ecpieceM D L b (f b)) * rem) =
        (∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
          ∏ b, ecpieceM D L b (f b)) * rem := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (coupled_weighted_emass_le D ha L ω σ j) hr
  have hsum := sum_maxWeight_le (TheoremCBlock.Structured.dprice_nonneg D L)
      (TheoremCBlock.Structured.vprice_nonneg D L)
  have hexp := Real.exp_le_exp.mpr (TheoremCBlock.Structured.sum_prices_le_totals D L)
  have hstep1 := Finset.sum_le_sum (s := univ.filter
      (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none))
    fun σ _ => Finset.sum_le_sum (s := (univ : Finset D.FS.Tag)) fun j _ => hterm σ j
  have hstep2 : ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ _j : D.FS.Tag, maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ * rem =
      (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hstep3 : (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ ≤
      (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
        Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) :=
    mul_le_mul_of_nonneg_left (hsum.trans hexp) (by positivity)
  have hsharp := hstep1.trans (le_of_eq hstep2) |>.trans hstep3
  have hfin : remainder (Real.exp D.GB.U₀ * (1 + (Fintype.card D.FS.Tag : ℝ) *
      Real.exp (∑ j, (D.FS.dT j + D.FS.vT j))) * c₁) L A =
      remainder (Real.exp D.GB.U₀ * c₁) L A +
      (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
        Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) := by
    unfold rem remainder
    ring
  rw [hfin]
  exact add_le_add hsub_rem hsharp


omit [DecidableEq P] in
/-- **K2's uniform (E1) inputs give the aggregate ones** (the uniform remainders, `hrem` by
`uniform_rem_le` and `sum_selection_remainder_le`). -/
noncomputable def E1InputsAgg.ofUniform {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (ha : 0 ≤ a) (I : MainFinal2.E1Inputs D) : E1InputsAgg D where
  εE := I.εE
  hε0 := I.hε0
  hεt := I.hεt
  cE := Real.exp D.CL.S * Real.cosh D.CL.A * (Real.exp D.GB.U₀ *
    (1 + (Fintype.card D.FS.Tag : ℝ) * Real.exp (∑ j, (D.FS.dT j + D.FS.vT j))) * I.c₁)
  hcE := by
    have := I.hc₁
    positivity
  r0 L A ω f :=
    (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
      remainder I.c₁ L A
  r L A _ _ _ f := (∏ b, ecpieceM D L b (f b)) * remainder I.c₁ L A
  hsub := I.hsub
  hcoup := I.hcoup
  hrem := Filter.Eventually.of_forall fun L => by
    intro C _ _ A _ _
    exact TheoremCBlock.Structured.sum_selection_remainder_le D ha L A _
      (by have := I.hc₁; positivity) fun ω _ => uniform_rem_le D ha I.hc₁ L A ω
  hr0 L A _ _ _ f := mul_nonneg (prod_nonneg fun b _ => ecpieceM_nonneg D L b (f b))
    (by
      unfold remainder
      exact mul_nonneg (mul_nonneg I.hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (density_nonneg _ _))
  hs0 L A ω f := mul_nonneg (prod_nonneg fun b _ => subsetMass_nonneg D L ω f b)
    (by
      unfold remainder
      exact mul_nonneg (mul_nonneg I.hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (density_nonneg _ _))

end Sarkozy.MainFinalF1b
