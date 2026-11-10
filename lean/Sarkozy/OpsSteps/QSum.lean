module

public import Sarkozy.E1Closure.Paper

@[expose] public section

/-!
# The summed bound of the coupled pieces, independent of the law on the support (OPS-S)

`paper/sections/10_comparison_lemmas.tex`, "Fixed selections and summed remainders"
(ll. 126–140), `lem:sharp-first`, `lem:density:coupled`, `lem:record:density-lp`.

EC bounds every coupled piece of (E1) by a quantity that depends on the law on the selected atoms
only through its mass: `(∏_𝔟 cM_𝔟) c₁ L^{-σ} α` on a small union (`E1CoupSmallPT`), and the
Hölder bound `(∏_𝔟 ‖cDom_𝔟‖) B` on a large one (`coup_large_le`, `abs_diag_le_dom`). EC sums these
bounds inside the proofs of `e1CoupSmall_of_perTerm` and `coup_large_le`. This file isolates that
summation, with no law in it:

* `pieceBnd rem B ω f`: the bound of the piece `f` under the selection `ω`;
* **`sum_pieceBnd_le`**: `∑_ω π̃_ω ∑_{σ≠∅} ∑_j ∑_f ∏|c| pieceBnd ≤ |𝔗| e^{3S} rem +
  |𝔗| B N^{-τ/4} ∏_𝔟 W_𝔟` (EC's two summations, verbatim in structure);
* **`sum_pieceBnd_remainder`**: at `rem = c₁ L^{-σ} α` and the moment bound `B` of the lift, this
  is at most `c L^{-σ} α` for every large `L` and every `A` (EC's `final_le` step).

Any law on the support that is a probability measure with uniform one-slot marginals (a placed
coupling, `OpsSteps.QPieces`) has its pieces bounded by `pieceBnd`, so its canonical remainders sum
to `c L^{-σ} α` as EC's do.
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.E1Closure Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice
open Sarkozy.LargeSums (atomQR atomQR_nonneg atomPr)
open Sarkozy.FourierArithmetic (ResidueSpace)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- **The law-independent bound of a coupled piece**: `(∏ cM) rem` on a small union, the Hölder
bound `(∏ ‖cDom‖) B` on a large union. -/
noncomputable def pieceBnd (rem B : ℝ) (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) : ℝ :=
  if CoupSmall D L ω f then (∏ b, cM D L b (f b)) * rem
  else (∏ b, mass (cDom D L b (ω b) (f b))) * B

omit [DecidableEq P] in
theorem pieceBnd_nonneg (hp : ∀ j, (p L j).Prime) {rem B : ℝ} (hrem : 0 ≤ rem) (hB : 0 ≤ B)
    (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b) : 0 ≤ pieceBnd D L rem B ω f := by
  unfold pieceBnd
  split_ifs
  · exact mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem
  · exact mul_nonneg (prod_nonneg fun b _ => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (isPositiveRecord_cDom D L hp b (ω b) (f b)).1) hB

omit [DecidableEq P] in
/-- **The small part of the summation** (EC's `e1CoupSmall_of_perTerm`, without the law). -/
theorem sum_small_le (ha : 0 ≤ a) {rem : ℝ} (hrem0 : 0 ≤ rem) :
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      monomial (D.CL.πt L) ω *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            (if CoupSmall D L ω f then (∏ b, cM D L b (f b)) * rem else 0) ≤
      (Fintype.card D.FS.Tag : ℝ) * Real.exp (3 * D.SM.bound) * rem := by
  set SS := univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)
  set g : ∀ b : BlockAtom Bk J L, Option (D.CL.T L b × ChangeType) → CEPiece D L b → ℝ :=
    fun b o x => entryPrice (D.CL.πt L b) o * compat D L b o x * cM D L b x with hg
  have hg0 : ∀ b o x, 0 ≤ g b o x := fun b o x =>
    mul_nonneg (mul_nonneg (entryPrice_nonneg (D.CL.πt_nonneg L b) o) (compat_nonneg D L b o x))
      (cM_nonneg D L b x)
  have hpt : ∀ (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
      (f : ∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
      (if CoupSmall D L ω f then (∏ b, cM D L b (f b)) * rem else 0) ≤
      (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * ((∏ b, cM D L b (f b)) * rem) := by
    intro ω σ j f
    refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun b _ => abs_nonneg _)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem0
  have hσ : ∀ ω : Choice (D.CL.T L), ∑ σ ∈ SS, ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
      (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * ((∏ b, cM D L b (f b)) * rem) ≤
      ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
        (∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem) := by
    intro ω
    have hG0 : ∀ f : (∀ b, CEPiece D L b), 0 ≤ (∏ b, cM D L b (f b)) * rem := fun f =>
      mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem0
    calc _ ≤ ∑ σ : (∀ b, Option (D.FS.Ib L b)), ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * ((∏ b, cM D L b (f b)) * rem) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ =>
            sum_nonneg fun j _ => sum_nonneg fun f _ =>
              mul_nonneg (prod_nonneg fun b _ => abs_nonneg _) (hG0 f)
      _ = ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∑ σ : (∀ b, Option (D.FS.Ib L b)), ∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            ((∏ b, cM D L b (f b)) * rem) := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_comm]
          simp only [sum_mul]
      _ ≤ _ := sum_le_sum fun j _ => sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (sum_prod_abs_coef_le D L ω j f) (hG0 f)
  have hper : ∀ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
      monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem)) ≤
      Real.exp (3 * D.SM.bound) * rem := by
    intro j
    have e : ∀ (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b),
        monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) *
          ((∏ b, cM D L b (f b)) * rem)) = rem * ∏ b, g b (ω b) (f b) := by
      intro ω f
      have hm : monomial (D.CL.πt L) ω = ∏ b, entryPrice (D.CL.πt L b) (ω b) := rfl
      rw [hm]
      simp only [hg, prod_mul_distrib]
      ring
    simp only [e, ← mul_sum]
    rw [sum_sum_prod g, mul_comm]
    refine mul_le_mul_of_nonneg_right ((prod_le_prod₀ (fun b _ => sum_nonneg fun o _ =>
      sum_nonneg fun x _ => hg0 b o x) fun b _ => coupAtomM_le D L b).trans
        (prod_three_atomPr_le D ha L)) hrem0
  calc _ ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem) := by
        refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_
          (monomial_nonneg (D.CL.πt_nonneg L) ω)
        exact (sum_le_sum fun σ _ => sum_le_sum fun j _ => sum_le_sum fun f _ =>
          hpt ω σ j f).trans (hσ ω)
    _ ≤ ∑ ω : Choice (D.CL.T L), monomial (D.CL.πt L) ω * ∑ j : D.FS.Tag,
          ∑ f : (∀ b, CEPiece D L b),
            (∏ b, compat D L b (ω b) (f b)) * ((∏ b, cM D L b (f b)) * rem) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
          mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (sum_nonneg fun j _ =>
            sum_nonneg fun f _ => mul_nonneg (prod_nonneg fun b _ =>
              compat_nonneg D L b (ω b) (f b))
              (mul_nonneg (prod_nonneg fun b _ => cM_nonneg D L b (f b)) hrem0))
    _ = ∑ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
          monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) *
            ((∏ b, cM D L b (f b)) * rem)) := by
        simp only [mul_sum]
        rw [sum_comm]
    _ ≤ ∑ _j : D.FS.Tag, Real.exp (3 * D.SM.bound) * rem := sum_le_sum fun j _ => hper j
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

omit [DecidableEq P] in
/-- **The large part of the summation** (EC's `coup_large_le`, without the law). -/
theorem sum_large_le (hp : ∀ j, (p L j).Prime) {B : ℝ} (hB0 : 0 ≤ B) (hT : 0 < stageT L) :
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            (if CoupSmall D L ω f then 0 else (∏ b, mass (cDom D L b (ω b) (f b))) * B) ≤
      (Fintype.card D.FS.Tag : ℝ) * (B * (stageT L ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b)) := by
  set T := stageT L with hTdef
  set G : Choice (D.CL.T L) → (∀ b, CEPiece D L b) → ℝ := fun ω f =>
    if CoupSmall D L ω f then 0 else (∏ b, mass (cDom D L b (ω b) (f b))) * B with hG
  have hG0 : ∀ ω f, 0 ≤ G ω f := fun ω f => by
    simp only [hG]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (prod_nonneg fun b _ => TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
        (isPositiveRecord_cDom D L hp b (ω b) (f b)).1) hB0
  set g : ∀ b : BlockAtom Bk J L, Option (D.CL.T L b × ChangeType) → CEPiece D L b → ℝ :=
    fun b o x => entryPrice (D.CL.πt L b) o * compat D L b o x * mass (cDom D L b o x) *
      coupQ D L b o x ^ ((1 : ℝ) / 4) with hg
  have hw0 : ∀ b o x, 0 ≤ entryPrice (D.CL.πt L b) o * compat D L b o x * mass (cDom D L b o x) :=
    fun b o x => mul_nonneg (mul_nonneg (entryPrice_nonneg (D.CL.πt_nonneg L b) o)
      (compat_nonneg D L b o x))
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (isPositiveRecord_cDom D L hp b o x).1)
  have hg0 : ∀ b o x, 0 ≤ g b o x := fun b o x =>
    mul_nonneg (hw0 b o x) (Real.rpow_nonneg (coupQ_nonneg D L b o x) _)
  have hT4 : 0 ≤ T ^ (-((1 : ℝ) / 4)) := Real.rpow_nonneg hT.le _
  have hσ : ∀ ω : Choice (D.CL.T L),
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * G ω f ≤
      ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b), (∏ b, compat D L b (ω b) (f b)) * G ω f := by
    intro ω
    calc _ ≤ ∑ σ : (∀ b, Option (D.FS.Ib L b)),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * G ω f :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun σ _ _ =>
            sum_nonneg fun j _ => sum_nonneg fun f _ =>
              mul_nonneg (prod_nonneg fun b _ => abs_nonneg _) (hG0 ω f)
      _ = ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b),
          (∑ σ : (∀ b, Option (D.FS.Ib L b)), ∏ b, |ecpieceCoef D L ω σ j b (f b)|) * G ω f := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_comm]
          simp only [sum_mul]
      _ ≤ _ := sum_le_sum fun j _ => sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (sum_prod_abs_coef_le D L ω j f) (hG0 ω f)
  have hterm : ∀ (ω : Choice (D.CL.T L)) (f : ∀ b, CEPiece D L b),
      monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * G ω f) ≤
        B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) := by
    intro ω f
    simp only [hG]
    split_ifs with hs
    · rw [mul_zero, mul_zero]
      exact mul_nonneg hB0 (mul_nonneg hT4 (prod_nonneg fun b _ => hg0 b (ω b) (f b)))
    · have h2 := rankin_term univ
        (fun b => entryPrice (D.CL.πt L b) (ω b) * compat D L b (ω b) (f b) *
          mass (cDom D L b (ω b) (f b)))
        (fun b => coupQ D L b (ω b) (f b)) (fun b _ => hw0 b (ω b) (f b))
        (fun b _ => coupQ_nonneg D L b (ω b) (f b)) hT (lt_of_not_ge hs)
      have hm : monomial (D.CL.πt L) ω = ∏ b, entryPrice (D.CL.πt L b) (ω b) := rfl
      calc monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) *
            ((∏ b, mass (cDom D L b (ω b) (f b))) * B))
          = B * ∏ b, (entryPrice (D.CL.πt L b) (ω b) * compat D L b (ω b) (f b) *
              mass (cDom D L b (ω b) (f b))) := by
            rw [hm, prod_mul_distrib, prod_mul_distrib]
            ring
        _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
            mul_le_mul_of_nonneg_left h2 hB0
  have hper : ∀ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
      monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * G ω f) ≤
      B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
    intro j
    calc _ ≤ ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
          B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, g b (ω b) (f b)) :=
          sum_le_sum fun ω _ => sum_le_sum fun f _ => hterm ω f
      _ = B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, ∑ o, ∑ x, g b o x) := by
          rw [← sum_sum_prod g]
          simp only [mul_sum]
      _ ≤ B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hT4) hB0
          exact prod_le_prod₀ (fun b _ => sum_nonneg fun o _ => sum_nonneg fun x _ => hg0 b o x)
            fun b _ => coupAtom_le D L b
  calc _ ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b), (∏ b, compat D L b (ω b) (f b)) * G ω f :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hσ ω)
          (monomial_nonneg (D.CL.πt_nonneg L) ω)
    _ ≤ ∑ ω : Choice (D.CL.T L), monomial (D.CL.πt L) ω *
          ∑ j : D.FS.Tag, ∑ f : (∀ b, CEPiece D L b), (∏ b, compat D L b (ω b) (f b)) * G ω f :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun ω _ _ =>
          mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (sum_nonneg fun j _ =>
            sum_nonneg fun f _ =>
              mul_nonneg (prod_nonneg fun b _ => compat_nonneg D L b (ω b) (f b)) (hG0 ω f))
    _ = ∑ j : D.FS.Tag, ∑ ω : Choice (D.CL.T L), ∑ f : (∀ b, CEPiece D L b),
          monomial (D.CL.πt L) ω * ((∏ b, compat D L b (ω b) (f b)) * G ω f) := by
        simp only [mul_sum]
        rw [sum_comm]
    _ ≤ ∑ _j : D.FS.Tag, B * (T ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b) :=
        sum_le_sum fun j _ => hper j
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]

omit [DecidableEq P] in
/-- **The law-independent summation**: small and large parts together. -/
theorem sum_pieceBnd_le (ha : 0 ≤ a) (hp : ∀ j, (p L j).Prime) {rem B : ℝ} (hrem0 : 0 ≤ rem)
    (hB0 : 0 ≤ B) (hT : 0 < stageT L) :
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * pieceBnd D L rem B ω f ≤
      (Fintype.card D.FS.Tag : ℝ) * Real.exp (3 * D.SM.bound) * rem +
        (Fintype.card D.FS.Tag : ℝ) * (B * (stageT L ^ (-((1 : ℝ) / 4)) * ∏ b, atomW D L b)) := by
  have hsplit : ∀ ω f, pieceBnd D L rem B ω f =
      (if CoupSmall D L ω f then (∏ b, cM D L b (f b)) * rem else 0) +
        (if CoupSmall D L ω f then 0 else (∏ b, mass (cDom D L b (ω b) (f b))) * B) := by
    intro ω f
    unfold pieceBnd
    split_ifs <;> ring
  simp only [hsplit, mul_add, sum_add_distrib]
  exact add_le_add (sum_small_le D L ha hrem0) (sum_large_le D L hp hB0 hT)

/-- The moment bound of the lift (`lem:record:lift-moments`(c)) at the constant `C`. -/
noncomputable def momB (C : ℝ) (L : ℕ) (A : Finset ℤ) : ℝ :=
  1 ^ 72 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 72 * C *
    Functional.paperCutoff (blockScale * L) ^ ((1 : ℝ) / 2000) *
    ((blockScale : ℝ) * density (blockScale * L) A))

omit [DecidableEq P] in
/-- **The law-independent summation is a remainder** (EC's `e1Large_proved` and
`e1CoupSmall_of_perTerm` constants): with the moment bound `B = momB C` of the lift
(`blockLift_moment_le`) and `rem = c₁ L^{-σ} α`, at every large `L` and every `A`,
`∑_ω π̃_ω ∑_{σ,j,f} ∏|c| pieceBnd ≤ c L^{-σ} α`. -/
theorem pieceBnd_summable (ha : 0 ≤ a) {c₁ : ℝ} (hc₁ : 0 ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ L : ℕ in atTop, ∀ A : Finset ℤ,
      0 ≤ momB (m₀ := m₀) C L A ∧
      (FiniteLaw.uniform (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b)).moment 72
          (blockLift m₀ blk p L A) ≤ momB (m₀ := m₀) C L A ∧ 0 < stageT L ∧
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), monomial (D.CL.πt L) ω *
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
            pieceBnd D L (remainder c₁ L A) (momB (m₀ := m₀) C L A) ω f ≤ remainder c L A := by
  obtain ⟨C, hC, hmom⟩ := blockLift_moment_le (m₀ := m₀) (blk := blk) (p := p)
  set X : ℝ := (Fintype.card (ResidueSpace m₀) : ℝ) with hX
  set nT : ℝ := (Fintype.card D.FS.Tag : ℝ) with hnT
  have hnT0 : 0 ≤ nT := by positivity
  refine ⟨C, hC, nT * Real.exp (3 * D.SM.bound) * c₁ +
    nT * ((1 : ℝ) ^ 72 * (X ^ 72 * C * blockScale)) * Real.exp (2 * D.SM.bound),
    by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ 20 * blockScale)] with L hL
  intro A
  have hL1 : 1 ≤ L := le_trans (by norm_num [blockScale]) hL
  have hB := hmom L hL (D.S.p_prime L) (D.S.p_inj L) A
  have hB0 := Sarkozy.LargeSums.lpB_nonneg (M0 := 1) (X := X) hL1 A hC.le
  have hT : 0 < stageT L := Sarkozy.LargeSums.stageT_pos L hL1
  refine ⟨hB0, hB, hT, ?_⟩
  have hrem0 : 0 ≤ remainder c₁ L A := E1Closure.remainder_nonneg' hc₁ L A
  have h1 := sum_pieceBnd_le D L ha (D.S.p_prime L) hrem0 hB0 hT
  have hPi := prod_atomW_le D L ha
  have key := Sarkozy.LargeSums.final_le hL1 hnT0 hC.le (density_nonneg (blockScale * L) A) hPi
    (M0 := 1) (X := X)
  refine h1.trans ?_
  rw [E1Closure.remainder_add]
  refine add_le_add (le_of_eq ?_) ?_
  · unfold remainder
    ring
  · unfold stageT
    unfold remainder
    exact le_of_eq_of_le (by rfl) (key.trans_eq (by ring))

end Sarkozy.OpsSteps
