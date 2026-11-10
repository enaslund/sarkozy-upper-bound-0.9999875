module

public import Sarkozy.EnvelopeInputs.SharpFirstFolded
public import Sarkozy.TheoremC.Cancellation

/-!
# `SharpFirstTerms` from density-structured folded-energy bounds alone

`sharpFirstTerms_of_foldedPieces` takes the folded-energy bounds with free remainders and a
remainder summation. In `prop:record:density-structured` the remainder of an energy of a positive
law `ρ` is `‖ρ‖ C L^{-σ} α`. For a folded law of a choice `f` of pieces, `‖ρ‖ = ∏_𝔟 m_𝔟(f_𝔟)` is
the product of the masses of the pieces (`pieceM`; the folded factors have the masses of the
pieces, `FoldedLaws`). With remainders of this form the summation is proved here:

* `sum_pieceMass_le`: per atom, `∑_x |c_x| d_x m_x` is at most the factor of `tagWeight` (as in
  `sum_pieceWeight`, with `m ≤ g` since the selection factors are at least one);
* hence the weighted remainder of `σ` and `j` is at most `tagWeight_j(σ) · C L^{-σ} α`, and summed
  over `σ ≠ ∅` and the tags it is at most `|𝔗| e^{P} e^{∑_j (d_j + v_j)} C L^{-σ} α`
  (WP-R's `sum_maxWeight_le`, `sum_prices_le_totals`).

**`sharpFirstTerms_of_foldedPieces_uniform`**: `D.SharpFirstTerms` from the folded-energy bounds
`𝔈_±(f) ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + (∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α` alone (`lem:sharp-first` with
`prop:record:density-structured` for the folded laws).
-/

@[expose] public section

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.Structured ReflectionCut

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Masses

variable {D : ComparisonData m₀ p pr h E} {L : ℕ} (dec : DecFamily D L)

/-- The masses of the pieces (of their positive measures; one for `μ_𝔟` and for the probability
components `κ_s`). -/
noncomputable def pieceM (b : PaperAtom J L) : Piece dec b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some h) => mass (D.FS.κa L b h)
  | Sum.inr ⟨_, Sum.inl _⟩ => 1
  | Sum.inr ⟨i, Sum.inr t⟩ => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

omit [DecidableEq P] in
theorem pieceM_nonneg (b : PaperAtom J L) (x : Piece dec b) : 0 ≤ pieceM dec b x := by
  rcases x with (_ | hh) | ⟨i, s | t⟩
  · exact zero_le_one
  · exact ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b hh).1
  · exact zero_le_one
  · cases t
    · exact ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
/-- The masses are at most the prices: `m ≤ g` (the selection factors are at least one). -/
theorem pieceM_le_pieceG (b : PaperAtom J L) (x : Piece dec b) :
    pieceM dec b x ≤ pieceG dec b x := by
  have hs := D.one_le_selectionFactor L b
  rcases x with (_ | hh) | ⟨i, s | t⟩
  · exact le_rfl
  · exact le_mul_of_one_le_right (ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b hh).1) hs
  · exact hs
  · cases t
    · exact le_mul_of_one_le_right (ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1) hs
    · exact le_mul_of_one_le_right (ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
        hs

omit [DecidableEq P] in
/-- The weighted masses of the pieces of an atom are at most the factor of `tagWeight`. -/
theorem sum_pieceMass_le (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : PaperAtom J L) :
    ∑ x, |pieceCoef dec σ j b x| * pieceD dec b x * pieceM dec b x ≤
      (σ b).elim (1 + D.FS.pvar L b)
        (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rw [← sum_pieceWeight dec σ j b]
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (pieceM_le_pieceG dec b x)
    (mul_nonneg (abs_nonneg _) (pieceD_nonneg dec b x))

end Masses

omit [DecidableEq P] in
/-- **The weighted remainders of one choice**: with remainders `(∏ m) · rem`, the weighted sum is
at most `tagWeight_j(σ) · rem`. -/
theorem weighted_mass_le (D : ComparisonData m₀ p pr h E) (L : ℕ) (dec : DecFamily D L)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    ∑ f, choiceWeight (pieceCoef dec σ j) (pieceD dec) f * ∏ b, pieceM dec b (f b) ≤
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (D.FS.pvar L) j σ := by
  have hprod : ∏ b, ∑ x, |pieceCoef dec σ j b x| * pieceD dec b x * pieceM dec b x =
      ∑ f : (∀ b, Piece dec b), choiceWeight (pieceCoef dec σ j) (pieceD dec) f *
        ∏ b, pieceM dec b (f b) := by
    rw [Fintype.prod_sum (fun b x => |pieceCoef dec σ j b x| * pieceD dec b x * pieceM dec b x)]
    refine Finset.sum_congr rfl fun f _ => ?_
    unfold choiceWeight
    rw [← Finset.prod_mul_distrib]
  rw [← hprod]
  unfold tagWeight
  exact Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ => mul_nonneg
    (mul_nonneg (abs_nonneg _) (pieceD_nonneg dec b x)) (pieceM_nonneg dec b x))
    (fun b _ => sum_pieceMass_le dec σ j b)

omit [DecidableEq P] in
/-- `tagWeight_j(σ) ≤ maxWeight(σ) e^{P}`. -/
theorem tagWeight_le_maxWeight_exp (D : ComparisonData m₀ p pr h E) (L : ℕ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (D.FS.pvar L) j σ ≤
      maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.FS.P := by
  rw [tagWeight_eq_mul]
  have hW := sharpVarWeight_le_maxWeight (D.FS.tag L) (Structured.dprice_nonneg D L)
    (Structured.vprice_nonneg D L) j σ
  have hR0 := restWeight_nonneg (pvar_nonneg D L) σ
  have hW0 := sharpVarWeight_nonneg (D.FS.tag L) (Structured.dprice_nonneg D L)
    (Structured.vprice_nonneg D L) j σ
  have hR : restWeight (D.FS.pvar L) σ ≤ Real.exp D.FS.P := by
    have h1 : restWeight (D.FS.pvar L) σ ≤ ∏ b, (1 + D.FS.pvar L b) := by
      unfold restWeight
      refine Finset.prod_le_prod₀ (fun b _ => ?_) (fun b _ => ?_)
      · rcases σ b with _ | i
        · simp only [Option.elim_none]
          linarith [pvar_nonneg D L b]
        · exact zero_le_one
      · rcases σ b with _ | i
        · exact le_rfl
        · simp only [Option.elim_some]
          linarith [pvar_nonneg D L b]
    have h2 := prod_one_add_le_exp (D.FS.pvar L) (pvar_nonneg D L)
    have h3 : Real.exp (∑ b, D.FS.pvar L b) ≤ Real.exp D.FS.P :=
      Real.exp_le_exp.mpr (by unfold FirstStage.pvar; exact D.FS.P_total L)
    linarith
  have hM0 : 0 ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ :=
    hW0.trans hW
  calc sharpVarWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) j σ *
        restWeight (D.FS.pvar L) σ
      ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * restWeight (D.FS.pvar L) σ :=
        mul_le_mul_of_nonneg_right hW hR0
    _ ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.FS.P :=
        mul_le_mul_of_nonneg_left hR hM0

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from density-structured folded-energy bounds alone** (`lem:sharp-first`,
`lem:record:folded-energy`, `prop:record:density-structured` for the folded laws): for every tag
`j`, the folded energies at the cut `c_j` of every choice `f` of pieces satisfy
`𝔈_±(f) ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + (∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α`. The remainder summation is
proved, with the constant `|𝔗| e^{P} e^{∑_j (d_j + v_j)} c₁`. -/
theorem sharpFirstTerms_of_foldedPieces_uniform (D : ComparisonData m₀ p pr h E)
    (dec : ∀ L, DecFamily D L)
    (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0)) {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (hfold : AtCounterexamples D.Y (fun L A => ∀ j f,
      foldedPlus (D.FS.cut j) (pieceLp (dec L) j) (fun _ => atomLift m₀ p L A) f ≤
          (∏ b, pieceG (dec L) b (f b)) * ((1 + ε L) * D.Y L A) +
            (∏ b, pieceM (dec L) b (f b)) * remainder c₁ L A ∧
        foldedMinus (D.FS.cut j) (pieceLm (dec L) j) (fun _ => atomLift m₀ p L A) f ≤
          (∏ b, pieceG (dec L) b (f b)) * ((1 + ε L) * D.Y L A) +
            (∏ b, pieceM (dec L) b (f b)) * remainder c₁ L A)) :
    D.SharpFirstTerms := by
  have hrem0 : ∀ L A, 0 ≤ remainder c₁ L A := fun L A => by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  refine sharpFirstTerms_of_foldedPieces D dec ε hε0 hεt
    (c := (Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P *
      Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) * c₁)
    (by positivity)
    (fun L A _ _ f => (∏ b, pieceM (dec L) b (f b)) * remainder c₁ L A)
    (fun L A _ _ f => (∏ b, pieceM (dec L) b (f b)) * remainder c₁ L A)
    (fun L A _ _ f => ⟨mul_nonneg (prod_nonneg fun b _ => pieceM_nonneg (dec L) b (f b))
      (hrem0 L A), mul_nonneg (prod_nonneg fun b _ => pieceM_nonneg (dec L) b (f b))
      (hrem0 L A)⟩) ?_ ?_
  · filter_upwards [hfold] with L hL
    intro C hC hk A hA hY _ _ j _ f
    exact hL C hC hk A hA hY j f
  refine Filter.Eventually.of_forall fun L => ?_
  intro C _ _ A _ _
  set rem := remainder c₁ L A
  have hr := hrem0 L A
  -- each `(σ, j)` contributes at most `maxWeight(σ) e^P · rem`
  have hterm : ∀ σ : (∀ b, Option (D.FS.Ib L b)), ∀ j,
      ∑ f, choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L)) f *
        (((∏ b, pieceM (dec L) b (f b)) * rem + (∏ b, pieceM (dec L) b (f b)) * rem) / 2) ≤
        maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.FS.P * rem := by
    intro σ j
    have h1 : ∑ f, choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L)) f *
        (((∏ b, pieceM (dec L) b (f b)) * rem + (∏ b, pieceM (dec L) b (f b)) * rem) / 2) =
        (∑ f, choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L)) f *
          ∏ b, pieceM (dec L) b (f b)) * rem := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f _ => ?_
      ring
    rw [h1]
    exact (mul_le_mul_of_nonneg_right (weighted_mass_le D L (dec L) σ j) hr).trans
      (mul_le_mul_of_nonneg_right (tagWeight_le_maxWeight_exp D L σ j) hr)
  have hsum := sum_maxWeight_le (Structured.dprice_nonneg D L) (Structured.vprice_nonneg D L)
  have hexp := Real.exp_le_exp.mpr (sum_prices_le_totals D L)
  have hM0 : ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      0 ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
    intro σ
    unfold maxWeight
    refine prod_nonneg fun b _ => ?_
    rcases σ b with _ | i
    · exact zero_le_one
    · exact add_nonneg (Structured.dprice_nonneg D L b i) (Structured.vprice_nonneg D L b i)
  have hP0 : 0 ≤ Real.exp D.FS.P := (Real.exp_pos _).le
  calc ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        ∑ j, ∑ f, choiceWeight (pieceCoef (dec L) σ j) (pieceD (dec L)) f *
          (((∏ b, pieceM (dec L) b (f b)) * rem + (∏ b, pieceM (dec L) b (f b)) * rem) / 2)
      ≤ ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          ∑ _j : D.FS.Tag, maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.FS.P * rem :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun j _ => hterm σ j
    _ = (Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P * rem *
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ (Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P * rem *
          Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) :=
        mul_le_mul_of_nonneg_left (hsum.trans hexp) (by positivity)
    _ = remainder ((Fintype.card D.FS.Tag : ℝ) * Real.exp D.FS.P *
          Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) * c₁) L A := by
        unfold rem remainder
        ring

end Sarkozy.EnvelopeInputs
