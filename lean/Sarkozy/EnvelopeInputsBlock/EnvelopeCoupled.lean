module

public import Sarkozy.EnvelopeInputs.EnvelopeCoupled
public import Sarkozy.EnvelopeInputsBlock.SharpFirstCoupled
public import Sarkozy.EnvelopeInputsBlock.EnvelopeSharpFolded

@[expose] public section




open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputsBlock

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut

section Pieces

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (ω : Choice (D.CL.T L))

/-- The coupled pieces of an atom under a selection: the entry factor (`inl none`), the bracket
records `κu_{𝔟,i}` (`inl (some i)`), the whole difference (`inr (i, none)`) and its two positive
parts (`inr (i, some t)`). -/
abbrev CEPiece (b : BlockAtom Bk J L) : Type :=
  Option (D.GB.Iu L b) ⊕ (D.FS.Ib L b × Option Bool)

/-- The coefficients of the coupled pieces for the selection `ω`, the choice `σ` and the tag
`j`. -/
noncomputable def ecpieceCoef (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) : CEPiece D L b → ℝ
  | Sum.inl none => if σ b = none then 1 else 0
  | Sum.inl (some _) => if σ b = none ∧ ω b = none then 1 else 0
  | Sum.inr (i, none) => if σ b = some i ∧ D.FS.tag L b i = j ∧ ω b = none then 1 else 0
  | Sum.inr (i, some t) =>
      if σ b = some i ∧ D.FS.tag L b i ≠ j ∧ ω b = none then (if t then 1 else -1) else 0

/-- The coupled pieces under the selection `ω`. -/
noncomputable def ecpieceK (b : BlockAtom Bk J L) : CEPiece D L b →
    TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr (i, none) => D.FS.κ' L b i - D.FS.κ L b i
  | Sum.inr (i, some t) => if t then D.FS.κ' L b i else D.FS.κ L b i

/-- The prices of the coupled pieces: one for `μ_𝔟`, the selection factor for the selected
envelope (a probability measure), the sharp price for the whole difference, mass times selection
factor for the records and the positive parts. -/
noncomputable def ecpieceG (b : BlockAtom Bk J L) : CEPiece D L b → ℝ
  | Sum.inl none => (ω b).elim 1 (fun _ => TheoremCBlock.selectionFactor a p D.S.selPre L b)
  | Sum.inl (some i) => mass (D.GB.κu L b i) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | Sum.inr (i, none) => D.FS.dprice L b i
  | Sum.inr (i, some t) =>
      (if t then mass (D.FS.κ' L b i) else mass
          (D.FS.κ L b i)) * TheoremCBlock.selectionFactor a p D.S.selPre L b

omit [DecidableEq P] in
theorem ecpieceG_nonneg (b : BlockAtom Bk J L) (x : CEPiece D L b) : 0 ≤ ecpieceG D L ω b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · unfold ecpieceG
    rcases ω b with _ | te
    · exact zero_le_one
    · exact D.selectionFactor_nonneg L b
  · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
      (D.selectionFactor_nonneg L b)
  · exact TheoremCBlock.Structured.dprice_nonneg D L b i
  · cases t
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
        (D.selectionFactor_nonneg L b)
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
        (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
/-- **The coupled pieces add up to the factor of the term** (`termLaw`). -/
theorem ecpieceSum_eq (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, ecpieceCoef D L ω σ j b x • ecpieceK D L ω b x = termLaw ω σ b := by
  unfold termLaw
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [ecpieceCoef, hσ]
    simp only [hinr, zero_smul, Finset.sum_const_zero, add_zero]
    rcases hω : ω b with _ | te
    · simp [ecpieceCoef, ecpieceK, hσ, hω]
    · simp [ecpieceCoef, ecpieceK, hσ, hω]
  · have hinl : ∀ o, ecpieceCoef D L ω σ j b (Sum.inl o) = 0 := by
      intro o
      rcases o with _ | i <;> simp [ecpieceCoef, hσ]
    simp only [hinl, zero_smul, Finset.sum_const_zero, zero_add]
    rcases hω : ω b with _ | te
    · have hinr : ∀ i, i ≠ i₀ → ∀ y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i hi y
        rcases y with _ | t <;> simp [ecpieceCoef, hσ, Ne.symm hi]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
      simp only [Option.elim, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [Fintype.sum_option, Fintype.sum_bool]
      by_cases ht : D.FS.tag L b i₀ = j
      · have hb : ∀ t : Bool, ecpieceCoef D L ω σ j b (Sum.inr (i₀, some t)) = 0 := by
          intro t
          simp [ecpieceCoef, hσ, ht]
        have h1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        rw [hb, hb, h1]
        simp only [zero_smul, add_zero, one_smul]
        rfl
      · have h0 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 0 := by
          simp [ecpieceCoef, hσ, ht]
        have ht1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some true)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        have ht2 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some false)) = -1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        have hk1 : ecpieceK D L ω b (Sum.inr (i₀, some true)) = D.FS.κ' L b i₀ := rfl
        have hk2 : ecpieceK D L ω b (Sum.inr (i₀, some false)) = D.FS.κ L b i₀ := rfl
        rw [h0, ht1, ht2, hk1, hk2, zero_smul, zero_add, one_smul]
        apply LinearMap.ext
        intro F
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
        ring
    · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i y
        rcases y with _ | t <;> simp [ecpieceCoef, hω]
      simp [hinr]

omit [DecidableEq P] in
/-- **The price bookkeeping of the coupled expansion under a selection**: the weighted prices
are at most `C_𝔟` (the selection factor on `X`, one off it) times the factor of
`tagWeight(d, v, u')`. -/
theorem esum_cpieceWeight_le (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) :
    ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceG D L ω b x ≤
      (if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b else 1) *
        (σ b).elim (1 + selPriceU ω b)
          (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [ecpieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rcases hω : ω b with _ | te
    · simp only [ecpieceCoef, ecpieceG, hσ, hω, and_self, ↓reduceIte, abs_one, one_mul,
        Option.elim, Option.isSome_none, Bool.false_eq_true, selPriceU]
      unfold TheoremCBlock.GramBracket.uprice
      exact le_of_eq rfl
    · simp only [ecpieceCoef, ecpieceG, hσ, hω, ↓reduceIte, abs_one, one_mul, mul_one,
        Option.elim, Option.isSome_some, selPriceU, reduceCtorEq, and_false, abs_zero,
        zero_mul, Finset.sum_const_zero, add_zero]
      exact le_refl _
  · have hinl : ∀ o, ecpieceCoef D L ω σ j b (Sum.inl o) = 0 := by
      intro o
      rcases o with _ | i <;> simp [ecpieceCoef, hσ]
    simp only [hinl, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rcases hω : ω b with _ | te
    · have hinr : ∀ i, i ≠ i₀ → ∀ y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i hi y
        rcases y with _ | t <;> simp [ecpieceCoef, hσ, Ne.symm hi]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
      simp only [Option.elim, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [Fintype.sum_option, Fintype.sum_bool]
      by_cases ht : D.FS.tag L b i₀ = j
      · have hb : ∀ t : Bool, ecpieceCoef D L ω σ j b (Sum.inr (i₀, some t)) = 0 := by
          intro t
          simp [ecpieceCoef, hσ, ht]
        have h1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        rw [hb, hb, h1]
        simp only [abs_zero, zero_mul, add_zero, abs_one, one_mul, ecpieceG, ht, ↓reduceIte]
        exact le_refl _
      · have h0 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 0 := by
          simp [ecpieceCoef, hσ, ht]
        have ht1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some true)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        have ht2 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some false)) = -1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        rw [h0, ht1, ht2]
        simp only [ecpieceG, ht, ↓reduceIte, abs_zero, zero_mul, zero_add, abs_one, abs_neg,
          one_mul, Bool.false_eq_true]
        unfold TheoremCBlock.FirstStage.vprice
        exact le_of_eq (by ring)
    · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i y
        rcases y with _ | t <;> simp [ecpieceCoef, hω]
      simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, Option.elim,
        Option.isSome_some, ↓reduceIte]
      refine mul_nonneg (D.selectionFactor_nonneg L b) ?_
      split_ifs
      · exact TheoremCBlock.Structured.dprice_nonneg D L b i₀
      · exact TheoremCBlock.Structured.vprice_nonneg D L b i₀

/-- The variations of the coupled pieces under a selection: one for the entry factor (`μ_𝔟` or
a selected envelope, both probability measures), `2 κ(1)` for the whole difference, the mass
otherwise. -/
noncomputable def ecpieceM (b : BlockAtom Bk J L) : CEPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some i) => mass (D.GB.κu L b i)
  | Sum.inr (i, none) => 2 * mass (D.FS.κ L b i)
  | Sum.inr (i, some t) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

omit [DecidableEq P] in
theorem ecpieceM_nonneg (b : BlockAtom Bk J L) (x : CEPiece D L b) : 0 ≤ ecpieceM D L b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
  · exact mul_nonneg zero_le_two
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · cases t
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
/-- The weighted variations of the coupled pieces of an atom under a selection are at most
`v_{𝔟,i}` at a chosen difference and `1 + u'_𝔟` at an unchosen atom. -/
theorem esum_cpieceMass_le (ha : 0 ≤ a) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) :
    ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceM D L b x ≤
      (σ b).elim (1 + selPriceU ω b) (fun i => D.FS.vprice L b i) := by
  have hs := D.one_le_selectionFactor ha L b
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
      intro i y
      rcases y with _ | t <;> simp [ecpieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rcases hω : ω b with _ | te
    · simp only [ecpieceCoef, ecpieceM, hσ, hω, and_self, ↓reduceIte, abs_one, one_mul,
        Option.elim, Option.isSome_none, Bool.false_eq_true, selPriceU]
      unfold TheoremCBlock.GramBracket.uprice
      refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
      exact le_mul_of_one_le_right
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1) hs
    · simp only [ecpieceCoef, ecpieceM, hσ, hω, ↓reduceIte, abs_one, one_mul,
        Option.elim, Option.isSome_some, selPriceU, reduceCtorEq, and_false, abs_zero,
        zero_mul, Finset.sum_const_zero, add_zero]
      exact le_refl _
  · have hinl : ∀ o, ecpieceCoef D L ω σ j b (Sum.inl o) = 0 := by
      intro o
      rcases o with _ | i <;> simp [ecpieceCoef, hσ]
    simp only [hinl, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
    have hv := TheoremCBlock.Structured.vprice_nonneg D L b i₀
    rcases hω : ω b with _ | te
    · have hinr : ∀ i, i ≠ i₀ → ∀ y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i hi y
        rcases y with _ | t <;> simp [ecpieceCoef, hσ, Ne.symm hi]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
      simp only [Option.elim]
      rw [Fintype.sum_option, Fintype.sum_bool]
      have hm := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i₀).1
      have hm' := D.FS.mass_eq L b i₀
      unfold TheoremCBlock.FirstStage.vprice
      by_cases ht : D.FS.tag L b i₀ = j
      · have hb : ∀ t : Bool, ecpieceCoef D L ω σ j b (Sum.inr (i₀, some t)) = 0 := by
          intro t
          simp [ecpieceCoef, hσ, ht]
        have h1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        rw [hb, hb, h1]
        simp only [ecpieceM, abs_zero, zero_mul, add_zero, abs_one, one_mul]
        rw [hm']
        nlinarith
      · have h0 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, none)) = 0 := by
          simp [ecpieceCoef, hσ, ht]
        have ht1 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some true)) = 1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        have ht2 : ecpieceCoef D L ω σ j b (Sum.inr (i₀, some false)) = -1 := by
          simp [ecpieceCoef, hσ, ht, hω]
        rw [h0, ht1, ht2]
        simp only [ecpieceM, ↓reduceIte, abs_zero, zero_mul, zero_add, abs_one, abs_neg,
          one_mul, Bool.false_eq_true]
        rw [hm']
        nlinarith
    · have hinr : ∀ i y, ecpieceCoef D L ω σ j b (Sum.inr (i, y)) = 0 := by
        intro i y
        rcases y with _ | t <;> simp [ecpieceCoef, hω]
      simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, Option.elim]
      exact hv

end Pieces

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The two families of term bounds of `envelopeBound_of_terms`** from the subset terms and the
coupled per-term bounds (only the sharp atoms bracketed, the selected envelopes kept whole as
packets). -/
theorem envelopeBound_terms_of_coupled (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ)
    (r : ∀ L, Finset ℤ → (ω : Choice (D.CL.T L)) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, CEPiece D L b) → ℝ)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f))
    (hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
        (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) + r L A ω σ j f)) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      (∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f) ∧
      (∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (D.FS.tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim
          (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
          (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
            (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ +
          ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f)) := by
  filter_upwards [hsub, hcoup] with L hS hC'
  intro C hC hk A hA hY ω hω
  refine ⟨hS C hC hk A hA hY ω hω, ?_⟩
  intro σ hσ j hj
  have hY0 : 0 ≤ D.Y L A := by
    have : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    linarith
  have hK : 0 ≤ (1 + εE L) * D.Y L A := mul_nonneg (by linarith [hε0 L]) hY0
  have hT : (fun b => (σ b).elim (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
        (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
        (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))) =
      fun b => ∑ x, ecpieceCoef D L ω σ j b x • ecpieceK D L ω b x :=
    funext fun b => (ecpieceSum_eq D L ω σ j b).symm
  rw [hT, diagonalIntegral_tensorLaw_sum']
  have hw := weighted_abs_le (ecpieceCoef D L ω σ j) (ecpieceG D L ω)
    (fun f => diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A))
    (r L A ω σ j) ((1 + εE L) * D.Y L A) (hC' C hC hk A hA hY ω hω σ hσ j hj)
  refine hw.trans ?_
  have hprod : ∏ b, ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceG D L ω b x ≤
      (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
        tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ := by
    have h1 : ∏ b, ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceG D L ω b x ≤
        ∏ b, ((if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b else 1) *
          (σ b).elim (1 + selPriceU ω b)
            (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i)) :=
      Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ => mul_nonneg
        (abs_nonneg _) (ecpieceG_nonneg D L ω b x))
        (fun b _ => esum_cpieceWeight_le D L ω σ j b)
    refine h1.trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, prod_selFactor_eq D L ω]
    rfl
  have hKP := mul_le_mul_of_nonneg_left hprod hK
  have hre : (1 + εE L) * D.Y L A *
      ((∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
      tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
        (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ) =
      ((1 + εE L) *
          (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A) *
        tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
          (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ := by ring
  linarith

omit [DecidableEq P] in
/-- **`EnvelopeBound` from the subset terms and the coupled per-term bounds** (`lem:bracket-energy`
with `lem:sharp-first` and `lem:density:coupled`). Input 1 of WP-R's `envelopeBound_of_terms` (the
subset terms) is kept. Its input 2 (the sharp-first terms under the selected envelopes) is
replaced by the coupled per-term bounds
`|Y[⊗_𝔟 K_𝔟(f_𝔟)]| ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + r_f`, for the choices `f` of coupled pieces
with nonzero coefficients. Nothing is folded: the sharp atoms of the tag are kept whole and the
selected envelopes enter as packets. -/
theorem envelopeBound_of_coupledPieces (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {cE : ℝ} (hcE : 0 ≤ cE)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ)
    (r : ∀ L, Finset ℤ → (ω : Choice (D.CL.T L)) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, CEPiece D L b) → ℝ)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f))
    (hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
        (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) + r L A ω σ j f))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          (∑ f, r0 L A ω f +
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f) ≤
          remainder cE L A))
    (hr0 : ∀ L A ω σ j f, 0 ≤ r L A ω σ j f) :
    D.EnvelopeBound := by
  refine TheoremCBlock.Structured.envelopeBound_of_terms D εE hε0 hεt hcE r0
    (fun L A ω σ => ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f) ?_ hrem
  filter_upwards [envelopeBound_terms_of_coupled D εE hε0 r0 r hsub hcoup] with L hL
  intro C hC hk A hA hY ω hω
  obtain ⟨h1, h2⟩ := hL C hC hk A hA hY ω hω
  refine ⟨h1, fun σ hσ j hj => (h2 σ hσ j hj).trans ?_⟩
  have hsingle : ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f ≤
      ∑ j', ∑ f, (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) * r L A ω σ j' f := by
    refine Finset.single_le_sum (f := fun j' => ∑ f, (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) *
      r L A ω σ j' f) (fun j' _ => ?_) (Finset.mem_univ j)
    exact Finset.sum_nonneg fun f _ =>
      mul_nonneg (Finset.prod_nonneg fun b _ => abs_nonneg _) (hr0 L A ω σ j' f)
  linarith

omit [DecidableEq P] in
/-- **The weighted variations of one `(σ, j)` under a selection** are at most
`maxWeight(σ) e^{U₀}`. -/
theorem coupled_weighted_emass_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (ha : 0 ≤ a)
    (L : ℕ)
    (ω : Choice (D.CL.T L)) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
        ∏ b, ecpieceM D L b (f b) ≤
      maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * Real.exp D.GB.U₀ := by
  have hu0 : ∀ b, 0 ≤ selPriceU ω b := by
    intro b
    unfold selPriceU
    split_ifs
    · exact le_rfl
    · exact TheoremCBlock.Structured.uprice_nonneg D L b
  have hprod : ∏ b, ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceM D L b x =
      ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
        ∏ b, ecpieceM D L b (f b) := by
    rw [Fintype.prod_sum (fun b x => |ecpieceCoef D L ω σ j b x| * ecpieceM D L b x)]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [← Finset.prod_mul_distrib]
  rw [← hprod]
  have h1 : ∏ b, ∑ x, |ecpieceCoef D L ω σ j b x| * ecpieceM D L b x ≤
      ∏ b, (σ b).elim (1 + selPriceU ω b) (fun i => D.FS.vprice L b i) :=
    Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ =>
      mul_nonneg (abs_nonneg _) (ecpieceM_nonneg D L b x))
      (fun b _ => esum_cpieceMass_le D L ω ha σ j b)
  have h2 : ∏ b, (σ b).elim (1 + selPriceU ω b) (fun i => D.FS.vprice L b i) ≤
      maxWeight (D.FS.dprice L) (D.FS.vprice L) σ * restWeight (selPriceU ω) σ := by
    unfold maxWeight restWeight
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun b _ => ?_) (fun b _ => ?_)
    · rcases σ b with _ | i
      · simp only [Option.elim_none]
        linarith [hu0 b]
      · exact TheoremCBlock.Structured.vprice_nonneg D L b i
    · rcases σ b with _ | i
      · simp only [Option.elim_none, one_mul]
        exact le_rfl
      · simp only [Option.elim_some, mul_one]
        linarith [TheoremCBlock.Structured.dprice_nonneg D L b i]
  have hR : restWeight (selPriceU ω) σ ≤ Real.exp D.GB.U₀ := by
    have h3 : restWeight (selPriceU ω) σ ≤ ∏ b, (1 + selPriceU ω b) := by
      unfold restWeight
      refine Finset.prod_le_prod₀ (fun b _ => ?_) (fun b _ => ?_)
      · rcases σ b with _ | i
        · simp only [Option.elim_none]
          linarith [hu0 b]
        · exact zero_le_one
      · rcases σ b with _ | i
        · exact le_rfl
        · simp only [Option.elim_some]
          linarith [hu0 b]
    have h4 := prod_one_add_le_exp (selPriceU ω) hu0
    have h5 : ∑ b, selPriceU ω b ≤ D.GB.U₀ := by
      refine le_trans (Finset.sum_le_sum fun b _ => ?_) (D.GB.U₀_total L)
      unfold selPriceU
      split_ifs
      · exact Finset.sum_nonneg fun i _ => mul_nonneg
          (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
          (D.selectionFactor_nonneg L b)
      · exact le_rfl
    have h6 := Real.exp_le_exp.mpr h5
    linarith
  have hM0 : 0 ≤ maxWeight (D.FS.dprice L) (D.FS.vprice L) σ := by
    unfold maxWeight
    refine prod_nonneg fun b _ => ?_
    rcases σ b with _ | i
    · exact zero_le_one
    · exact add_nonneg (TheoremCBlock.Structured.dprice_nonneg D L b i)
        (TheoremCBlock.Structured.vprice_nonneg D L b i)
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hR hM0))

omit [DecidableEq P] in
/-- **`EnvelopeBound` from the subset terms and the coupled per-term bounds alone**
(`lem:bracket-energy`, `lem:sharp-first`, `lem:density:coupled`): the subset terms with the
remainders `∏_f mass(∑κu) c₁ L^{-σ} α`, and the coupled terms with the remainders
`(∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α`. The remainder summation is proved, with the per-selection constant
`e^{U₀} (1 + |𝔗| e^{∑_j(d_j+v_j)}) c₁`. -/
theorem envelopeBound_of_coupledPieces_uniform (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {c₁ : ℝ}
        (hc₁ : 0 ≤ c₁)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
            remainder c₁ L A))
    (hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
        (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) +
          (∏ b, ecpieceM D L b (f b)) * remainder c₁ L A)) :
    D.EnvelopeBound := by
  have hrem0 : ∀ L A, 0 ≤ remainder c₁ L A := fun L A => by
    unfold remainder
    exact mul_nonneg (mul_nonneg hc₁ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  set K := Real.exp D.GB.U₀ * (1 + (Fintype.card D.FS.Tag : ℝ) *
    Real.exp (∑ j, (D.FS.dT j + D.FS.vT j))) * c₁ with hK
  have hK0 : 0 ≤ K := by positivity
  refine TheoremCBlock.Structured.envelopeBound_of_terms_uniform D ha εE hε0 hεt hK0
    (fun L A ω f =>
      (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
        remainder c₁ L A)
    (fun L A ω σ => ∑ j, ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
      ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A)) ?_ ?_
  · filter_upwards [envelopeBound_terms_of_coupled D εE hε0
      (fun L A ω f =>
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A)
      (fun L A _ _ _ f => (∏ b, ecpieceM D L b (f b)) * remainder c₁ L A) hsub hcoup]
      with L hL
    intro C hC hk A hA hY ω hω
    obtain ⟨h1, h2⟩ := hL C hC hk A hA hY ω hω
    refine ⟨h1, fun σ hσ j hj => (h2 σ hσ j hj).trans ?_⟩
    have hsingle : ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j b (f b)|) *
        ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A) ≤
        ∑ j', ∑ f : (∀ b, CEPiece D L b), (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) *
          ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A) := by
      refine Finset.single_le_sum (f := fun j' => ∑ f : (∀ b, CEPiece D L b),
        (∏ b, |ecpieceCoef D L ω σ j' b (f b)|) *
          ((∏ b, ecpieceM D L b (f b)) * remainder c₁ L A)) (fun j' _ => ?_)
        (Finset.mem_univ j)
      exact Finset.sum_nonneg fun f _ => mul_nonneg (Finset.prod_nonneg fun b _ => abs_nonneg _)
        (mul_nonneg (prod_nonneg fun b _ => ecpieceM_nonneg D L b (f b)) (hrem0 L A))
    linarith
  · refine Filter.Eventually.of_forall fun L => ?_
    intro C _ _ A _ _ ω _
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
    have hfin : remainder K L A = remainder (Real.exp D.GB.U₀ * c₁) L A +
        (Fintype.card D.FS.Tag : ℝ) * Real.exp D.GB.U₀ * rem *
          Real.exp (∑ j, (D.FS.dT j + D.FS.vT j)) := by
      unfold rem remainder
      rw [hK]
      ring
    rw [hfin]
    exact add_le_add hsub_rem hsharp

end Final

end Sarkozy.EnvelopeInputsBlock
