module

public import Sarkozy.EnvelopeInputs.EnvelopeSharpFolded
public import Sarkozy.EnvelopeInputsBlock.SharpFirstFolded

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
  {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ} (dec : DecFamily D L)
      (ω : Choice (D.CL.T L))

/-- The pieces of an atom under the selection `ω`: the entry factor (`inl none`), the bracket
records `κu_{𝔟,i}` (`inl (some i)`), and the sharp components and positive parts of the
differences (`inr`). -/
abbrev EPiece (b : BlockAtom Bk J L) : Type :=
  Option (D.GB.Iu L b) ⊕ (Σ i : D.FS.Ib L b, (dec b i).S ⊕ Bool)

/-- The coefficients of the pieces for the choice `σ` and the tag `j`. -/
noncomputable def epieceCoef (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    EPiece dec b → ℝ
  | Sum.inl none => if σ b = none then 1 else 0
  | Sum.inl (some _) => if σ b = none ∧ ω b = none then 1 else 0
  | Sum.inr ⟨i, Sum.inl s⟩ =>
      if σ b = some i ∧ D.FS.tag L b i = j ∧ ω b = none then
        mass (D.FS.κ L b i) * (dec b i).π.weight s else 0
  | Sum.inr ⟨i, Sum.inr t⟩ =>
      if σ b = some i ∧ D.FS.tag L b i ≠ j ∧ ω b = none then (if t then 1 else -1) else 0

/-- The pieces. -/
noncomputable def epieceK (j : D.FS.Tag) (b : BlockAtom Bk J L) : EPiece dec b →
    TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)
  | Sum.inl (some i) => D.GB.κu L b i
  | Sum.inr ⟨i, Sum.inl s⟩ => if D.FS.tag L b i = j then (dec b i).Ks s else 0
  | Sum.inr ⟨i, Sum.inr t⟩ => if t then D.FS.κ' L b i else D.FS.κ L b i

/-- The plus folded factors at the cut `c_j`. -/
noncomputable def epieceLp (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    EPiece dec b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => (ω b).elim (D.R.law p L b) (fun te =>
      (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.CL.D L b te.1 te.2)))
  | Sum.inl (some i) => (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) (D.GB.κu L b i))
  | Sum.inr ⟨i, Sum.inl s⟩ =>
      (D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) ((dec b i).κs s))
  | Sum.inr ⟨i, Sum.inr t⟩ => (D.FS.cut j).diagonalLaw
      (halfMarginalPlus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))

/-- The minus folded factors at the cut `c_j`. -/
noncomputable def epieceLm (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    EPiece dec b → TheoremCBlock.AtomMeasure m₀ blk p L b
  | Sum.inl none => (ω b).elim (D.R.law p L b) (fun te =>
      (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.CL.D L b te.1 te.2)))
  | Sum.inl (some i) => (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) (D.GB.κu L b i))
  | Sum.inr ⟨i, Sum.inl s⟩ =>
      (D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) ((dec b i).κs s))
  | Sum.inr ⟨i, Sum.inr t⟩ => (D.FS.cut j).diagonalLaw
      (halfMarginalMinus (D.FS.cut j) (if t then D.FS.κ' L b i else D.FS.κ L b i))

/-- The bracket constants: the sharp constant for the components, one otherwise. -/
noncomputable def epieceD (b : BlockAtom Bk J L) : EPiece dec b → ℝ
  | Sum.inl _ => 1
  | Sum.inr ⟨i, Sum.inl _⟩ => D.FS.dconst L b i
  | Sum.inr ⟨_, Sum.inr _⟩ => 1

/-- The prices of the folded pieces: mass times selection factor; one for `μ_𝔟`, the selection
factor for the selected envelope (a probability measure). -/
noncomputable def epieceG (b : BlockAtom Bk J L) : EPiece dec b → ℝ
  | Sum.inl none => (ω b).elim 1 (fun _ => TheoremCBlock.selectionFactor a p D.S.selPre L b)
  | Sum.inl (some i) => mass (D.GB.κu L b i) * TheoremCBlock.selectionFactor a p D.S.selPre L b
  | Sum.inr ⟨_, Sum.inl _⟩ => TheoremCBlock.selectionFactor a p D.S.selPre L b
  | Sum.inr ⟨i, Sum.inr t⟩ =>
      (if t then mass (D.FS.κ' L b i) else mass
          (D.FS.κ L b i)) * TheoremCBlock.selectionFactor a p D.S.selPre L b

/-- The law of the term at an atom (the second input of `envelopeBound_of_terms`). -/
noncomputable def termLaw (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) :
    TheoremCBlock.AtomMeasure m₀ blk p L b :=
  (σ b).elim (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
      (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
    (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))

omit [DecidableEq P] in
/-- **The pieces add up to the factor of the term.** -/
theorem epieceSum_eq (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, epieceCoef dec ω σ j b x • epieceK dec ω j b x = termLaw ω σ b := by
  unfold termLaw
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, epieceCoef dec ω σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i y
      rcases y with s | t <;> simp [epieceCoef, hσ]
    simp only [hinr, zero_smul, Finset.sum_const_zero, add_zero]
    rcases hω : ω b with _ | te
    · simp [epieceCoef, epieceK, hσ, hω]
    · simp [epieceCoef, epieceK, hσ, hω]
  · have hinl : ∀ o, epieceCoef dec ω σ j b (Sum.inl o) = 0 := by
      intro o
      rcases o with _ | i <;> simp [epieceCoef, hσ]
    simp only [hinl, zero_smul, Finset.sum_const_zero, zero_add]
    rcases hω : ω b with _ | te
    · have hinr : ∀ i, i ≠ i₀ → ∀ y, epieceCoef dec ω σ j b (Sum.inr ⟨i, y⟩) = 0 := by
        intro i hi y
        rcases y with s | t <;> simp [epieceCoef, hσ, Ne.symm hi]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
      simp only [Option.elim, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [Fintype.sum_sum_type, Fintype.sum_bool]
      by_cases ht : D.FS.tag L b i₀ = j
      · have hb : ∀ t : Bool, epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inr t⟩) = 0 := by
          intro t
          simp [epieceCoef, hσ, ht]
        simp only [hb, zero_smul, add_zero]
        simp only [epieceCoef, epieceK, hσ, ht, hω, and_self, ↓reduceIte]
        refine Eq.trans ?_ (dec b i₀).hζ.symm
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [smul_smul]
      · have hs : ∀ s, epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inl s⟩) = 0 := by
          intro s
          simp [epieceCoef, hσ, ht]
        simp only [hs, zero_smul, Finset.sum_const_zero, zero_add]
        have ht1 : epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inr true⟩) = 1 := by
          simp [epieceCoef, hσ, ht, hω]
        have ht2 : epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inr false⟩) = -1 := by
          simp [epieceCoef, hσ, ht, hω]
        have hk1 : epieceK dec ω j b (Sum.inr ⟨i₀, Sum.inr true⟩) = D.FS.κ' L b i₀ := rfl
        have hk2 : epieceK dec ω j b (Sum.inr ⟨i₀, Sum.inr false⟩) = D.FS.κ L b i₀ := rfl
        rw [ht1, ht2, hk1, hk2, one_smul]
        apply LinearMap.ext
        intro F
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
        ring
    · have hinr : ∀ i y, epieceCoef dec ω σ j b (Sum.inr ⟨i, y⟩) = 0 := by
        intro i y
        rcases y with s | t <;> simp [epieceCoef, hω]
      simp [hinr]

omit [DecidableEq P] in
theorem epieceD_nonneg (b : BlockAtom Bk J L) (x : EPiece dec b) : 0 ≤ epieceD dec b x := by
  rcases x with _ | ⟨i, s | t⟩
  · exact zero_le_one
  · exact D.FS.dconst_nonneg L b i
  · exact zero_le_one

omit [DecidableEq P] in
theorem epieceLp_positive (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : EPiece dec b) :
    (D.FS.cut j).Positive (epieceLp dec ω j b x) := by
  rcases x with (_ | i) | ⟨i, s | t⟩
  · rcases hω : ω b with _ | te
    · simp only [epieceLp, hω, Option.elim]
      exact D.law_positive (D.FS.cut_family j) L b
    · simp only [epieceLp, hω, Option.elim]
      exact (D.FS.cut j).diagonalLaw_positive
        (halfMarginalPlus_nonneg _ (D.CL.D_prob L b te.1 te.2).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.GB.κu_pos L b i).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ ((dec b i).prob s).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalPlus_nonneg _ (D.FS.κ'_pos L b i).1)

omit [DecidableEq P] in
theorem epieceLm_positive (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : EPiece dec b) :
    (D.FS.cut j).Positive (epieceLm dec ω j b x) := by
  rcases x with (_ | i) | ⟨i, s | t⟩
  · rcases hω : ω b with _ | te
    · simp only [epieceLm, hω, Option.elim]
      exact D.law_positive (D.FS.cut_family j) L b
    · simp only [epieceLm, hω, Option.elim]
      exact (D.FS.cut j).diagonalLaw_positive
        (halfMarginalMinus_nonneg _ (D.CL.D_prob L b te.1 te.2).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.GB.κu_pos L b i).1)
  · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ ((dec b i).prob s).1)
  · cases t
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ_pos L b i).1)
    · exact (D.FS.cut j).diagonalLaw_positive (halfMarginalMinus_nonneg _ (D.FS.κ'_pos L b i).1)

omit [DecidableEq P] in
/-- Every piece is bracketed at the cut `c_j` by its folded factors. -/
theorem epiece_bracket (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : EPiece dec b) :
    (D.FS.cut j).Bracket (epieceD dec b x • epieceLp dec ω j b x) (epieceK dec ω j b x)
      (epieceD dec b x • epieceLm dec ω j b x) := by
  rcases x with (_ | i) | ⟨i, s | t⟩
  · rcases hω : ω b with _ | te
    · simp only [epieceD, epieceLp, epieceLm, epieceK, hω, Option.elim]
      exact bracket_of_positive _ (D.law_positive (D.FS.cut_family j) L b)
    · simp only [epieceD, epieceLp, epieceLm, epieceK, hω, Option.elim]
      exact bracket_of_nonneg _ _ (D.CL.D_prob L b te.1 te.2).1
  · exact bracket_of_nonneg _ _ (D.GB.κu_pos L b i).1
  · by_cases ht : D.FS.tag L b i = j
    · simp only [epieceD, epieceLp, epieceLm, epieceK, ht, ↓reduceIte]
      have hsh := (dec b i).sharp s
      subst ht
      exact (sharp_iff_bracket _ _ (halfMarginalPlus_nonneg _ ((dec b i).prob s).1)
        (halfMarginalMinus_nonneg _ ((dec b i).prob s).1) (D.FS.dconst_nonneg L b i)).mp hsh
    · simp only [epieceD, epieceLp, epieceLm, epieceK, ht, ↓reduceIte]
      have hp := ((D.FS.cut j).diagonalLaw_positive
        (halfMarginalPlus_nonneg (D.FS.cut j) ((dec b i).prob s).1)).smul
          (D.FS.dconst_nonneg L b i)
      have hm := ((D.FS.cut j).diagonalLaw_positive
        (halfMarginalMinus_nonneg (D.FS.cut j) ((dec b i).prob s).1)).smul
          (D.FS.dconst_nonneg L b i)
      refine ⟨hp, hm, fun F G => ?_⟩
      have h1 := hp.nonneg F
      have h2 := hm.nonneg G
      have h0 : (D.FS.cut j).form (0 : TheoremCBlock.AtomMeasure m₀ blk p L b) F G = 0 := rfl
      rw [h0]
      linarith
  · cases t
    · exact bracket_of_nonneg _ _ (D.FS.κ_pos L b i).1
    · exact bracket_of_nonneg _ _ (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
theorem epieceG_nonneg (b : BlockAtom Bk J L) (x : EPiece dec b) : 0 ≤ epieceG dec ω b x := by
  have hs := D.selectionFactor_nonneg L b
  rcases x with (_ | i) | ⟨i, s | t⟩
  · rcases hω : ω b with _ | te
    · simp only [epieceG, hω, Option.elim]
      exact zero_le_one
    · simp only [epieceG, hω, Option.elim]
      exact hs
  · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1) hs
  · exact hs
  · cases t
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1) hs
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1) hs

omit [DecidableEq P] in
/-- **The folded factorization of a sharp-first term under a selection.** -/
theorem envelope_term_le_folded (A : Finset ℤ) (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) :
    (∀ f, 0 ≤ foldedPlus (D.FS.cut j) (epieceLp dec ω j) (fun _ => blockLift m₀ blk p L A) f) ∧
    (∀ f, 0 ≤ foldedMinus (D.FS.cut j) (epieceLm dec ω j) (fun _ => blockLift m₀ blk p L A) f) ∧
    |diagonalIntegral (tensorLaw (termLaw ω σ)) (blockLift m₀ blk p L A)| ≤
      Real.sqrt (∑ f, choiceWeight (epieceCoef dec ω σ j) (epieceD dec) f *
          foldedPlus (D.FS.cut j) (epieceLp dec ω j) (fun _ => blockLift m₀ blk p L A) f) *
        Real.sqrt (∑ f, choiceWeight (epieceCoef dec ω σ j) (epieceD dec) f *
          foldedMinus (D.FS.cut j) (epieceLm dec ω j) (fun _ => blockLift m₀ blk p L A) f) := by
  have hlaw : termLaw ω σ = fun b => ∑ x, epieceCoef dec ω σ j b x • epieceK dec ω j b x :=
    funext fun b => (epieceSum_eq dec ω σ j b).symm
  rw [hlaw]
  exact abs_tensor_sum_le_folded (D.FS.cut j) (epieceCoef dec ω σ j) (epieceD dec)
    (epieceK dec ω j) (epieceLp dec ω j) (epieceLm dec ω j) (epieceD_nonneg dec)
    (epieceLp_positive dec ω j) (epieceLm_positive dec ω j) (epiece_bracket dec ω j)
    (fun _ => blockLift m₀ blk p L A)

/-- The record prices `u'_𝔟` of the unselected atoms (`0` on the selected set). -/
noncomputable def selPriceU (b : BlockAtom Bk J L) : ℝ := if
    (ω b).isSome then 0 else D.GB.uprice L b

omit [DecidableEq P] in
/-- **The price bookkeeping under a selection**: the weighted prices of the pieces of an atom are
at most `C_𝔟` (the selection factor on the selected set, one off it) times the factor of
`tagWeight(d, v, u')`; with equality unless a difference is chosen at a selected atom. -/
theorem sum_epieceWeight_le (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L) :
    ∑ x, |epieceCoef dec ω σ j b x| * epieceD dec b x * epieceG dec ω b x ≤
      (if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b else 1) *
        (σ b).elim (1 + selPriceU ω b)
          (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  rcases hσ : σ b with _ | i₀
  · have hinr : ∀ i y, epieceCoef dec ω σ j b (Sum.inr ⟨i, y⟩) = 0 := by
      intro i y
      rcases y with s | t <;> simp [epieceCoef, hσ]
    simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rcases hω : ω b with _ | te
    · simp only [epieceCoef, epieceD, epieceG, hσ, hω, and_self, ↓reduceIte, abs_one, mul_one,
        Option.elim, Option.isSome_none, Bool.false_eq_true, one_mul, selPriceU]
      unfold TheoremCBlock.GramBracket.uprice
      exact le_of_eq rfl
    · simp only [epieceCoef, epieceD, epieceG, hσ, hω, ↓reduceIte, abs_one, mul_one,
        Option.elim, Option.isSome_some, selPriceU, reduceCtorEq, and_false, abs_zero,
        zero_mul, Finset.sum_const_zero, add_zero, one_mul]
      linarith
  · have hinl : ∀ o, epieceCoef dec ω σ j b (Sum.inl o) = 0 := by
      intro o
      rcases o with _ | i <;> simp [epieceCoef, hσ]
    simp only [hinl, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
    rcases hω : ω b with _ | te
    · have hinr : ∀ i, i ≠ i₀ → ∀ y, epieceCoef dec ω σ j b (Sum.inr ⟨i, y⟩) = 0 := by
        intro i hi y
        rcases y with s | t <;> simp [epieceCoef, hσ, Ne.symm hi]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hinr i hi]) (by simp)]
      simp only [Option.elim, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [Fintype.sum_sum_type, Fintype.sum_bool]
      by_cases ht : D.FS.tag L b i₀ = j
      · have hb : ∀ t : Bool, epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inr t⟩) = 0 := by
          intro t
          simp [epieceCoef, hσ, ht]
        simp only [hb, abs_zero, zero_mul, add_zero]
        simp only [epieceCoef, epieceD, epieceG, hσ, ht, hω, and_self, ↓reduceIte]
        have hm := TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i₀).1
        have hterm : ∀ s, |mass (D.FS.κ L b i₀) * (dec b i₀).π.weight s| * D.FS.dconst L b i₀ *
            TheoremCBlock.selectionFactor a p D.S.selPre L b =
              (dec b i₀).π.weight s * (mass (D.FS.κ L b i₀) * D.FS.dconst L b i₀ *
                TheoremCBlock.selectionFactor a p D.S.selPre L b) := by
          intro s
          rw [abs_of_nonneg (mul_nonneg hm ((dec b i₀).π.nonneg s))]
          ring
        rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.sum_mul, (dec b i₀).π.total,
          one_mul]
        exact le_of_eq rfl
      · have hs : ∀ s, epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inl s⟩) = 0 := by
          intro s
          simp [epieceCoef, hσ, ht]
        simp only [hs, abs_zero, zero_mul, Finset.sum_const_zero, zero_add]
        have ht1 : epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inr true⟩) = 1 := by
          simp [epieceCoef, hσ, ht, hω]
        have ht2 : epieceCoef dec ω σ j b (Sum.inr ⟨i₀, Sum.inr false⟩) = -1 := by
          simp [epieceCoef, hσ, ht, hω]
        rw [ht1, ht2]
        simp only [epieceD, epieceG, ht, ↓reduceIte, abs_one, abs_neg, one_mul,
          Bool.false_eq_true]
        unfold TheoremCBlock.FirstStage.vprice
        exact le_of_eq (by ring)
    · have hinr : ∀ i y, epieceCoef dec ω σ j b (Sum.inr ⟨i, y⟩) = 0 := by
        intro i y
        rcases y with s | t <;> simp [epieceCoef, hω]
      simp only [hinr, abs_zero, zero_mul, Finset.sum_const_zero, Option.elim,
        Option.isSome_some, ↓reduceIte]
      refine mul_nonneg (D.selectionFactor_nonneg L b) ?_
      split_ifs
      · exact TheoremCBlock.Structured.dprice_nonneg D L b i₀
      · exact TheoremCBlock.Structured.vprice_nonneg D L b i₀

end Pieces

section Final

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- The selection factors: `∏_𝔟 (𝔟 ∈ X ? q_𝔟^{2a} : 1) = C_X`. -/
theorem prod_selFactor_eq (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) :
    ∏ b, (if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b else 1) =
      ∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b := by
  unfold Choice.support
  rw [Finset.prod_filter]

omit [DecidableEq P] in
/-- **The two families of term bounds of `envelopeBound_of_terms`** from the subset terms and the
folded-energy bounds of the pieces (the second family by folding, gap 8). -/
theorem envelopeBound_terms_of_folded (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (dec : ∀ L, DecFamily D L) (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ)
    (rp rm : ∀ L, Finset ℤ → Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, EPiece (dec L) b) → ℝ)
    (hr0 : ∀ L A ω σ j f, 0 ≤ rp L A ω σ j f ∧ 0 ≤ rm L A ω σ j f)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f))
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
      foldedPlus (D.FS.cut j) (epieceLp (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) + rp L A ω σ j f ∧
        foldedMinus (D.FS.cut j) (epieceLm (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) + rm L A ω σ j f)) :
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
          ∑ j', ∑ f, choiceWeight (epieceCoef (dec L) ω σ j') (epieceD (dec L)) f *
            ((rp L A ω σ j' f + rm L A ω σ j' f) / 2))) := by
  filter_upwards [hsub, hfold] with L hS hF
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
  obtain ⟨hFp0, hFm0, hT⟩ := envelope_term_le_folded (dec L) ω A σ j
  have hw : ∀ f, 0 ≤ choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f := fun f =>
    Finset.prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (epieceD_nonneg (dec L) b (f b))
  set CX := ∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b with hCX
  set TW := tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
    (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ with hTW
  have hprod : ∏ b, ∑ x, |epieceCoef (dec L) ω σ j b x| * epieceD (dec L) b x *
      epieceG (dec L) ω b x ≤ CX * TW := by
    have h1 : ∏ b, ∑ x, |epieceCoef (dec L) ω σ j b x| * epieceD (dec L) b x *
        epieceG (dec L) ω b x ≤
        ∏ b, ((if (ω b).isSome then TheoremCBlock.selectionFactor a p D.S.selPre L b else 1) *
          (σ b).elim (1 + selPriceU ω b)
            (fun i => if D.FS.tag L b i = j then D.FS.dprice L b i else D.FS.vprice L b i)) :=
      Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun x _ => mul_nonneg (mul_nonneg
        (abs_nonneg _) (epieceD_nonneg (dec L) b x)) (epieceG_nonneg (dec L) ω b x))
        (fun b _ => sum_epieceWeight_le (dec L) ω σ j b)
    refine h1.trans (le_of_eq ?_)
    rw [Finset.prod_mul_distrib, prod_selFactor_eq D L ω]
    rfl
  have hFp := weighted_folded_le (epieceCoef (dec L) ω σ j) (epieceD (dec L)) (epieceG (dec L) ω)
    (epieceD_nonneg (dec L)) _ (rp L A ω σ j) ((1 + εE L) * D.Y L A)
    (fun f => (hF C hC hk A hA hY ω hω σ hσ j hj f).1)
  have hFm := weighted_folded_le (epieceCoef (dec L) ω σ j) (epieceD (dec L)) (epieceG (dec L) ω)
    (epieceD_nonneg (dec L)) _ (rm L A ω σ j) ((1 + εE L) * D.Y L A)
    (fun f => (hF C hC hk A hA hY ω hω σ hσ j hj f).2)
  have hKP := mul_le_mul_of_nonneg_left hprod hK
  set w := choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L))
  set Fp := ∑ f, w f * foldedPlus (D.FS.cut j) (epieceLp (dec L) ω j)
    (fun _ => blockLift m₀ blk p L A) f
  set Fm := ∑ f, w f * foldedMinus (D.FS.cut j) (epieceLm (dec L) ω j)
    (fun _ => blockLift m₀ blk p L A) f
  have hFp0' : 0 ≤ Fp := Finset.sum_nonneg fun f _ => mul_nonneg (hw f) (hFp0 f)
  have hFm0' : 0 ≤ Fm := Finset.sum_nonneg fun f _ => mul_nonneg (hw f) (hFm0 f)
  have hgm := sqrt_mul_sqrt_le_add_div_two hFp0' hFm0'
  have hsplit : ∑ f, w f * ((rp L A ω σ j f + rm L A ω σ j f) / 2) =
      ((∑ f, w f * rp L A ω σ j f) + ∑ f, w f * rm L A ω σ j f) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hsingle : ∑ f, w f * ((rp L A ω σ j f + rm L A ω σ j f) / 2) ≤
      ∑ j', ∑ f, choiceWeight (epieceCoef (dec L) ω σ j') (epieceD (dec L)) f *
        ((rp L A ω σ j' f + rm L A ω σ j' f) / 2) := by
    refine Finset.single_le_sum (f := fun j' => ∑ f, choiceWeight (epieceCoef (dec L) ω σ j')
      (epieceD (dec L)) f * ((rp L A ω σ j' f + rm L A ω σ j' f) / 2)) (fun j' _ => ?_)
      (Finset.mem_univ j)
    refine Finset.sum_nonneg fun f _ => mul_nonneg ?_ ?_
    · exact Finset.prod_nonneg fun b _ =>
        mul_nonneg (abs_nonneg _) (epieceD_nonneg (dec L) b (f b))
    · have := hr0 L A ω σ j' f
      linarith [this.1, this.2]
  have hterm : |diagonalIntegral (tensorLaw (fun b => (σ b).elim
      (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
        (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
      (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
        (blockLift m₀ blk p L A)| ≤ Real.sqrt Fp * Real.sqrt Fm := hT
  calc |diagonalIntegral (tensorLaw (fun b => (σ b).elim
          (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
          (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
            (blockLift m₀ blk p L A)|
      ≤ Real.sqrt Fp * Real.sqrt Fm := hterm
    _ ≤ (Fp + Fm) / 2 := hgm
    _ ≤ ((1 + εE L) * D.Y L A) * (CX * TW) +
          ∑ f, w f * ((rp L A ω σ j f + rm L A ω σ j f) / 2) := by
        rw [hsplit]
        linarith
    _ ≤ ((1 + εE L) * CX * D.Y L A) * TW + ∑ j', ∑ f,
          choiceWeight (epieceCoef (dec L) ω σ j') (epieceD (dec L)) f *
            ((rp L A ω σ j' f + rm L A ω σ j' f) / 2) := by
        have : ((1 + εE L) * D.Y L A) * (CX * TW) = ((1 + εE L) * CX * D.Y L A) * TW := by ring
        linarith

omit [DecidableEq P] in
/-- **`EnvelopeBound` from the subset terms and the folded-energy bounds of the pieces**
(`lem:bracket-energy` with `lem:sharp-first` and `lem:record:folded-energy`, gap 8). Input 1 of
WP-R's `envelopeBound_of_terms` (the subset terms) is kept. Its input 2 (the sharp-first terms
under the selected envelopes) is replaced by the folded-energy bounds of the pieces
`𝔈_±(f) ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + r_±(f)`, with nonnegative remainders; the remainder
summation includes the weighted folded remainders. -/
theorem envelopeBound_of_foldedPieces (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (dec : ∀ L, DecFamily D L)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {cE : ℝ} (hcE : 0 ≤ cE)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ)
    (rp rm : ∀ L, Finset ℤ → Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
      (∀ b, EPiece (dec L) b) → ℝ)
    (hr0 : ∀ L A ω σ j f, 0 ≤ rp L A ω σ j f ∧ 0 ≤ rm L A ω σ j f)
    (hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ f : BlockAtom Bk J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f))
    (hfold : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
      foldedPlus (D.FS.cut j) (epieceLp (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) + rp L A ω σ j f ∧
        foldedMinus (D.FS.cut j) (epieceLm (dec L) ω j) (fun _ => blockLift m₀ blk p L A) f ≤
          (∏ b, epieceG (dec L) ω b (f b)) * ((1 + εE L) * D.Y L A) + rm L A ω σ j f))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          (∑ f, r0 L A ω f +
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
                ((rp L A ω σ j f + rm L A ω σ j f) / 2)) ≤ remainder cE L A)) :
    D.EnvelopeBound :=
  TheoremCBlock.Structured.envelopeBound_of_terms D εE hε0 hεt hcE r0
    (fun L A ω σ => ∑ j, ∑ f, choiceWeight (epieceCoef (dec L) ω σ j) (epieceD (dec L)) f *
      ((rp L A ω σ j f + rm L A ω σ j f) / 2))
    (envelopeBound_terms_of_folded D dec εE hε0 r0 rp rm hr0 hsub hfold) hrem

end Final

end Sarkozy.EnvelopeInputsBlock
