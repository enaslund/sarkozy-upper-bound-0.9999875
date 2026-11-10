module

public import Sarkozy.EnvelopeInputs.FoldedRecords
public import Sarkozy.EnvelopeInputsParam.EnvelopeSharpFolded

@[expose] public section



open scoped BigOperators

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice ReflectionCut

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  {D : TheoremCParam.ComparisonData a m₀ p pr h E} {L : ℕ} (dec : DecFamily D L)

omit [DecidableEq P] in
/-- **The plus folded factors of the sharp-first pieces** (other than `μ_𝔟`) are positive
records with mass times selection factor equal to the price `g` of the piece. -/
theorem pieceLp_record (hκs : ∀ b i s, IsPositiveRecord ((dec b i).κs s)) (j : D.FS.Tag)
    (b : PaperAtom J L) (x : Piece dec b) (hx : x ≠ Sum.inl none) :
    IsPositiveRecord (pieceLp dec j b x) ∧
      mass (pieceLp dec j b x) * TheoremCParam.selectionFactor a p D.S.selPre L b =
          pieceG dec b x := by
  rcases x with (_ | hh) | ⟨i, s | t⟩
  · exact absurd rfl hx
  · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (D.FS.κa_pos L b hh)
    exact ⟨h1, by simp only [pieceLp, pieceG]; rw [h2]⟩
  · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (hκs b i s)
    refine ⟨h1, ?_⟩
    simp only [pieceLp, pieceG]
    rw [h2, mass_eq_one_of_prob ((dec b i).prob s), one_mul]
  · cases t
    · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (D.FS.κ_pos L b i)
      exact ⟨h1, by simp only [pieceLp, pieceG, Bool.false_eq_true, ↓reduceIte]; rw [h2]⟩
    · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (D.FS.κ'_pos L b i)
      exact ⟨h1, by simp only [pieceLp, pieceG, ↓reduceIte]; rw [h2]⟩

omit [DecidableEq P] in
/-- The minus folded factors of the sharp-first pieces. -/
theorem pieceLm_record (hκs : ∀ b i s, IsPositiveRecord ((dec b i).κs s)) (j : D.FS.Tag)
    (b : PaperAtom J L) (x : Piece dec b) (hx : x ≠ Sum.inl none) :
    IsPositiveRecord (pieceLm dec j b x) ∧
      mass (pieceLm dec j b x) * TheoremCParam.selectionFactor a p D.S.selPre L b =
          pieceG dec b x := by
  rcases x with (_ | hh) | ⟨i, s | t⟩
  · exact absurd rfl hx
  · obtain ⟨h1, h2⟩ := isPositiveRecord_foldMinus (D.FS.cut j) (D.FS.κa_pos L b hh)
    exact ⟨h1, by simp only [pieceLm, pieceG]; rw [h2]⟩
  · obtain ⟨h1, h2⟩ := isPositiveRecord_foldMinus (D.FS.cut j) (hκs b i s)
    refine ⟨h1, ?_⟩
    simp only [pieceLm, pieceG]
    rw [h2, mass_eq_one_of_prob ((dec b i).prob s), one_mul]
  · cases t
    · obtain ⟨h1, h2⟩ := isPositiveRecord_foldMinus (D.FS.cut j) (D.FS.κ_pos L b i)
      exact ⟨h1, by simp only [pieceLm, pieceG, Bool.false_eq_true, ↓reduceIte]; rw [h2]⟩
    · obtain ⟨h1, h2⟩ := isPositiveRecord_foldMinus (D.FS.cut j) (D.FS.κ'_pos L b i)
      exact ⟨h1, by simp only [pieceLm, pieceG, ↓reduceIte]; rw [h2]⟩

omit [DecidableEq P] in
/-- The unselected factor `μ_𝔟` of the sharp-first pieces, with price one. -/
theorem pieceLp_none (j : D.FS.Tag) (b : PaperAtom J L) :
    pieceLp dec j b (Sum.inl none) = D.R.law p L b ∧ pieceG dec b (Sum.inl none) = 1 :=
  ⟨rfl, rfl⟩

variable (ω : Choice (D.CL.T L))

omit [DecidableEq P] in
/-- **The plus folded factors of the pieces under a selection** (other than `μ_𝔟` off the
selected set) are positive records with mass times selection factor equal to the price `g`. -/
theorem epieceLp_record (hκs : ∀ b i s, IsPositiveRecord ((dec b i).κs s)) (j : D.FS.Tag)
    (b : PaperAtom J L) (x : EPiece dec b) (hx : ¬ (x = Sum.inl none ∧ ω b = none)) :
    IsPositiveRecord (epieceLp dec ω j b x) ∧
      mass (epieceLp dec ω j b x) * TheoremCParam.selectionFactor a p D.S.selPre L b =
          epieceG dec ω b x := by
  rcases x with (_ | i) | ⟨i, s | t⟩
  · rcases hω : ω b with _ | te
    · exact absurd ⟨rfl, hω⟩ hx
    · have hrec : IsPositiveRecord (D.CL.D L b te.1 te.2) :=
        ⟨(D.CL.D_prob L b te.1 te.2).1, D.CL.D_unif L b te.1 te.2⟩
      obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) hrec
      refine ⟨by simp only [epieceLp, hω, Option.elim]; exact h1, ?_⟩
      simp only [epieceLp, epieceG, hω, Option.elim]
      rw [h2, mass_eq_one_of_prob (D.CL.D_prob L b te.1 te.2), one_mul]
  · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (D.GB.κu_pos L b i)
    exact ⟨h1, by simp only [epieceLp, epieceG]; rw [h2]⟩
  · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (hκs b i s)
    refine ⟨h1, ?_⟩
    simp only [epieceLp, epieceG]
    rw [h2, mass_eq_one_of_prob ((dec b i).prob s), one_mul]
  · cases t
    · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (D.FS.κ_pos L b i)
      exact ⟨h1, by simp only [epieceLp, epieceG, Bool.false_eq_true, ↓reduceIte]; rw [h2]⟩
    · obtain ⟨h1, h2⟩ := isPositiveRecord_foldPlus (D.FS.cut j) (D.FS.κ'_pos L b i)
      exact ⟨h1, by simp only [epieceLp, epieceG, ↓reduceIte]; rw [h2]⟩

end Sarkozy.EnvelopeInputsParam
