module

public import Sarkozy.EnvelopeInputs.CoupledPrices
public import Sarkozy.EnvelopeInputsParam.SharpFirstCoupled

@[expose] public section



open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.Structured

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ)

/-- The weight of a coupled piece without its selection factor. -/
noncomputable def cpieceW (b : PaperAtom J L) : CPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some h) => mass (D.FS.κa L b h)
  | Sum.inr (i, none) => mass (D.FS.κ L b i) * D.FS.dconst L b i
  | Sum.inr (i, some t) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

/-- Whether a coupled piece is `μ_𝔟` (the outside reference, unselected). -/
def cpieceIsMu (b : PaperAtom J L) : CPiece D L b → Bool
  | Sum.inl none => true
  | _ => false

omit [DecidableEq P] in
theorem cpieceW_nonneg (b : PaperAtom J L) (x : CPiece D L b) : 0 ≤ cpieceW D L b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b hh).1
  · exact mul_nonneg (TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
      (D.FS.dconst_nonneg L b i)
  · cases t
    · exact TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
/-- **The price of a coupled piece is its weight times its selection factor** (one for `μ_𝔟`). -/
theorem cpieceG_eq (b : PaperAtom J L) (x : CPiece D L b) :
    cpieceG D L b x = cpieceW D L b x *
      (if cpieceIsMu D L b x then 1 else TheoremCParam.selectionFactor a p D.S.selPre L b) := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · simp [cpieceG, cpieceW, cpieceIsMu]
  · simp [cpieceG, cpieceW, cpieceIsMu]
  · simp only [cpieceG, cpieceW, cpieceIsMu, Bool.false_eq_true, ↓reduceIte]
    unfold TheoremCParam.FirstStage.dprice sharpPrice
    ring
  · simp [cpieceG, cpieceW, cpieceIsMu]

omit [DecidableEq P] in
/-- `∏_𝔟 g_𝔟(f_𝔟) = (∏_𝔟 w_𝔟(f_𝔟)) ∏_{𝔟 selected} sel_𝔟`. -/
theorem prod_cpieceG_eq (f : ∀ b, CPiece D L b) :
    ∏ b, cpieceG D L b (f b) = (∏ b, cpieceW D L b (f b)) *
      ∏ b ∈ univ.filter (fun b => cpieceIsMu D L b (f b) = false),
        TheoremCParam.selectionFactor a p D.S.selPre L b := by
  rw [Finset.prod_congr rfl fun b _ => cpieceG_eq D L b (f b), Finset.prod_mul_distrib,
    Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hb : cpieceIsMu D L b (f b) = true <;> simp [hb]

omit [DecidableEq P] in
/-- **The per-term bound of `hcoup` from the coupled bound in weight form**: if
`|Y_f| ≤ (∏_𝔟 w_𝔟(f_𝔟)) Q + R` with `Q ≤ (∏_{selected} sel) K` and `R ≤ (∏_𝔟 m_𝔟(f_𝔟)) rem`,
then `|Y_f| ≤ (∏_𝔟 g_𝔟(f_𝔟)) K + (∏_𝔟 m_𝔟(f_𝔟)) rem`. -/
theorem coupled_term_of_weights (f : ∀ b, CPiece D L b) {Yf Q R K rem : ℝ}
    (hY : |Yf| ≤ (∏ b, cpieceW D L b (f b)) * Q + R)
    (hQ : Q ≤ (∏ b ∈ univ.filter (fun b => cpieceIsMu D L b (f b) = false),
      TheoremCParam.selectionFactor a p D.S.selPre L b) * K)
    (hR : R ≤ (∏ b, cpieceM D L b (f b)) * rem) :
    |Yf| ≤ (∏ b, cpieceG D L b (f b)) * K + (∏ b, cpieceM D L b (f b)) * rem := by
  have hW : 0 ≤ ∏ b, cpieceW D L b (f b) := Finset.prod_nonneg fun b _ => cpieceW_nonneg D L b _
  have h1 := mul_le_mul_of_nonneg_left hQ hW
  rw [prod_cpieceG_eq D L f]
  nlinarith

end Sarkozy.EnvelopeInputsParam
