module

public import Sarkozy.EnvelopeInputs.EnvelopeCoupledPrices
public import Sarkozy.EnvelopeInputsParam.EnvelopeCoupled
public import Sarkozy.EnvelopeInputsParam.CoupledPrices

@[expose] public section



open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ) (ω : Choice (D.CL.T L))

/-- The weight of a coupled envelope piece without its selection factor: one for the entry
factor (`μ_𝔟` or a selected envelope, both probability measures). -/
noncomputable def ecpieceW (b : PaperAtom J L) : CEPiece D L b → ℝ
  | Sum.inl none => 1
  | Sum.inl (some i) => mass (D.GB.κu L b i)
  | Sum.inr (i, none) => mass (D.FS.κ L b i) * D.FS.dconst L b i
  | Sum.inr (i, some t) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

/-- Whether a coupled envelope piece is `μ_𝔟` (the entry factor off the selected set). -/
def ecpieceIsMu (b : PaperAtom J L) : CEPiece D L b → Bool
  | Sum.inl none => !(ω b).isSome
  | _ => false

omit [DecidableEq P] in
theorem ecpieceW_nonneg (b : PaperAtom J L) (x : CEPiece D L b) : 0 ≤ ecpieceW D L b x := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1
  · exact mul_nonneg (TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
      (D.FS.dconst_nonneg L b i)
  · cases t
    · exact TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCParam.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

omit [DecidableEq P] in
/-- **The price of a coupled envelope piece is its weight times its selection factor.** -/
theorem ecpieceG_eq (b : PaperAtom J L) (x : CEPiece D L b) :
    ecpieceG D L ω b x = ecpieceW D L b x *
      (if ecpieceIsMu D L ω b x then 1 else TheoremCParam.selectionFactor a p D.S.selPre L b) := by
  rcases x with (_ | i) | ⟨i, _ | t⟩
  · unfold ecpieceG ecpieceW ecpieceIsMu
    rcases ω b with _ | te <;> simp
  · simp [ecpieceG, ecpieceW, ecpieceIsMu]
  · simp only [ecpieceG, ecpieceW, ecpieceIsMu, Bool.false_eq_true, ↓reduceIte]
    unfold TheoremCParam.FirstStage.dprice sharpPrice
    ring
  · simp [ecpieceG, ecpieceW, ecpieceIsMu]

omit [DecidableEq P] in
/-- `∏_𝔟 g_𝔟(f_𝔟) = (∏_𝔟 w_𝔟(f_𝔟)) ∏_{𝔟 selected} sel_𝔟` under a selection. -/
theorem prod_ecpieceG_eq (f : ∀ b, CEPiece D L b) :
    ∏ b, ecpieceG D L ω b (f b) = (∏ b, ecpieceW D L b (f b)) *
      ∏ b ∈ univ.filter (fun b => ecpieceIsMu D L ω b (f b) = false),
        TheoremCParam.selectionFactor a p D.S.selPre L b := by
  rw [Finset.prod_congr rfl fun b _ => ecpieceG_eq D L ω b (f b), Finset.prod_mul_distrib,
    Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hb : ecpieceIsMu D L ω b (f b) = true <;> simp [hb]

omit [DecidableEq P] in
/-- **The coupled envelope per-term bound from the coupled bound in weight form.** -/
theorem envelope_term_of_weights (f : ∀ b, CEPiece D L b) {Yf Q R K rem : ℝ}
    (hY : |Yf| ≤ (∏ b, ecpieceW D L b (f b)) * Q + R)
    (hQ : Q ≤ (∏ b ∈ univ.filter (fun b => ecpieceIsMu D L ω b (f b) = false),
      TheoremCParam.selectionFactor a p D.S.selPre L b) * K)
    (hR : R ≤ (∏ b, ecpieceM D L b (f b)) * rem) :
    |Yf| ≤ (∏ b, ecpieceG D L ω b (f b)) * K + (∏ b, ecpieceM D L b (f b)) * rem := by
  have hW : 0 ≤ ∏ b, ecpieceW D L b (f b) :=
    Finset.prod_nonneg fun b _ => ecpieceW_nonneg D L b _
  have h1 := mul_le_mul_of_nonneg_left hQ hW
  rw [prod_ecpieceG_eq D L ω f]
  nlinarith

end Sarkozy.EnvelopeInputsParam
