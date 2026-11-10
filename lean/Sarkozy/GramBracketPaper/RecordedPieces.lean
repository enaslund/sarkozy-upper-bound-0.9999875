module

public import Sarkozy.GramBracketPaper.ProvedTail
public import Sarkozy.PartVLaws.RecordedMiddle

/-!
# The Gram gate for the recorded middle pieces

Protection is automatic whenever the block specification uses the recorded
weights and inputs. Constructing that specification still requires its analytic
estimates and the assignment of the paper's blocks to their pieces.
-/

@[expose] public section

namespace Sarkozy.GramBracketPaper

open Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.MiddleRecords

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- The middle entries use the exact weights and input caps of one of the 33 pieces. -/
def UsesRecordedPieces {b : B} : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => ∃ i, M.W = pieceWeights i ∧ M.I = pieceInputs i
  | .middleIndividual M => ∃ i, M.W = pieceWeights i ∧ M.I = pieceInputs i
  | .middleCoherent M => ∃ i, M.W = pieceWeights i ∧ M.I = pieceInputs i

omit [Fintype B] in
theorem specProtects_of_recorded {b : B} {S : PaperBlockSpec blockOf b}
    (h : UsesRecordedPieces S) : specProtects S := by
  cases S with
  | upper U => trivial
  | middleUniform M =>
    obtain ⟨i, hw, hi⟩ := h
    dsimp only [specProtects]
    rw [hw, hi]
    exact pieceWeights_protects i
  | middleIndividual M =>
    obtain ⟨i, hw, hi⟩ := h
    dsimp only [specProtects]
    rw [hw, hi]
    exact pieceWeights_protects i
  | middleCoherent M =>
    obtain ⟨i, hw, hi⟩ := h
    dsimp only [specProtects]
    rw [hw, hi]
    exact pieceWeights_protects i

omit [Fintype B] in
theorem GramInputs.ofRecordedPieces (spec : ∀ b, PaperBlockSpec blockOf b)
    (h : ∀ b, UsesRecordedPieces (spec b)) : GramInputs blockOf spec where
  protects b := specProtects_of_recorded (h b)

end Sarkozy.GramBracketPaper
