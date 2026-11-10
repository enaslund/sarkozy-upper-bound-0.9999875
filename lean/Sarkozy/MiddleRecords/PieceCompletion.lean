module

public import Sarkozy.MiddleRecords.CompletionData

/-!
# Completion and protection on all 33 middle pieces

This supplies the rational gates of `cert:record:frame-data` and
`rem:middle-weights`, using the exact source weights and rational input caps.
The spectral and row estimates underlying those caps remain separate.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Sarkozy.PartV Sarkozy.Labellings
open CompletionData

noncomputable def pieceWeights (i : Fin 33) : MiddleWeights :=
  (record i).weights (record_nonneg i)

noncomputable def pieceInputs (i : Fin 33) : MiddleInputs := (record i).inputs

/-- All thirteen completion inequalities on each of the paper's 33 pieces. -/
theorem pieceWeights_completes (i : Fin 33) : (pieceWeights i).Completes (pieceInputs i) :=
  (record i).completes_sound (record_nonneg i) (record_completes i)

/-- The fourteenth inequality: protection of the Gram bracket. -/
theorem pieceWeights_protects (i : Fin 33) : (pieceWeights i).Protects (pieceInputs i) :=
  (record i).protects_sound (record_nonneg i) (record_protects i)

theorem pieceInputs_nonneg (i : Fin 33) :
    0 ≤ (pieceInputs i).d ∧ 0 ≤ (pieceInputs i).d₁ ∧
      0 ≤ (pieceInputs i).f₁ ∧ 0 ≤ (pieceInputs i).f₂ ∧
      0 ≤ (pieceInputs i).h₁ ∧ 0 ≤ (pieceInputs i).h₂ ∧
      ∀ t, 0 ≤ (pieceInputs i).k t :=
  (record i).inputs_nonneg (record_nonneg i)

theorem pieceWeights_equalities (i : Fin 33) :
    (pieceWeights i).w .L = 1 ∧ (pieceWeights i).w .S = (pieceWeights i).w .D ∧
      (pieceWeights i).v .S = (pieceWeights i).v .D :=
  ⟨(pieceWeights i).w_L, rfl, rfl⟩

/-- The source checks a stronger matching-type gate than `MiddleWeights.Completes`. -/
theorem pieceWeights_strong_matching (i : Fin 33) :
    2 * (pieceInputs i).k .S * (pieceWeights i).w .S ≤ (pieceWeights i).v .S := by
  change 2 * ((record i).kE : ℝ) * (record i).wD ≤ (record i).vD
  exact_mod_cast record_strong_matching i

/-- The rounding error in protection is strictly less than the printed `10^-9`. -/
theorem pieceWeights_protection_rounding (i : Fin 33) :
    0 ≤ (pieceWeights i).v .D - 2 * (pieceInputs i).k .D * (pieceWeights i).w .D ∧
      (pieceWeights i).v .D - 2 * (pieceInputs i).k .D * (pieceWeights i).w .D <
        1 / 10 ^ 9 := by
  constructor
  · exact sub_nonneg.mpr (pieceWeights_protects i)
  · change ((record i).vD : ℝ) - 2 * (record i).kD * (record i).wD < 1 / 10 ^ 9
    have h := (Rat.cast_lt (K := ℝ)).mpr (record_rounding i)
    push_cast at h
    exact h

theorem pieceWeights_leading_rounding (i : Fin 33) :
    0 ≤ (pieceWeights i).w .D - (pieceInputs i).d ∧
      (pieceWeights i).w .D - (pieceInputs i).d < 1 / 10 ^ 12 ∧
      0 ≤ (pieceWeights i).v .L - (pieceInputs i).k .L ∧
      (pieceWeights i).v .L - (pieceInputs i).k .L < 1 / 10 ^ 12 := by
  have hc := pieceWeights_completes i
  refine ⟨sub_nonneg.mpr hc.1, ?_, ?_, ?_⟩
  · change ((record i).wD : ℝ) - (record i).d < 1 / 10 ^ 12
    have h := (Rat.cast_lt (K := ℝ)).mpr (record_leading_rounding i).1
    push_cast at h
    exact h
  · have h := hc.2.2.2.2.2.2.2.2 .L
    rw [(pieceWeights i).w_L, mul_one] at h
    exact sub_nonneg.mpr h
  · change ((record i).vL : ℝ) - (record i).kL < 1 / 10 ^ 12
    have h := (Rat.cast_lt (K := ℝ)).mpr (record_leading_rounding i).2
    push_cast at h
    exact h

/-- The lower bound `5.7 × 10^-5` in `rem:middle-weights` holds on every piece. -/
theorem pieceWeights_root_slack (i : Fin 33) :
    (57 : ℝ) / 10 ^ 6 < (pieceWeights i).v .D - (pieceInputs i).d₁ * (pieceWeights i).v .L := by
  change (57 : ℝ) / 10 ^ 6 < (record i).vD - (record i).d₁ * (record i).vL
  have h := (Rat.cast_lt (K := ℝ)).mpr (record_root_slack i)
  push_cast at h
  exact h

end Sarkozy.MiddleRecords
