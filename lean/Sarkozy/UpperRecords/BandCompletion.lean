module

public import Sarkozy.UpperRecords.CompletionData
public import Sarkozy.PartVLaws.UpperCompletionBridge

/-!
# The 32,550 upper-band completion inequalities

The exact source weights, inputs and statewise caps supply the real
`WeightsOK` hypothesis for every band. Their analytic validity on the
corresponding prime blocks is a separate obligation.
-/

@[expose] public section

namespace Sarkozy.UpperRecords

open Sarkozy.PartV Sarkozy.PartVLaws Sarkozy.FiveType.TwoCoord
open CompletionData

noncomputable def bandWeights (i : Fin 310) : UpperWeights :=
  (record i).weights (record_positive i)

def bandOrd (i : Fin 310) : FieldTy → CompletionInput := (record i).ordinary

def bandRes (i : Fin 310) : FieldTy → CompletionInput := (record i).reserved

noncomputable def bandCap (i : Fin 310) : PType → PType → ℝ := (record i).realCap

/-- All 105 completion gates for each of the 310 upper bands. -/
theorem bandWeightsOK (i : Fin 310) :
    WeightsOK (bandWeights i) (bandOrd i) (bandRes i) (bandCap i) :=
  (record i).weightsOK (record_positive i) (record_completes i)

theorem bandWeights_pos (i : Fin 310) :
    (∀ t₀ t₁, 0 < (bandWeights i).w t₀ t₁) ∧
      ∀ t₀ t₁, 0 < (bandWeights i).v t₀ t₁ :=
  (record i).weights_pos (record_positive i)

theorem bandCap_pos (i : Fin 310) (t₀ t₁ : PType) : 0 < bandCap i t₀ t₁ :=
  (record i).cap_pos (record_positive i) t₀ t₁

theorem band_budget (i : Fin 310) : 550 ≤ (record i).budget ∧ (record i).budget ≤ 886 :=
  (record_range i).2.2.2

theorem band_start_min (i : Fin 310) : (81 * 10 ^ 12 : ℝ) ≤ (record i).start := by
  have h : (P3 : ℝ) ≤ (record i).start := by exact_mod_cast (record_range i).1
  exact (show (81 * 10 ^ 12 : ℝ) ≤ P3 by norm_num [P3]).trans h

end Sarkozy.UpperRecords
