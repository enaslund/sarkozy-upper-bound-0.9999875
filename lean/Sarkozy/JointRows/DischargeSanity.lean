module

public import Sarkozy.JointRows.Discharge
public import Sarkozy.FiveType.JointBlocksSanity

/-!
# Non-vacuity of the discharged corollary

The toy block of `FiveType/JointBlocksSanity.lean` (one prime, the uniform law on `Fin 2`,
`T_E = T_F = 1`) satisfies every hypothesis of `joint_completion_blocks'`, which no longer asks
for `lem:joint-rows` (b), (c): they are proved (`jointRowsB_holds`, `jointRowsC_holds`).
-/

@[expose] public section

namespace Sarkozy.JointRows.DischargeSanity

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.FiveType.JointBlocksSanity

/-- **`cor:joint-completion-blocks` without hypotheses from 16_extraction, on the toy block.** -/
theorem toy_jointData' :
    ExactMarginals (blockLaw ν0) (prodKernel one) ∧
    Nonempty (JointData (blockLaw ν0) (prodKernel one) (fun x y => 1 * prodKernel one x y) 1 0
      (ET 0 1 (fun _ : Unit => 1 / 2)) (0 * (1 / 2)) (1 * (1 / 2))) := by
  obtain ⟨h1, ⟨J, -⟩, -⟩ := joint_completion_blocks' (r := 1 / 2) (cF := 1) (cE := 1) (kJ := 1)
    (h := 0) (H := 1) (υ := 0) (mb := 1) ν0 one one (fun _ => 1 / 2) exact_one
    (fun _ _ _ => rfl) mass_one (by norm_num) (fun _ => ⟨by norm_num, le_rfl⟩) zero_le_one
    zero_le_one (fun _ => formBound_zero (ν0 ()) foldCov_one (by norm_num))
    (fun _ => formBound_zero (ν0 ()) matchCov_one (by norm_num))
    (fun _ => jointBlockLower_zero (ν0 ()) matchCov_one foldCov_one (by norm_num)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (le_of_eq (nrm_zero' (blockLaw ν0) fun x => by rw [UL_one, sub_self]))
    (le_of_eq (nrm_zero' (blockLaw ν0) fun x => by rw [UR_one, sub_self]))
    (fun Φ => by
      rw [kf_zero (blockLaw ν0) (A := EB one)
        (fun x y => sectorKernel_zero (C := fun i => matchCov (one i)) (fun _ => matchCov_one) x y)]
      simp)
  exact ⟨h1, ⟨J⟩⟩

end Sarkozy.JointRows.DischargeSanity
