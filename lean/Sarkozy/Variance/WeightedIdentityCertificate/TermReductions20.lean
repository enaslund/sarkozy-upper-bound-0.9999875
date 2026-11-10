module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term320 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 0 = 0 := by
  have h : moment F (termGraph 4 0 0) =
      (1 : ℝ) * moment F graph370 := by
    apply moment_pointwise F (termGraph 4 0 0) graph370 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 0) = _
  rw [h, reduce370 F hF hm1]
  ring

theorem term321 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 1 = 0 := by
  have h : moment F (termGraph 4 0 1) =
      (1 : ℝ) * moment F graph371 := by
    apply moment_pointwise F (termGraph 4 0 1) graph371 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 1) = _
  rw [h, reduce371 F hF hm1]
  ring

theorem term322 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 2 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 4 0 2) =
      (1 : ℝ) * moment F graph372 := by
    apply moment_pointwise F (termGraph 4 0 2) graph372 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 2) = _
  rw [h, reduce372 F hF hm1]
  ring

theorem term323 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 3 = 0 := by
  have h : moment F (termGraph 4 0 3) =
      (1 : ℝ) * moment F graph373 := by
    apply moment_pointwise F (termGraph 4 0 3) graph373 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 3) = _
  rw [h, reduce373 F hF hm1]
  ring

theorem term324 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 4 = 0 := by
  have h : moment F (termGraph 4 0 4) =
      (-1 : ℝ) * moment F graph374 := by
    apply moment_pointwise F (termGraph 4 0 4) graph374 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 4) = _
  rw [h, reduce374 F hF hm1]
  ring

theorem term325 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 5 = 0 := by
  have h : moment F (termGraph 4 0 5) =
      (-1 : ℝ) * moment F graph375 := by
    apply moment_pointwise F (termGraph 4 0 5) graph375 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 5) = _
  rw [h, reduce375 F hF hm1]
  ring

theorem term326 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 6 = 0 := by
  have h : moment F (termGraph 4 0 6) =
      (-1 : ℝ) * moment F graph376 := by
    apply moment_pointwise F (termGraph 4 0 6) graph376 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 6) = _
  rw [h, reduce376 F hF hm1]
  ring

theorem term327 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 7 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 4 0 7) =
      (-1 : ℝ) * moment F graph377 := by
    apply moment_pointwise F (termGraph 4 0 7) graph377 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 7) = _
  rw [h, reduce377 F hF hm1]
  ring

theorem term328 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 8 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 4 0 8) =
      (1 : ℝ) * moment F graph378 := by
    apply moment_pointwise F (termGraph 4 0 8) graph378 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 8) = _
  rw [h, reduce378 F hF hm1]
  ring

theorem term329 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 9 = 0 := by
  have h : moment F (termGraph 4 0 9) =
      (1 : ℝ) * moment F graph379 := by
    apply moment_pointwise F (termGraph 4 0 9) graph379 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 9) = _
  rw [h, reduce379 F hF hm1]
  ring

theorem term330 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 10 = 0 := by
  have h : moment F (termGraph 4 0 10) =
      (1 : ℝ) * moment F graph380 := by
    apply moment_pointwise F (termGraph 4 0 10) graph380 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 10) = _
  rw [h, reduce380 F hF hm1]
  ring

theorem term331 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 11 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 4 0 11) =
      (1 : ℝ) * moment F graph381 := by
    apply moment_pointwise F (termGraph 4 0 11) graph381 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 11) = _
  rw [h, reduce381 F hF hm1]
  ring

theorem term332 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 12 = 0 := by
  have h : moment F (termGraph 4 0 12) =
      (-1 : ℝ) * moment F graph382 := by
    apply moment_pointwise F (termGraph 4 0 12) graph382 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 12) = _
  rw [h, reduce382 F hF hm1]
  ring

theorem term333 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 13 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 4 0 13) =
      (-1 : ℝ) * moment F graph383 := by
    apply moment_pointwise F (termGraph 4 0 13) graph383 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 13) = _
  rw [h, reduce383 F hF hm1]
  ring

theorem term334 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 14 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 4 0 14) =
      (-1 : ℝ) * moment F graph384 := by
    apply moment_pointwise F (termGraph 4 0 14) graph384 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 14) = _
  rw [h, reduce384 F hF hm1]
  ring

theorem term335 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 0 15 = 0 := by
  have h : moment F (termGraph 4 0 15) =
      (-1 : ℝ) * moment F graph385 := by
    apply moment_pointwise F (termGraph 4 0 15) graph385 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 4 0 15) = _
  rw [h, reduce385 F hF hm1]
  ring

theorem block20 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 4 0 h) = (2 : ℝ) * (q F) ^ 2 + (-6 : ℝ) * (q F) ^ 3 + (4 : ℝ) * (q F) ^ 4 + (2 : ℝ) * g10 F + (2 : ℝ) * (q F) ^ 1 * g5 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term320 F hF hm1, term321 F hF hm1, term322 F hF hm1, term323 F hF hm1, term324 F hF hm1, term325 F hF hm1, term326 F hF hm1, term327 F hF hm1, term328 F hF hm1, term329 F hF hm1, term330 F hF hm1, term331 F hF hm1, term332 F hF hm1, term333 F hF hm1, term334 F hF hm1, term335 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
