module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term368 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 0 = 0 := by
  have h : moment F (termGraph 4 3 0) =
      (1 : ℝ) * moment F graph418 := by
    apply moment_pointwise F (termGraph 4 3 0) graph418 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 0) = _
  rw [h, reduce418 F hF hm1]
  ring

theorem term369 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 1 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 4 3 1) =
      (1 : ℝ) * moment F graph419 := by
    apply moment_pointwise F (termGraph 4 3 1) graph419 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 1) = _
  rw [h, reduce419 F hF hm1]
  ring

theorem term370 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 2 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 4 3 2) =
      (1 : ℝ) * moment F graph420 := by
    apply moment_pointwise F (termGraph 4 3 2) graph420 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 2) = _
  rw [h, reduce420 F hF hm1]
  ring

theorem term371 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 3 = 0 := by
  have h : moment F (termGraph 4 3 3) =
      (1 : ℝ) * moment F graph421 := by
    apply moment_pointwise F (termGraph 4 3 3) graph421 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 3) = _
  rw [h, reduce421 F hF hm1]
  ring

theorem term372 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 4 = 0 := by
  have h : moment F (termGraph 4 3 4) =
      (-1 : ℝ) * moment F graph422 := by
    apply moment_pointwise F (termGraph 4 3 4) graph422 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 4) = _
  rw [h, reduce422 F hF hm1]
  ring

theorem term373 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 5 = 0 := by
  have h : moment F (termGraph 4 3 5) =
      (-1 : ℝ) * moment F graph423 := by
    apply moment_pointwise F (termGraph 4 3 5) graph423 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 5) = _
  rw [h, reduce423 F hF hm1]
  ring

theorem term374 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 6 = 0 := by
  have h : moment F (termGraph 4 3 6) =
      (-1 : ℝ) * moment F graph424 := by
    apply moment_pointwise F (termGraph 4 3 6) graph424 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 6) = _
  rw [h, reduce424 F hF hm1]
  ring

theorem term375 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 7 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 4 3 7) =
      (-1 : ℝ) * moment F graph425 := by
    apply moment_pointwise F (termGraph 4 3 7) graph425 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 7) = _
  rw [h, reduce425 F hF hm1]
  ring

theorem term376 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 8 = 0 := by
  have h : moment F (termGraph 4 3 8) =
      (1 : ℝ) * moment F graph426 := by
    apply moment_pointwise F (termGraph 4 3 8) graph426 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 8) = _
  rw [h, reduce426 F hF hm1]
  ring

theorem term377 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 9 = 0 := by
  have h : moment F (termGraph 4 3 9) =
      (1 : ℝ) * moment F graph427 := by
    apply moment_pointwise F (termGraph 4 3 9) graph427 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 9) = _
  rw [h, reduce427 F hF hm1]
  ring

theorem term378 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 10 = 0 := by
  have h : moment F (termGraph 4 3 10) =
      (1 : ℝ) * moment F graph428 := by
    apply moment_pointwise F (termGraph 4 3 10) graph428 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 10) = _
  rw [h, reduce428 F hF hm1]
  ring

theorem term379 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 11 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 4 3 11) =
      (1 : ℝ) * moment F graph429 := by
    apply moment_pointwise F (termGraph 4 3 11) graph429 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 11) = _
  rw [h, reduce429 F hF hm1]
  ring

theorem term380 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 12 = 0 := by
  have h : moment F (termGraph 4 3 12) =
      (-1 : ℝ) * moment F graph430 := by
    apply moment_pointwise F (termGraph 4 3 12) graph430 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 12) = _
  rw [h, reduce430 F hF hm1]
  ring

theorem term381 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 13 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 4 3 13) =
      (-1 : ℝ) * moment F graph431 := by
    apply moment_pointwise F (termGraph 4 3 13) graph431 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 13) = _
  rw [h, reduce431 F hF hm1]
  ring

theorem term382 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 14 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 4 3 14) =
      (-1 : ℝ) * moment F graph432 := by
    apply moment_pointwise F (termGraph 4 3 14) graph432 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 14) = _
  rw [h, reduce432 F hF hm1]
  ring

theorem term383 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 4 3 15 = 0 := by
  have h : moment F (termGraph 4 3 15) =
      (-1 : ℝ) * moment F graph433 := by
    apply moment_pointwise F (termGraph 4 3 15) graph433 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 4 3 15) = _
  rw [h, reduce433 F hF hm1]
  ring

theorem block23 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 4 3 h) = (2 : ℝ) * (q F) ^ 2 + (-6 : ℝ) * (q F) ^ 3 + (4 : ℝ) * (q F) ^ 4 + (2 : ℝ) * g10 F + (2 : ℝ) * (q F) ^ 1 * g5 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term368 F hF hm1, term369 F hF hm1, term370 F hF hm1, term371 F hF hm1, term372 F hF hm1, term373 F hF hm1, term374 F hF hm1, term375 F hF hm1, term376 F hF hm1, term377 F hF hm1, term378 F hF hm1, term379 F hF hm1, term380 F hF hm1, term381 F hF hm1, term382 F hF hm1, term383 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
