module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions17

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce360 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph360 = 0 := by
  exact moment_odd F hm1 graph360 (by decide +kernel)

theorem reduce361 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph361 = (1 : ℝ) * g10 F := by
  have h : moment F graph361 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph361 graph90 perm88 (1)
    intro x
    change chi (x 1 - x 4) * (chi (x 3 - x 4) * (chi (x 0 - x 4) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 0 - x 1) * (chi (x 5 - x 2) * (chi (x 3 - x 2) * (chi (x 0 - x 5) * (chi (x 0 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce362 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph362 = 0 := by
  have h : moment F graph362 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph362 [(0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce363 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph363 = 0 := by
  exact moment_odd F hm1 graph363 (by decide +kernel)

theorem reduce364 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph364 = 0 := by
  exact moment_odd F hm1 graph364 (by decide +kernel)

theorem reduce365 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph365 = (-1 : ℝ) * g10 F := by
  have h : moment F graph365 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph365 graph90 perm89 (-1)
    intro x
    change chi (x 3 - x 4) * (chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 5 - x 2) * (chi (x 1 - x 2) * (chi (x 1 - x 5) * (chi (x 0 - x 5) * (chi (x 0 - x 1) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce366 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph366 = 0 := by
  exact moment_odd F hm1 graph366 (by decide +kernel)

theorem reduce367 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph367 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph367 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph367 graph120 perm90 (1)
    intro x
    change chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 1 - x 0) * (chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 1 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce368 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph368 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph368 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph368 graph120 perm91 (1)
    intro x
    change chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 4 - x 3) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 2 - x 4) * (chi (x 0 - x 4) * (chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 1 - x 0) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce369 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph369 = 0 := by
  exact moment_odd F hm1 graph369 (by decide +kernel)

theorem reduce370 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph370 = 0 := by
  exact moment_odd F hm1 graph370 (by decide +kernel)

theorem reduce371 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph371 = 0 := by
  have h : moment F graph371 = (-1 : ℝ) * moment F ([(4, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph371 [(4, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 2 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce372 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph372 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph372 = (-1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph372 graph112 perm92 (-1)
    intro x
    change chi (x 0 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce373 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph373 = 0 := by
  exact moment_odd F hm1 graph373 (by decide +kernel)

theorem reduce374 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph374 = 0 := by
  have h : moment F graph374 = (-1 : ℝ) * moment F ([(4, 2), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph374 [(4, 2), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 4) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 2 (by decide +kernel)
    [(0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce375 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph375 = 0 := by
  exact moment_odd F hm1 graph375 (by decide +kernel)

theorem reduce376 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph376 = 0 := by
  exact moment_odd F hm1 graph376 (by decide +kernel)

theorem reduce377 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph377 = (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph377 = (-1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph377 graph120 perm93 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce378 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph378 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph378 = (-1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph378 graph112 perm94 (-1)
    intro x
    change chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce379 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph379 = 0 := by
  exact moment_odd F hm1 graph379 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
