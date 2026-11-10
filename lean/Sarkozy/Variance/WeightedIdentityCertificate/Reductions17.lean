module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions16

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce340 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph340 = 0 := by
  exact moment_odd F hm1 graph340 (by decide +kernel)

theorem reduce341 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph341 = (-1 : ℝ) * (q F) ^ 2 + (4 : ℝ) * (q F) ^ 3 + (-3 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph341 = (1 : ℝ) * moment F graph25 := by
    apply moment_relabel F graph341 graph25 perm58 (1)
    intro x
    change chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 0 - x 3) * (chi (x 1 - x 3) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 5) * (chi (x 1 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce25 F hF hm1]
  ring

theorem reduce342 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph342 = 0 := by
  exact moment_odd F hm1 graph342 (by decide +kernel)

theorem reduce343 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph343 = 0 := by
  have h : moment F graph343 = (1 : ℝ) * moment F ([(0, 1), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph343 [(0, 1), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 1 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce344 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph344 = 0 := by
  have h : moment F graph344 = (1 : ℝ) * moment F ([(0, 4), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph344 [(0, 4), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 4 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce345 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph345 = 0 := by
  exact moment_odd F hm1 graph345 (by decide +kernel)

theorem reduce346 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph346 = 0 := by
  exact moment_odd F hm1 graph346 (by decide +kernel)

theorem reduce347 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph347 = 0 := by
  have h : moment F graph347 = (1 : ℝ) * moment F ([(0, 1), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph347 [(0, 1), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 1 (by decide +kernel)
    [(1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce348 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph348 = 0 := by
  have h : moment F graph348 = (1 : ℝ) * moment F ([(0, 4), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph348 [(0, 4), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 4 (by decide +kernel)
    [(1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce349 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph349 = 0 := by
  exact moment_odd F hm1 graph349 (by decide +kernel)

theorem reduce350 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph350 = (-1 : ℝ) * g5 F := by
  have h : moment F graph350 = (-1 : ℝ) * moment F graph13 := by
    apply moment_relabel F graph350 graph13 perm84 (-1)
    intro x
    change chi (x 3 - x 1) * (chi (x 0 - x 1) * (chi (x 4 - x 1) * (chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, reduce13 F hF hm1]
  ring

theorem reduce351 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph351 = 0 := by
  exact moment_odd F hm1 graph351 (by decide +kernel)

theorem reduce352 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph352 = 0 := by
  exact moment_odd F hm1 graph352 (by decide +kernel)

theorem reduce353 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph353 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph353 = (-1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph353 graph45 perm85 (-1)
    intro x
    change chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 3 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 1) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

theorem reduce354 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph354 = 0 := by
  exact moment_odd F hm1 graph354 (by decide +kernel)

theorem reduce355 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph355 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph355 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph355 graph112 perm86 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 1 - x 2) * (chi (x 0 - x 2) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 0 - x 4) * (chi (x 0 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce356 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph356 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph356 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph356 graph112 perm87 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 5 - x 1) * (chi (x 2 - x 1) * (chi (x 0 - x 5) * (chi (x 0 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce357 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph357 = 0 := by
  exact moment_odd F hm1 graph357 (by decide +kernel)

theorem reduce358 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph358 = 0 := by
  have h : moment F graph358 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph358 [(0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce359 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph359 = 0 := by
  exact moment_odd F hm1 graph359 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
