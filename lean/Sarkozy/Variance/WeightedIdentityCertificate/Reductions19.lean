module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions18

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce380 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph380 = 0 := by
  exact moment_odd F hm1 graph380 (by decide +kernel)

theorem reduce381 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph381 = (1 : ℝ) * g10 F := by
  have h : moment F graph381 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph381 graph90 perm30 (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 4) * (chi (x 3 - x 4) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 2) * (chi (x 3 - x 2) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce382 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph382 = 0 := by
  exact moment_odd F hm1 graph382 (by decide +kernel)

theorem reduce383 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph383 = (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph383 = (-1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph383 graph120 perm95 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (chi (x 1 - x 2) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce384 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph384 = (-1 : ℝ) * g10 F := by
  have h : moment F graph384 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph384 graph90 perm96 (-1)
    intro x
    change chi (x 1 - x 2) * (chi (x 5 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 3 - x 4) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce385 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph385 = 0 := by
  exact moment_odd F hm1 graph385 (by decide +kernel)

theorem reduce386 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph386 = 0 := by
  exact moment_odd F hm1 graph386 (by decide +kernel)

theorem reduce387 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph387 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph387 = (-1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph387 graph112 perm1 (-1)
    intro x
    change chi (x 3 - x 2) * (chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 4) * (chi (x 1 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce388 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph388 = 0 := by
  have h : moment F graph388 = (1 : ℝ) * moment F ([(1, 2), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph388 [(1, 2), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 2 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce389 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph389 = 0 := by
  exact moment_odd F hm1 graph389 (by decide +kernel)

theorem reduce390 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph390 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph390 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph390 graph112 perm97 (1)
    intro x
    change chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 2) * (chi (x 1 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce391 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph391 = 0 := by
  exact moment_odd F hm1 graph391 (by decide +kernel)

theorem reduce392 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph392 = 0 := by
  exact moment_odd F hm1 graph392 (by decide +kernel)

theorem reduce393 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph393 = (-1 : ℝ) * g10 F := by
  have h : moment F graph393 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph393 graph90 perm11 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 5) * (chi (x 2 - x 5) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 3 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce394 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph394 = 0 := by
  have h : moment F graph394 = (1 : ℝ) * moment F ([(1, 2), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph394 [(1, 2), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 2 (by decide +kernel)
    [(0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce395 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph395 = 0 := by
  exact moment_odd F hm1 graph395 (by decide +kernel)

theorem reduce396 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph396 = 0 := by
  exact moment_odd F hm1 graph396 (by decide +kernel)

theorem reduce397 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph397 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph397 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph397 graph120 perm98 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 5) * (chi (x 3 - x 1) * (chi (x 2 - x 1) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 4 - x 2) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce398 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph398 = 0 := by
  exact moment_odd F hm1 graph398 (by decide +kernel)

theorem reduce399 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph399 = (-1 : ℝ) * g10 F := by
  have h : moment F graph399 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph399 graph90 perm99 (-1)
    intro x
    change chi (x 5 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 5) * (chi (x 0 - x 5) * (chi (x 0 - x 1) * (chi (x 4 - x 1) * (chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
