module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions14

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce300 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph300 = 0 := by
  have h : moment F graph300 = (-1 : ℝ) * moment F graph300 := by
    apply moment_relabel F graph300 graph300 perm72 (-1)
    intro x
    change chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 4) * (chi (x 2 - x 4) * (chi (x 2 - x 3) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  linarith

theorem reduce301 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph301 = 0 := by
  exact moment_odd F hm1 graph301 (by decide +kernel)

theorem reduce302 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph302 = 0 := by
  have h : moment F graph302 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5)] : Graph) := by
    apply moment_pointwise F graph302 [(0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce303 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph303 = 0 := by
  exact moment_odd F hm1 graph303 (by decide +kernel)

theorem reduce304 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph304 = 0 := by
  exact moment_odd F hm1 graph304 (by decide +kernel)

theorem reduce305 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph305 = (1 : ℝ) * g10 F := by
  have h : moment F graph305 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph305 graph90 perm73 (1)
    intro x
    change chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 1) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (chi (x 0 - x 4) * (chi (x 3 - x 4) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce306 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph306 = 0 := by
  have h : moment F graph306 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph306 [(0, 5), (1, 2), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce307 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph307 = 0 := by
  exact moment_odd F hm1 graph307 (by decide +kernel)

theorem reduce308 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph308 = 0 := by
  exact moment_odd F hm1 graph308 (by decide +kernel)

theorem reduce309 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph309 = 0 := by
  have h : moment F graph309 = (-1 : ℝ) * moment F graph309 := by
    apply moment_relabel F graph309 graph309 perm74 (-1)
    intro x
    change chi (x 3 - x 5) * (chi (x 4 - x 5) * (chi (x 0 - x 5) * (chi (x 2 - x 3) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 0 - x 1) * (chi (x 0 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 3) (x 5), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce310 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph310 = 0 := by
  exact moment_odd F hm1 graph310 (by decide +kernel)

theorem reduce311 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph311 = 0 := by
  have h : moment F graph311 = (-1 : ℝ) * moment F graph311 := by
    apply moment_relabel F graph311 graph311 perm75 (-1)
    intro x
    change chi (x 2 - x 4) * (chi (x 5 - x 4) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 3 - x 1) * (chi (x 0 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  linarith

theorem reduce312 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph312 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph312 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph312 graph64 perm76 (-1)
    intro x
    change chi (x 3 - x 4) * (chi (x 2 - x 4) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce313 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph313 = 0 := by
  exact moment_odd F hm1 graph313 (by decide +kernel)

theorem reduce314 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph314 = 0 := by
  exact moment_odd F hm1 graph314 (by decide +kernel)

theorem reduce315 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph315 = 0 := by
  have h : moment F graph315 = (-1 : ℝ) * moment F graph315 := by
    apply moment_relabel F graph315 graph315 perm44 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 3 - x 4) * (chi (x 5 - x 4) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4)]
    ring
  linarith

theorem reduce316 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph316 = 0 := by
  have h : moment F graph316 = (1 : ℝ) * moment F ([(1, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph316 [(1, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 2 (by decide +kernel)
    [(0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce317 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph317 = 0 := by
  exact moment_odd F hm1 graph317 (by decide +kernel)

theorem reduce318 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph318 = 0 := by
  have h : moment F graph318 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph318 [(0, 5), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce319 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph319 = 0 := by
  exact moment_odd F hm1 graph319 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
