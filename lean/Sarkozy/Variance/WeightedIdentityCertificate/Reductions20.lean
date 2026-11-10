module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions19

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce400 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph400 = (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph400 = (-1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph400 graph120 perm100 (-1)
    intro x
    change chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 1 - x 5) * (chi (x 0 - x 5) * (chi (x 0 - x 1) * (chi (x 2 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 2) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce401 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph401 = 0 := by
  exact moment_odd F hm1 graph401 (by decide +kernel)

theorem reduce402 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph402 = 0 := by
  exact moment_odd F hm1 graph402 (by decide +kernel)

theorem reduce403 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph403 = 0 := by
  have h : moment F graph403 = (-1 : ℝ) * moment F ([(3, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph403 [(3, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 2 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce404 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph404 = 0 := by
  have h : moment F graph404 = (-1 : ℝ) * moment F ([(3, 2), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph404 [(3, 2), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 2 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce405 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph405 = 0 := by
  exact moment_odd F hm1 graph405 (by decide +kernel)

theorem reduce406 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph406 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph406 = (-1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph406 graph112 perm101 (-1)
    intro x
    change chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 0 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce407 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph407 = 0 := by
  exact moment_odd F hm1 graph407 (by decide +kernel)

theorem reduce408 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph408 = 0 := by
  exact moment_odd F hm1 graph408 (by decide +kernel)

theorem reduce409 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph409 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph409 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph409 graph120 perm102 (1)
    intro x
    change chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce410 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph410 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph410 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph410 graph112 perm103 (1)
    intro x
    change chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 3 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 1 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce411 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph411 = 0 := by
  exact moment_odd F hm1 graph411 (by decide +kernel)

theorem reduce412 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph412 = 0 := by
  exact moment_odd F hm1 graph412 (by decide +kernel)

theorem reduce413 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph413 = (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph413 = (-1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph413 graph120 perm104 (-1)
    intro x
    change chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (chi (x 5 - x 1) * (chi (x 0 - x 1) * (chi (x 0 - x 5) * (chi (x 4 - x 0) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce414 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph414 = 0 := by
  exact moment_odd F hm1 graph414 (by decide +kernel)

theorem reduce415 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph415 = (1 : ℝ) * g10 F := by
  have h : moment F graph415 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph415 graph90 perm79 (1)
    intro x
    change chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 1) * (chi (x 2 - x 1) * (chi (x 2 - x 5) * (chi (x 3 - x 2) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce416 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph416 = (1 : ℝ) * g10 F := by
  have h : moment F graph416 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph416 graph90 perm80 (1)
    intro x
    change chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 2) * (chi (x 5 - x 2) * (chi (x 3 - x 2) * (chi (x 5 - x 1) * (chi (x 0 - x 1) * (chi (x 0 - x 5) * (chi (x 3 - x 0) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce417 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph417 = 0 := by
  exact moment_odd F hm1 graph417 (by decide +kernel)

theorem reduce418 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph418 = 0 := by
  exact moment_odd F hm1 graph418 (by decide +kernel)

theorem reduce419 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph419 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph419 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph419 graph112 perm105 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 4) * (chi (x 1 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
