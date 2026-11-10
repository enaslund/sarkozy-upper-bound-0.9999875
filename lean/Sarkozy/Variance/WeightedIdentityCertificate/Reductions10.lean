module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions09

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce200 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph200 = 0 := by
  exact moment_odd F hm1 graph200 (by decide +kernel)

theorem reduce201 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph201 = (-1 : ℝ) * g10 F := by
  have h : moment F graph201 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph201 graph90 perm31 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 0) * (chi (x 2 - x 5) * (chi (x 1 - x 5) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 1 - x 2) * (chi (x 1 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce202 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph202 = 0 := by
  have h : moment F graph202 = (1 : ℝ) * moment F ([(1, 5), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph202 [(1, 5), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 5 (by decide +kernel)
    [(0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce203 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph203 = 0 := by
  exact moment_odd F hm1 graph203 (by decide +kernel)

theorem reduce204 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph204 = 0 := by
  exact moment_odd F hm1 graph204 (by decide +kernel)

theorem reduce205 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph205 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph205 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph205 graph120 perm48 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (chi (x 3 - x 4) * (chi (x 2 - x 4) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 1 - x 2) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce206 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph206 = 0 := by
  exact moment_odd F hm1 graph206 (by decide +kernel)

theorem reduce207 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph207 = (-1 : ℝ) * g10 F := by
  have h : moment F graph207 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph207 graph90 perm49 (-1)
    intro x
    change chi (x 5 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 0 - x 3) * (chi (x 4 - x 3) * (chi (x 4 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce208 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph208 = (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph208 = (-1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph208 graph120 perm50 (-1)
    intro x
    change chi (x 4 - x 3) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 0 - x 4) * (chi (x 2 - x 4) * (chi (x 2 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 2) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce209 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph209 = 0 := by
  exact moment_odd F hm1 graph209 (by decide +kernel)

theorem reduce210 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph210 = 0 := by
  have h : moment F graph210 = (1 : ℝ) * moment F ([(3, 5), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4)] : Graph) := by
    apply moment_pointwise F graph210 [(3, 5), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 3) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 3 5 (by decide +kernel)
    [(0, 2), (0, 5), (1, 2), (1, 5), (2, 4)] (by decide +kernel), mul_zero]

theorem reduce211 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph211 = 0 := by
  exact moment_odd F hm1 graph211 (by decide +kernel)

theorem reduce212 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph212 = 0 := by
  exact moment_odd F hm1 graph212 (by decide +kernel)

theorem reduce213 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph213 = 0 := by
  have h : moment F graph213 = (1 : ℝ) * moment F ([(3, 5), (0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4)] : Graph) := by
    apply moment_pointwise F graph213 [(3, 5), (0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 3 5 (by decide +kernel)
    [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4)] (by decide +kernel), mul_zero]

theorem reduce214 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph214 = 0 := by
  exact moment_odd F hm1 graph214 (by decide +kernel)

theorem reduce215 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph215 = 0 := by
  have h : moment F graph215 = (-1 : ℝ) * moment F ([(4, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (3, 5)] : Graph) := by
    apply moment_pointwise F graph215 [(4, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (3, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 2 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce216 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph216 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph216 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph216 graph64 perm51 (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 5 - x 1) * (chi (x 3 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce217 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph217 = 0 := by
  exact moment_odd F hm1 graph217 (by decide +kernel)

theorem reduce218 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph218 = 0 := by
  exact moment_odd F hm1 graph218 (by decide +kernel)

theorem reduce219 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph219 = 0 := by
  have h : moment F graph219 = (-1 : ℝ) * moment F graph219 := by
    apply moment_relabel F graph219 graph219 perm14 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 2 - x 1) * (chi (x 3 - x 5) * (chi (x 3 - x 4) * (chi (x 2 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 3) (x 5)]
    ring
  linarith

end Sarkozy.Variance.WeightedIdentityCertificate
