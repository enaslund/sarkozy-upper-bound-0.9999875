module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions13

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce280 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph280 = 0 := by
  exact moment_odd F hm1 graph280 (by decide +kernel)

theorem reduce281 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph281 = (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph281 = (-1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph281 graph120 perm67 (-1)
    intro x
    change chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 3 - x 4) * (chi (x 1 - x 5) * (chi (x 1 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce282 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph282 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph282 = (-1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph282 graph112 perm68 (-1)
    intro x
    change chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 1 - x 5) * (chi (x 0 - x 5) * (chi (x 2 - x 1) * (chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 0 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce283 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph283 = 0 := by
  exact moment_odd F hm1 graph283 (by decide +kernel)

theorem reduce284 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph284 = 0 := by
  exact moment_odd F hm1 graph284 (by decide +kernel)

theorem reduce285 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph285 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph285 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph285 graph120 perm69 (1)
    intro x
    change chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 4 - x 3) * (chi (x 1 - x 3) * (chi (x 0 - x 4) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce286 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph286 = 0 := by
  exact moment_odd F hm1 graph286 (by decide +kernel)

theorem reduce287 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph287 = (-1 : ℝ) * g10 F := by
  have h : moment F graph287 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph287 graph90 perm62 (-1)
    intro x
    change chi (x 0 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 4) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 2) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce288 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph288 = (-1 : ℝ) * g10 F := by
  have h : moment F graph288 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph288 graph90 perm63 (-1)
    intro x
    change chi (x 3 - x 4) * (chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce289 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph289 = 0 := by
  exact moment_odd F hm1 graph289 (by decide +kernel)

theorem reduce290 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph290 = 0 := by
  have h : moment F graph290 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (3, 5)] : Graph) := by
    apply moment_pointwise F graph290 [(0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (3, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (1, 5), (2, 3), (2, 4), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce291 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph291 = 0 := by
  exact moment_odd F hm1 graph291 (by decide +kernel)

theorem reduce292 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph292 = 0 := by
  exact moment_odd F hm1 graph292 (by decide +kernel)

theorem reduce293 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph293 = 0 := by
  have h : moment F graph293 = (-1 : ℝ) * moment F graph293 := by
    apply moment_relabel F graph293 graph293 perm70 (-1)
    intro x
    change chi (x 1 - x 5) * (chi (x 3 - x 5) * (chi (x 0 - x 5) * (chi (x 2 - x 1) * (chi (x 0 - x 1) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 0 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 3) (x 5)]
    ring
  linarith

theorem reduce294 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph294 = 0 := by
  exact moment_odd F hm1 graph294 (by decide +kernel)

theorem reduce295 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph295 = 0 := by
  have h : moment F graph295 = (-1 : ℝ) * moment F ([(4, 2), (0, 1), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph295 [(4, 2), (0, 1), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 4) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 2 (by decide +kernel)
    [(0, 1), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce296 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph296 = 0 := by
  have h : moment F graph296 = (-1 : ℝ) * moment F graph296 := by
    apply moment_relabel F graph296 graph296 perm18 (-1)
    intro x
    change chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 5 - x 3) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 1) * (1)))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  linarith

theorem reduce297 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph297 = 0 := by
  exact moment_odd F hm1 graph297 (by decide +kernel)

theorem reduce298 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph298 = 0 := by
  exact moment_odd F hm1 graph298 (by decide +kernel)

theorem reduce299 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph299 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph299 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph299 graph64 perm71 (1)
    intro x
    change chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
