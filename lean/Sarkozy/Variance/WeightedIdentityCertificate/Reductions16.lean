module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions15

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce320 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph320 = 0 := by
  exact moment_odd F hm1 graph320 (by decide +kernel)

theorem reduce321 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph321 = (1 : ℝ) * g10 F := by
  have h : moment F graph321 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph321 graph90 perm77 (1)
    intro x
    change chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (chi (x 0 - x 3) * (chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce322 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph322 = 0 := by
  have h : moment F graph322 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph322 [(0, 5), (1, 2), (1, 5), (2, 3), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (1, 5), (2, 3), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce323 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph323 = 0 := by
  exact moment_odd F hm1 graph323 (by decide +kernel)

theorem reduce324 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph324 = 0 := by
  exact moment_odd F hm1 graph324 (by decide +kernel)

theorem reduce325 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph325 = 0 := by
  have h : moment F graph325 = (-1 : ℝ) * moment F ([(3, 2), (0, 1), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph325 [(3, 2), (0, 1), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 3) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 2 (by decide +kernel)
    [(0, 1), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce326 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph326 = 0 := by
  exact moment_odd F hm1 graph326 (by decide +kernel)

theorem reduce327 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph327 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph327 = (-1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph327 graph54 perm78 (-1)
    intro x
    change chi (x 0 - x 4) * (chi (x 2 - x 4) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 1) * (chi (x 2 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce328 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph328 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph328 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph328 graph64 perm79 (1)
    intro x
    change chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 1) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce329 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph329 = 0 := by
  exact moment_odd F hm1 graph329 (by decide +kernel)

theorem reduce330 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph330 = 0 := by
  exact moment_odd F hm1 graph330 (by decide +kernel)

theorem reduce331 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph331 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph331 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph331 graph64 perm80 (-1)
    intro x
    change chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 5 - x 1) * (chi (x 0 - x 1) * (chi (x 0 - x 5) * (chi (x 3 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce332 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph332 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph332 = (1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph332 graph54 perm81 (1)
    intro x
    change chi (x 0 - x 4) * (chi (x 2 - x 4) * (chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 5 - x 1) * (chi (x 0 - x 1) * (chi (x 0 - x 5) * (chi (x 2 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce333 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph333 = 0 := by
  exact moment_odd F hm1 graph333 (by decide +kernel)

theorem reduce334 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph334 = 0 := by
  have h : moment F graph334 = (1 : ℝ) * moment F ([(0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph334 [(0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce335 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph335 = 0 := by
  exact moment_odd F hm1 graph335 (by decide +kernel)

theorem reduce336 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph336 = 0 := by
  exact moment_odd F hm1 graph336 (by decide +kernel)

theorem reduce337 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph337 = 0 := by
  have h : moment F graph337 = (-1 : ℝ) * moment F graph337 := by
    apply moment_relabel F graph337 graph337 perm82 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  linarith

theorem reduce338 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph338 = (1 : ℝ) * (q F) ^ 1 + (-3 : ℝ) * (q F) ^ 2 + (2 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph338 = (1 : ℝ) * moment F graph7 := by
    apply moment_relabel F graph338 graph7 perm83 (1)
    intro x
    change chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 1 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 4)]
    ring
  rw [h, reduce7 F hF hm1]
  ring

theorem reduce339 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph339 = 0 := by
  exact moment_odd F hm1 graph339 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
