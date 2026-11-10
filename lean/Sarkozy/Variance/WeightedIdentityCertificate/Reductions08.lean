module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions07

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce160 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph160 = 0 := by
  exact moment_odd F hm1 graph160 (by decide +kernel)

theorem reduce161 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph161 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph161 = (-1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph161 graph45 perm34 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 5) * (chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 4 - x 2) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

theorem reduce162 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph162 = 0 := by
  have h : moment F graph162 = (1 : ℝ) * moment F ([(1, 5), (0, 2), (0, 5), (2, 3), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph162 [(1, 5), (0, 2), (0, 5), (2, 3), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 1 5 (by decide +kernel)
    [(0, 2), (0, 5), (2, 3), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce163 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph163 = 0 := by
  exact moment_odd F hm1 graph163 (by decide +kernel)

theorem reduce164 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph164 = 0 := by
  exact moment_odd F hm1 graph164 (by decide +kernel)

theorem reduce165 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph165 = 0 := by
  have h : moment F graph165 = (-1 : ℝ) * moment F ([(3, 2), (0, 1), (0, 2), (0, 4), (0, 5), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph165 [(3, 2), (0, 1), (0, 2), (0, 4), (0, 5), (1, 5), (2, 4), (4, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 2 (by decide +kernel)
    [(0, 1), (0, 2), (0, 4), (0, 5), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce166 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph166 = 0 := by
  exact moment_odd F hm1 graph166 (by decide +kernel)

theorem reduce167 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph167 = 0 := by
  have h : moment F graph167 = (-1 : ℝ) * moment F graph167 := by
    apply moment_relabel F graph167 graph167 perm36 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 2 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 5) * (chi (x 1 - x 5) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce168 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph168 = 0 := by
  have h : moment F graph168 = (-1 : ℝ) * moment F graph168 := by
    apply moment_relabel F graph168 graph168 perm37 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 1 - x 5) * (chi (x 4 - x 5) * (chi (x 2 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce169 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph169 = 0 := by
  exact moment_odd F hm1 graph169 (by decide +kernel)

theorem reduce170 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph170 = 0 := by
  exact moment_odd F hm1 graph170 (by decide +kernel)

theorem reduce171 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph171 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph171 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph171 graph64 perm38 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (chi (x 4 - x 3) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 1 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce172 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph172 = 0 := by
  have h : moment F graph172 = (1 : ℝ) * moment F ([(1, 5), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph172 [(1, 5), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 5 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce173 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph173 = 0 := by
  exact moment_odd F hm1 graph173 (by decide +kernel)

theorem reduce174 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph174 = 0 := by
  have h : moment F graph174 = (-1 : ℝ) * moment F graph174 := by
    apply moment_relabel F graph174 graph174 perm39 (-1)
    intro x
    change chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  linarith

theorem reduce175 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph175 = 0 := by
  exact moment_odd F hm1 graph175 (by decide +kernel)

theorem reduce176 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph176 = 0 := by
  exact moment_odd F hm1 graph176 (by decide +kernel)

theorem reduce177 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph177 = (1 : ℝ) * g10 F := by
  have h : moment F graph177 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph177 graph90 perm40 (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 2 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 2) * (chi (x 4 - x 1) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce178 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph178 = 0 := by
  have h : moment F graph178 = (1 : ℝ) * moment F ([(0, 2), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph178 [(0, 2), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce179 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph179 = 0 := by
  exact moment_odd F hm1 graph179 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
