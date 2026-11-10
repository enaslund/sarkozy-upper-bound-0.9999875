module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions11

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce240 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph240 = 0 := by
  exact moment_odd F hm1 graph240 (by decide +kernel)

theorem reduce241 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph241 = (-1 : ℝ) * g10 F := by
  have h : moment F graph241 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph241 graph90 perm57 (-1)
    intro x
    change chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 3) * (chi (x 2 - x 3) * (chi (x 1 - x 4) * (chi (x 1 - x 2) * (chi (x 5 - x 2) * (chi (x 5 - x 1) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 4)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce242 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph242 = (-1 : ℝ) * (q F) ^ 1 + (3 : ℝ) * (q F) ^ 2 + (-2 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph242 = (-1 : ℝ) * moment F graph7 := by
    apply moment_relabel F graph242 graph7 perm58 (-1)
    intro x
    change chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 1 - x 3) * (chi (x 4 - x 0) * (chi (x 1 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 4)]
    ring
  rw [h, reduce7 F hF hm1]
  ring

theorem reduce243 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph243 = 0 := by
  exact moment_odd F hm1 graph243 (by decide +kernel)

theorem reduce244 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph244 = 0 := by
  exact moment_odd F hm1 graph244 (by decide +kernel)

theorem reduce245 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph245 = (-1 : ℝ) * g5 F := by
  have h : moment F graph245 = (-1 : ℝ) * moment F graph13 := by
    apply moment_relabel F graph245 graph13 perm59 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 2 - x 3) * (chi (x 4 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, reduce13 F hF hm1]
  ring

theorem reduce246 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph246 = 0 := by
  exact moment_odd F hm1 graph246 (by decide +kernel)

theorem reduce247 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph247 = 0 := by
  have h : moment F graph247 = (-1 : ℝ) * moment F ([(3, 1), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph247 [(3, 1), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 1 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce248 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph248 = 0 := by
  have h : moment F graph248 = (-1 : ℝ) * moment F ([(3, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph248 [(3, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 1 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce249 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph249 = 0 := by
  exact moment_odd F hm1 graph249 (by decide +kernel)

theorem reduce250 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph250 = 0 := by
  exact moment_odd F hm1 graph250 (by decide +kernel)

theorem reduce251 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph251 = 0 := by
  have h : moment F graph251 = (1 : ℝ) * moment F ([(3, 4), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph251 [(3, 4), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 4 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 3 4 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce252 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph252 = 0 := by
  have h : moment F graph252 = (1 : ℝ) * moment F ([(3, 4), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph252 [(3, 4), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 4 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 3 4 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce253 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph253 = 0 := by
  exact moment_odd F hm1 graph253 (by decide +kernel)

theorem reduce254 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph254 = (-1 : ℝ) * (q F) ^ 2 + (4 : ℝ) * (q F) ^ 3 + (-3 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph254 = (1 : ℝ) * moment F graph25 := by
    apply moment_relabel F graph254 graph25 perm60 (1)
    intro x
    change chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 1 - x 5) * (chi (x 4 - x 1) * (1)))))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce25 F hF hm1]
  ring

theorem reduce255 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph255 = 0 := by
  exact moment_odd F hm1 graph255 (by decide +kernel)

theorem reduce256 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph256 = 0 := by
  exact moment_odd F hm1 graph256 (by decide +kernel)

theorem reduce257 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph257 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph257 = (1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph257 graph45 perm60 (1)
    intro x
    change chi (x 0 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 1 - x 5) * (chi (x 4 - x 1) * (1)))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

theorem reduce258 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph258 = 0 := by
  have h : moment F graph258 = (1 : ℝ) * moment F ([(0, 2), (1, 2), (1, 5), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph258 [(0, 2), (1, 2), (1, 5), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 2), (1, 5), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce259 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph259 = 0 := by
  exact moment_odd F hm1 graph259 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
