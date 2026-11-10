module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions12

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce260 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph260 = 0 := by
  exact moment_odd F hm1 graph260 (by decide +kernel)

theorem reduce261 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph261 = 0 := by
  have h : moment F graph261 = (1 : ℝ) * moment F ([(3, 5), (0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph261 [(3, 5), (0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 3 5 (by decide +kernel)
    [(0, 1), (0, 2), (0, 4), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce262 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph262 = 0 := by
  exact moment_odd F hm1 graph262 (by decide +kernel)

theorem reduce263 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph263 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph263 = (1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph263 graph54 perm61 (1)
    intro x
    change chi (x 0 - x 4) * (chi (x 2 - x 4) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 3 - x 2) * (chi (x 1 - x 5) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce264 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph264 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph264 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph264 graph64 perm62 (-1)
    intro x
    change chi (x 3 - x 4) * (chi (x 2 - x 4) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 2 - x 3) * (chi (x 1 - x 5) * (chi (x 1 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce265 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph265 = 0 := by
  exact moment_odd F hm1 graph265 (by decide +kernel)

theorem reduce266 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph266 = 0 := by
  exact moment_odd F hm1 graph266 (by decide +kernel)

theorem reduce267 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph267 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph267 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph267 graph64 perm63 (1)
    intro x
    change chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce268 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph268 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph268 = (-1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph268 graph54 perm64 (-1)
    intro x
    change chi (x 2 - x 4) * (chi (x 0 - x 4) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 0 - x 2) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce269 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph269 = 0 := by
  exact moment_odd F hm1 graph269 (by decide +kernel)

theorem reduce270 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph270 = 0 := by
  have h : moment F graph270 = (1 : ℝ) * moment F ([(0, 2), (1, 2), (1, 3), (1, 5), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph270 [(0, 2), (1, 2), (1, 3), (1, 5), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce271 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph271 = 0 := by
  exact moment_odd F hm1 graph271 (by decide +kernel)

theorem reduce272 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph272 = 0 := by
  exact moment_odd F hm1 graph272 (by decide +kernel)

theorem reduce273 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph273 = 0 := by
  have h : moment F graph273 = (-1 : ℝ) * moment F graph273 := by
    apply moment_relabel F graph273 graph273 perm65 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 5) * (chi (x 3 - x 5) * (chi (x 3 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 3) (x 5), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce274 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph274 = 0 := by
  exact moment_odd F hm1 graph274 (by decide +kernel)

theorem reduce275 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph275 = 0 := by
  have h : moment F graph275 = (1 : ℝ) * moment F ([(3, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph275 [(3, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 3 5 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce276 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph276 = 0 := by
  have h : moment F graph276 = (1 : ℝ) * moment F ([(3, 5), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph276 [(3, 5), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 3 5 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce277 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph277 = 0 := by
  exact moment_odd F hm1 graph277 (by decide +kernel)

theorem reduce278 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph278 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph278 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph278 graph112 perm66 (1)
    intro x
    change chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 0 - x 2) * (chi (x 5 - x 1) * (chi (x 0 - x 3) * (chi (x 0 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce279 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph279 = 0 := by
  exact moment_odd F hm1 graph279 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
