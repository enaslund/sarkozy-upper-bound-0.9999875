module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions08

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce180 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph180 = 0 := by
  exact moment_odd F hm1 graph180 (by decide +kernel)

theorem reduce181 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph181 = 0 := by
  have h : moment F graph181 = (-1 : ℝ) * moment F graph181 := by
    apply moment_relabel F graph181 graph181 perm41 (-1)
    intro x
    change chi (x 3 - x 2) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2)]
    ring
  linarith

theorem reduce182 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph182 = 0 := by
  exact moment_odd F hm1 graph182 (by decide +kernel)

theorem reduce183 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph183 = 0 := by
  have h : moment F graph183 = (-1 : ℝ) * moment F graph183 := by
    apply moment_relabel F graph183 graph183 perm42 (-1)
    intro x
    change chi (x 5 - x 4) * (chi (x 2 - x 4) * (chi (x 3 - x 5) * (chi (x 1 - x 5) * (chi (x 3 - x 2) * (chi (x 0 - x 2) * (chi (x 1 - x 3) * (chi (x 1 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 3) (x 5)]
    ring
  linarith

theorem reduce184 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph184 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph184 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph184 graph64 perm43 (-1)
    intro x
    change chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 5) * (chi (x 0 - x 5) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 0 - x 1) * (chi (x 0 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce185 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph185 = 0 := by
  exact moment_odd F hm1 graph185 (by decide +kernel)

theorem reduce186 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph186 = 0 := by
  exact moment_odd F hm1 graph186 (by decide +kernel)

theorem reduce187 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph187 = 0 := by
  have h : moment F graph187 = (-1 : ℝ) * moment F graph187 := by
    apply moment_relabel F graph187 graph187 perm44 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 3 - x 4) * (chi (x 5 - x 4) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4)]
    ring
  linarith

theorem reduce188 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph188 = 0 := by
  have h : moment F graph188 = (1 : ℝ) * moment F ([(1, 5), (0, 2), (0, 4), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph188 [(1, 5), (0, 2), (0, 4), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 5 (by decide +kernel)
    [(0, 2), (0, 4), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce189 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph189 = 0 := by
  exact moment_odd F hm1 graph189 (by decide +kernel)

theorem reduce190 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph190 = 0 := by
  have h : moment F graph190 = (1 : ℝ) * moment F ([(0, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph190 [(0, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 3), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce191 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph191 = 0 := by
  exact moment_odd F hm1 graph191 (by decide +kernel)

theorem reduce192 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph192 = 0 := by
  exact moment_odd F hm1 graph192 (by decide +kernel)

theorem reduce193 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph193 = (1 : ℝ) * g10 F := by
  have h : moment F graph193 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph193 graph90 perm45 (1)
    intro x
    change chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 4 - x 3) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce194 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph194 = 0 := by
  exact moment_odd F hm1 graph194 (by decide +kernel)

theorem reduce195 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph195 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph195 = (-1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph195 graph112 perm46 (-1)
    intro x
    change chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 2) * (chi (x 0 - x 3) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 0 - x 4) * (chi (x 0 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce196 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph196 = 0 := by
  have h : moment F graph196 = (1 : ℝ) * moment F ([(1, 5), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph196 [(1, 5), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 5 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce197 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph197 = 0 := by
  exact moment_odd F hm1 graph197 (by decide +kernel)

theorem reduce198 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph198 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph198 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph198 graph112 perm47 (1)
    intro x
    change chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 0 - x 2) * (chi (x 0 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce199 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph199 = 0 := by
  exact moment_odd F hm1 graph199 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
