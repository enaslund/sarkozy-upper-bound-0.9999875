module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions06

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce140 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph140 = 0 := by
  have h : moment F graph140 = (1 : ℝ) * moment F ([(1, 5), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5)] : Graph) := by
    apply moment_pointwise F graph140 [(1, 5), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 5 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce141 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph141 = 0 := by
  exact moment_odd F hm1 graph141 (by decide +kernel)

theorem reduce142 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph142 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph142 = (-1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph142 graph54 perm32 (-1)
    intro x
    change chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 0 - x 4) * (chi (x 2 - x 4) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 0) * (chi (x 2 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce143 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph143 = 0 := by
  exact moment_odd F hm1 graph143 (by decide +kernel)

theorem reduce144 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph144 = 0 := by
  exact moment_odd F hm1 graph144 (by decide +kernel)

theorem reduce145 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph145 = 0 := by
  have h : moment F graph145 = (-1 : ℝ) * moment F graph145 := by
    apply moment_relabel F graph145 graph145 perm6 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 4) * (chi (x 2 - x 4) * (chi (x 2 - x 3) * (chi (x 5 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  linarith

theorem reduce146 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph146 = (1 : ℝ) * (q F) ^ 1 + (-3 : ℝ) * (q F) ^ 2 + (2 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph146 = (1 : ℝ) * moment F graph7 := by
    apply moment_relabel F graph146 graph7 perm33 (1)
    intro x
    change chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 1 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 4)]
    ring
  rw [h, reduce7 F hF hm1]
  ring

theorem reduce147 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph147 = 0 := by
  exact moment_odd F hm1 graph147 (by decide +kernel)

theorem reduce148 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph148 = 0 := by
  exact moment_odd F hm1 graph148 (by decide +kernel)

theorem reduce149 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph149 = 0 := by
  have h : moment F graph149 = (-1 : ℝ) * moment F ([(1, 0), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph149 [(1, 0), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 0 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1)]
    ring
  rw [h, moment_leaf F hF hm1 1 0 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce150 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph150 = 0 := by
  exact moment_odd F hm1 graph150 (by decide +kernel)

theorem reduce151 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph151 = (1 : ℝ) * (q F) ^ 2 + (-4 : ℝ) * (q F) ^ 3 + (3 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph151 = (-1 : ℝ) * moment F graph25 := by
    apply moment_relabel F graph151 graph25 perm34 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 5) * (chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 4 - x 1) * (chi (x 4 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce25 F hF hm1]
  ring

theorem reduce152 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph152 = 0 := by
  have h : moment F graph152 = (1 : ℝ) * moment F ([(1, 3), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph152 [(1, 3), (0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 3 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 3 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce153 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph153 = 0 := by
  exact moment_odd F hm1 graph153 (by decide +kernel)

theorem reduce154 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph154 = 0 := by
  exact moment_odd F hm1 graph154 (by decide +kernel)

theorem reduce155 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph155 = 0 := by
  have h : moment F graph155 = (-1 : ℝ) * moment F ([(1, 0), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph155 [(1, 0), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 0 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1)]
    ring
  rw [h, moment_leaf F hF hm1 1 0 (by decide +kernel)
    [(0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce156 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph156 = (1 : ℝ) * g5 F := by
  have h : moment F graph156 = (1 : ℝ) * moment F graph13 := by
    apply moment_relabel F graph156 graph13 perm35 (1)
    intro x
    change chi (x 3 - x 1) * (chi (x 0 - x 1) * (chi (x 4 - x 1) * (chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, reduce13 F hF hm1]
  ring

theorem reduce157 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph157 = 0 := by
  exact moment_odd F hm1 graph157 (by decide +kernel)

theorem reduce158 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph158 = 0 := by
  have h : moment F graph158 = (1 : ℝ) * moment F ([(1, 3), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph158 [(1, 3), (0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 3 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 3 (by decide +kernel)
    [(0, 2), (0, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce159 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph159 = 0 := by
  exact moment_odd F hm1 graph159 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
