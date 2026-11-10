module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions03

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce80 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph80 = 0 := by
  have h : moment F graph80 = (1 : ℝ) * moment F ([(4, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3)] : Graph) := by
    apply moment_pointwise F graph80 [(4, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 4 5 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3)] (by decide +kernel), mul_zero]

theorem reduce81 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph81 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph81 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph81 graph64 perm13 (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 1 - x 2) * (chi (x 4 - x 3) * (chi (x 1 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce82 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph82 = 0 := by
  exact moment_odd F hm1 graph82 (by decide +kernel)

theorem reduce83 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph83 = 0 := by
  exact moment_odd F hm1 graph83 (by decide +kernel)

theorem reduce84 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph84 = 0 := by
  have h : moment F graph84 = (-1 : ℝ) * moment F graph84 := by
    apply moment_relabel F graph84 graph84 perm14 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 2 - x 1) * (chi (x 4 - x 5) * (chi (x 3 - x 4) * (chi (x 2 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce85 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph85 = 0 := by
  have h : moment F graph85 = (-1 : ℝ) * moment F graph85 := by
    apply moment_relabel F graph85 graph85 perm15 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 1 - x 2) * (chi (x 5 - x 1) * (chi (x 4 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce86 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph86 = 0 := by
  exact moment_odd F hm1 graph86 (by decide +kernel)

theorem reduce87 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph87 = 0 := by
  have h : moment F graph87 = (-1 : ℝ) * moment F graph87 := by
    apply moment_relabel F graph87 graph87 perm16 (-1)
    intro x
    change chi (x 3 - x 4) * (chi (x 5 - x 4) * (chi (x 3 - x 1) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 3) * (chi (x 0 - x 2) * (chi (x 5 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  linarith

theorem reduce88 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph88 = 0 := by
  exact moment_odd F hm1 graph88 (by decide +kernel)

theorem reduce89 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph89 = 0 := by
  exact moment_odd F hm1 graph89 (by decide +kernel)

theorem reduce90 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph90 = (1 : ℝ) * g10 F := by
  simp only [g10, graph90, one_mul]

theorem reduce91 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph91 = (-1 : ℝ) * g10 F := by
  have h : moment F graph91 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph91 graph90 perm3 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 2 - x 5) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce92 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph92 = 0 := by
  have h : moment F graph92 = (1 : ℝ) * moment F ([(0, 2), (1, 2), (1, 5), (2, 3), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph92 [(0, 2), (1, 2), (1, 5), (2, 3), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 2), (1, 5), (2, 3), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce93 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph93 = 0 := by
  exact moment_odd F hm1 graph93 (by decide +kernel)

theorem reduce94 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph94 = 0 := by
  exact moment_odd F hm1 graph94 (by decide +kernel)

theorem reduce95 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph95 = 0 := by
  have h : moment F graph95 = (-1 : ℝ) * moment F graph95 := by
    apply moment_relabel F graph95 graph95 perm17 (-1)
    intro x
    change chi (x 1 - x 2) * (chi (x 0 - x 2) * (chi (x 3 - x 2) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 5 - x 4) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2)]
    ring
  linarith

theorem reduce96 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph96 = 0 := by
  exact moment_odd F hm1 graph96 (by decide +kernel)

theorem reduce97 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph97 = 0 := by
  have h : moment F graph97 = (1 : ℝ) * moment F ([(4, 5), (0, 1), (0, 2), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph97 [(4, 5), (0, 1), (0, 2), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 4 5 (by decide +kernel)
    [(0, 1), (0, 2), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce98 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph98 = 0 := by
  have h : moment F graph98 = (-1 : ℝ) * moment F graph98 := by
    apply moment_relabel F graph98 graph98 perm18 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 5 - x 3) * (chi (x 1 - x 2) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  linarith

theorem reduce99 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph99 = 0 := by
  exact moment_odd F hm1 graph99 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
