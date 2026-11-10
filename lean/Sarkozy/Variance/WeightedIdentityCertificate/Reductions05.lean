module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions04

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce100 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph100 = 0 := by
  exact moment_odd F hm1 graph100 (by decide +kernel)

theorem reduce101 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph101 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph101 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph101 graph64 perm19 (-1)
    intro x
    change chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce102 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph102 = 0 := by
  have h : moment F graph102 = (-1 : ℝ) * moment F graph102 := by
    apply moment_relabel F graph102 graph102 perm20 (-1)
    intro x
    change chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 4 - x 3) * (chi (x 4 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce103 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph103 = 0 := by
  exact moment_odd F hm1 graph103 (by decide +kernel)

theorem reduce104 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph104 = 0 := by
  have h : moment F graph104 = (1 : ℝ) * moment F ([(0, 2), (1, 2), (1, 3), (1, 5), (2, 3), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph104 [(0, 2), (1, 2), (1, 3), (1, 5), (2, 3), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 3), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce105 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph105 = 0 := by
  exact moment_odd F hm1 graph105 (by decide +kernel)

theorem reduce106 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph106 = 0 := by
  exact moment_odd F hm1 graph106 (by decide +kernel)

theorem reduce107 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph107 = (-1 : ℝ) * g10 F := by
  have h : moment F graph107 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph107 graph90 perm21 (-1)
    intro x
    change chi (x 1 - x 2) * (chi (x 5 - x 2) * (chi (x 3 - x 2) * (chi (x 5 - x 1) * (chi (x 0 - x 1) * (chi (x 4 - x 1) * (chi (x 0 - x 5) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce108 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph108 = 0 := by
  exact moment_odd F hm1 graph108 (by decide +kernel)

theorem reduce109 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph109 = 0 := by
  have h : moment F graph109 = (1 : ℝ) * moment F ([(4, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph109 [(4, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 4 5 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce110 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph110 = (1 : ℝ) * (q F) ^ 1 + (-3 : ℝ) * (q F) ^ 2 + (2 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph110 = (1 : ℝ) * moment F graph7 := by
    apply moment_relabel F graph110 graph7 perm22 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))))
    ring
  rw [h, reduce7 F hF hm1]
  ring

theorem reduce111 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph111 = 0 := by
  have h : moment F graph111 = (1 : ℝ) * moment F ([(0, 0), (0, 1), (0, 4), (0, 5), (1, 4), (1, 5)] : Graph) := by
    apply moment_pointwise F graph111 [(0, 0), (0, 1), (0, 4), (0, 5), (1, 4), (1, 5)] (1)
    intro x
    change chi (x 0 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 0 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))
    ring
  rw [h, moment_loop F 0 [(0, 1), (0, 4), (0, 5), (1, 4), (1, 5)], mul_zero]

theorem reduce112 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph112 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph112 = (1 : ℝ) * moment F ([(3, 0), (3, 2)] ++ graph110) := by
    apply moment_pointwise F graph112 ([(3, 0), (3, 2)] ++ graph110) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  have hc : moment F (identify 0 2 graph110) =
      (-1 : ℝ) * moment F graph111 := by
    apply moment_pointwise F (identify 0 2 graph110) graph111 (-1)
    intro x
    change chi (x 0 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 0 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))) = (-1 : ℝ) * (chi (x 0 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))
    rw [chi_sub_comm hm1 (x 0) (x 1)]
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 3 0 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph110 (by decide +kernel), hc]
  rw [reduce110 F hF hm1]
  rw [reduce111 F hF hm1]
  unfold q
  ring

theorem reduce113 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph113 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph113 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph113 graph112 perm23 (1)
    intro x
    change chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 0 - x 2) * (chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 5 - x 1) * (chi (x 0 - x 5) * (chi (x 0 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce114 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph114 = 0 := by
  exact moment_odd F hm1 graph114 (by decide +kernel)

theorem reduce115 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph115 = 0 := by
  have h : moment F graph115 = (1 : ℝ) * moment F ([(4, 5), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph115 [(4, 5), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 4) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 4 5 (by decide +kernel)
    [(0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce116 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph116 = 0 := by
  exact moment_odd F hm1 graph116 (by decide +kernel)

theorem reduce117 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph117 = 0 := by
  exact moment_odd F hm1 graph117 (by decide +kernel)

theorem reduce118 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph118 = (-1 : ℝ) * g5 F := by
  have h : moment F graph118 = (-1 : ℝ) * moment F graph13 := by
    apply moment_relabel F graph118 graph13 perm24 (-1)
    intro x
    change chi (x 3 - x 1) * (chi (x 0 - x 1) * (chi (x 4 - x 1) * (chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, reduce13 F hF hm1]
  ring

theorem reduce119 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph119 = 0 := by
  have h : moment F graph119 = (1 : ℝ) * moment F ([(0, 0), (0, 2), (0, 2), (0, 3), (0, 4), (2, 3), (2, 4), (3, 4)] : Graph) := by
    apply moment_pointwise F graph119 [(0, 0), (0, 2), (0, 2), (0, 3), (0, 4), (2, 3), (2, 4), (3, 4)] (1)
    intro x
    change chi (x 0 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 0 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    ring
  rw [h, moment_loop F 0 [(0, 2), (0, 2), (0, 3), (0, 4), (2, 3), (2, 4), (3, 4)], mul_zero]

end Sarkozy.Variance.WeightedIdentityCertificate
