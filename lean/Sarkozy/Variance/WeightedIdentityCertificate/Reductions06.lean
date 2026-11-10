module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions05

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce120 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph120 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph120 = (1 : ℝ) * moment F ([(5, 0), (5, 1)] ++ graph118) := by
    apply moment_pointwise F graph120 ([(5, 0), (5, 1)] ++ graph118) (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  have hc : moment F (identify 0 1 graph118) =
      (1 : ℝ) * moment F graph119 := by
    apply moment_pointwise F (identify 0 1 graph118) graph119 (1)
    intro x
    change chi (x 0 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 0 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 5 0 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph118 (by decide +kernel), hc]
  rw [reduce118 F hF hm1]
  rw [reduce119 F hF hm1]
  unfold q
  ring

theorem reduce121 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph121 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph121 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph121 graph120 perm25 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 4) * (chi (x 1 - x 3) * (chi (x 1 - x 5) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce122 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph122 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph122 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph122 graph112 perm26 (1)
    intro x
    change chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 1 - x 5) * (chi (x 0 - x 5) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 0 - x 2) * (chi (x 0 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce123 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph123 = 0 := by
  exact moment_odd F hm1 graph123 (by decide +kernel)

theorem reduce124 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph124 = 0 := by
  exact moment_odd F hm1 graph124 (by decide +kernel)

theorem reduce125 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph125 = (-1 : ℝ) * g10 F := by
  have h : moment F graph125 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph125 graph90 perm10 (-1)
    intro x
    change chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 3 - x 4) * (chi (x 1 - x 4) * (chi (x 2 - x 3) * (chi (x 5 - x 2) * (chi (x 1 - x 2) * (chi (x 1 - x 5) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce126 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph126 = 0 := by
  exact moment_odd F hm1 graph126 (by decide +kernel)

theorem reduce127 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph127 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph127 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph127 graph120 perm27 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 1 - x 3) * (chi (x 4 - x 2) * (chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 4) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce128 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph128 = (1 : ℝ) * g10 F := by
  have h : moment F graph128 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph128 graph90 perm28 (1)
    intro x
    change chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 4) * (chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 0 - x 3) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce129 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph129 = 0 := by
  exact moment_odd F hm1 graph129 (by decide +kernel)

theorem reduce130 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph130 = 0 := by
  have h : moment F graph130 = (1 : ℝ) * moment F ([(1, 5), (0, 2), (0, 5), (2, 3), (2, 4), (3, 5)] : Graph) := by
    apply moment_pointwise F graph130 [(1, 5), (0, 2), (0, 5), (2, 3), (2, 4), (3, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 1 5 (by decide +kernel)
    [(0, 2), (0, 5), (2, 3), (2, 4), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce131 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph131 = 0 := by
  exact moment_odd F hm1 graph131 (by decide +kernel)

theorem reduce132 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph132 = 0 := by
  exact moment_odd F hm1 graph132 (by decide +kernel)

theorem reduce133 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph133 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph133 = (1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph133 graph54 perm29 (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 4) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce134 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph134 = 0 := by
  exact moment_odd F hm1 graph134 (by decide +kernel)

theorem reduce135 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph135 = 0 := by
  have h : moment F graph135 = (-1 : ℝ) * moment F ([(4, 2), (0, 1), (0, 2), (0, 5), (1, 3), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph135 [(4, 2), (0, 1), (0, 2), (0, 5), (1, 3), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 2 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 3), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce136 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph136 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph136 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph136 graph64 perm30 (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce137 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph137 = 0 := by
  exact moment_odd F hm1 graph137 (by decide +kernel)

theorem reduce138 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph138 = 0 := by
  exact moment_odd F hm1 graph138 (by decide +kernel)

theorem reduce139 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph139 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph139 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph139 graph64 perm31 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 4 - x 2) * (chi (x 1 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
