module

public import Sarkozy.Variance.WeightedIdentityCertificate.Data

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce0 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph0 = 0 := by
  have h : moment F graph0 = (-1 : ℝ) * moment F ([(2, 1), (1, 3)] : Graph) := by
    apply moment_pointwise F graph0 [(2, 1), (1, 3)] (-1)
    intro x
    change chi (x 2 - x 1) * (chi (x 3 - x 1) * (1)) = (-1 : ℝ) * (chi (x 1 - x 2) * (chi (x 3 - x 1) * (1)))
    rw [chi_sub_comm hm1 (x 1) (x 2)]
    ring
  rw [h, moment_leaf F hF hm1 2 1 (by decide +kernel)
    [(1, 3)] (by decide +kernel), mul_zero]

theorem reduce1 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph1 = (1 : ℝ) := by
  exact moment_nil F

theorem reduce2 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph2 = (1 : ℝ) + (-1 : ℝ) * (q F) ^ 1 := by
  have h : moment F graph2 = (1 : ℝ) * moment F ([(1, 2), (1, 2)] ++ graph1) := by
    apply moment_pointwise F graph2 ([(1, 2), (1, 2)] ++ graph1) (1)
    intro x
    change chi (x 2 - x 1) * (chi (x 2 - x 1) * (1)) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 1) * (1)))
    ring
  have hc : moment F (identify 1 2 graph1) =
      (1 : ℝ) * moment F graph1 := by
    apply moment_pointwise F (identify 1 2 graph1) graph1 (1)
    intro x
    change 1 = (1 : ℝ) * (1)
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 1 2 (by decide +kernel) graph1, hc]
  rw [reduce1 F hF hm1]
  unfold q
  ring

theorem reduce3 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph3 = (1 : ℝ) * (q F) ^ 1 + (-1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph3 = (1 : ℝ) * moment F ([(0, 2), (0, 3)] ++ graph0) := by
    apply moment_pointwise F graph3 ([(0, 2), (0, 3)] ++ graph0) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (1)))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (1)))))
    ring
  have hc : moment F (identify 2 3 graph0) =
      (1 : ℝ) * moment F graph2 := by
    apply moment_pointwise F (identify 2 3 graph0) graph2 (1)
    intro x
    change chi (x 2 - x 1) * (chi (x 2 - x 1) * (1)) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 1) * (1)))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 0 2 3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph0 (by decide +kernel), hc]
  rw [reduce0 F hF hm1]
  rw [reduce2 F hF hm1]
  unfold q
  ring

theorem reduce4 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph4 = (1 : ℝ) * (q F) ^ 1 + (-1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph4 = (1 : ℝ) * moment F graph3 := by
    apply moment_relabel F graph4 graph3 perm0 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (1)))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (1)))))
    ring
  rw [h, reduce3 F hF hm1]
  ring

theorem reduce5 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph5 = (1 : ℝ) + (-1 : ℝ) * (q F) ^ 1 := by
  have h : moment F graph5 = (1 : ℝ) * moment F ([(0, 4), (0, 4)] ++ graph1) := by
    apply moment_pointwise F graph5 ([(0, 4), (0, 4)] ++ graph1) (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))
    ring
  have hc : moment F (identify 0 4 graph1) =
      (1 : ℝ) * moment F graph1 := by
    apply moment_pointwise F (identify 0 4 graph1) graph1 (1)
    intro x
    change 1 = (1 : ℝ) * (1)
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 4 (by decide +kernel) graph1, hc]
  rw [reduce1 F hF hm1]
  unfold q
  ring

theorem reduce6 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph6 = (1 : ℝ) + (-2 : ℝ) * (q F) ^ 1 + (1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph6 = (1 : ℝ) * moment F ([(0, 3), (0, 3)] ++ graph5) := by
    apply moment_pointwise F graph6 ([(0, 3), (0, 3)] ++ graph5) (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))))
    ring
  have hc : moment F (identify 0 3 graph5) =
      (1 : ℝ) * moment F graph5 := by
    apply moment_pointwise F (identify 0 3 graph5) graph5 (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 3 (by decide +kernel) graph5, hc]
  rw [reduce5 F hF hm1]
  unfold q
  ring

theorem reduce7 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph7 = (1 : ℝ) * (q F) ^ 1 + (-3 : ℝ) * (q F) ^ 2 + (2 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph7 = (1 : ℝ) * moment F ([(2, 0), (2, 1)] ++ graph4) := by
    apply moment_pointwise F graph7 ([(2, 0), (2, 1)] ++ graph4) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2)]
    ring
  have hc : moment F (identify 0 1 graph4) =
      (1 : ℝ) * moment F graph6 := by
    apply moment_pointwise F (identify 0 1 graph4) graph6 (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (1)))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 2 0 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph4 (by decide +kernel), hc]
  rw [reduce4 F hF hm1]
  rw [reduce6 F hF hm1]
  unfold q
  ring

theorem reduce8 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph8 = (-1 : ℝ) * (q F) ^ 1 + (3 : ℝ) * (q F) ^ 2 + (-2 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph8 = (-1 : ℝ) * moment F graph7 := by
    apply moment_relabel F graph8 graph7 perm1 (-1)
    intro x
    change chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 1 - x 3) * (chi (x 4 - x 0) * (chi (x 1 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 4)]
    ring
  rw [h, reduce7 F hF hm1]
  ring

theorem reduce9 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph9 = 0 := by
  exact moment_odd F hm1 graph9 (by decide +kernel)

theorem reduce10 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph10 = 0 := by
  exact moment_odd F hm1 graph10 (by decide +kernel)

theorem reduce11 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph11 = 0 := by
  have h : moment F graph11 = (-1 : ℝ) * moment F ([(4, 0), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph11 [(4, 0), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 0 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 0 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce12 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph12 = 0 := by
  exact moment_odd F hm1 graph12 (by decide +kernel)

theorem reduce13 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph13 = (1 : ℝ) * g5 F := by
  simp only [g5, graph13, one_mul]

theorem reduce14 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph14 = (1 : ℝ) * g5 F := by
  have h : moment F graph14 = (1 : ℝ) * moment F graph13 := by
    apply moment_relabel F graph14 graph13 perm2 (1)
    intro x
    change chi (x 0 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 3) * (chi (x 4 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, reduce13 F hF hm1]
  ring

theorem reduce15 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph15 = 0 := by
  have h : moment F graph15 = (-1 : ℝ) * moment F ([(4, 0), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph15 [(4, 0), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 0 - x 4) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 0 (by decide +kernel)
    [(0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce16 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph16 = 0 := by
  exact moment_odd F hm1 graph16 (by decide +kernel)

theorem reduce17 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph17 = 0 := by
  exact moment_odd F hm1 graph17 (by decide +kernel)

theorem reduce18 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph18 = 0 := by
  have h : moment F graph18 = (-1 : ℝ) * moment F ([(4, 3), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph18 [(4, 3), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 3 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 3 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce19 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph19 = (1 : ℝ) * (q F) ^ 1 + (-3 : ℝ) * (q F) ^ 2 + (2 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph19 = (1 : ℝ) * moment F graph7 := by
    apply moment_relabel F graph19 graph7 perm3 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (1)))))))
    ring
  rw [h, reduce7 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
