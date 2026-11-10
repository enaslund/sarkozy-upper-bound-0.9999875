module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions00

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce20 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph20 = 0 := by
  have h : moment F graph20 = (1 : ℝ) * moment F ([(0, 5), (1, 5)] : Graph) := by
    apply moment_pointwise F graph20 [(0, 5), (1, 5)] (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)))
    ring
  rw [h, moment_leaf F hF hm1 0 5 (by decide +kernel)
    [(1, 5)] (by decide +kernel), mul_zero]

theorem reduce21 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph21 = 0 := by
  have h : moment F graph21 = (1 : ℝ) * moment F ([(1, 3), (1, 3)] ++ graph20) := by
    apply moment_pointwise F graph21 ([(1, 3), (1, 3)] ++ graph20) (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (1)))) = (1 : ℝ) * (chi (x 3 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)))))
    ring
  have hc : moment F (identify 1 3 graph20) =
      (1 : ℝ) * moment F graph20 := by
    apply moment_pointwise F (identify 1 3 graph20) graph20 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 1 3 (by decide +kernel) graph20, hc]
  rw [reduce20 F hF hm1]
  ring

theorem reduce22 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph22 = (1 : ℝ) + (-1 : ℝ) * (q F) ^ 1 := by
  have h : moment F graph22 = (1 : ℝ) * moment F ([(0, 5), (0, 5)] ++ graph1) := by
    apply moment_pointwise F graph22 ([(0, 5), (0, 5)] ++ graph1) (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))
    ring
  have hc : moment F (identify 0 5 graph1) =
      (1 : ℝ) * moment F graph1 := by
    apply moment_pointwise F (identify 0 5 graph1) graph1 (1)
    intro x
    change 1 = (1 : ℝ) * (1)
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 5 (by decide +kernel) graph1, hc]
  rw [reduce1 F hF hm1]
  unfold q
  ring

theorem reduce23 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph23 = (-1 : ℝ) * (q F) ^ 1 + (1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph23 = (1 : ℝ) * moment F ([(0, 1), (0, 1)] ++ graph20) := by
    apply moment_pointwise F graph23 ([(0, 1), (0, 1)] ++ graph20) (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)))))
    ring
  have hc : moment F (identify 0 1 graph20) =
      (1 : ℝ) * moment F graph22 := by
    apply moment_pointwise F (identify 0 1 graph20) graph22 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 1 (by decide +kernel) graph20, hc]
  rw [reduce20 F hF hm1]
  rw [reduce22 F hF hm1]
  unfold q
  ring

theorem reduce24 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph24 = (1 : ℝ) * (q F) ^ 2 + (-1 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph24 = (1 : ℝ) * moment F ([(0, 3), (0, 3)] ++ graph21) := by
    apply moment_pointwise F graph24 ([(0, 3), (0, 3)] ++ graph21) (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (1)))))))
    ring
  have hc : moment F (identify 0 3 graph21) =
      (1 : ℝ) * moment F graph23 := by
    apply moment_pointwise F (identify 0 3 graph21) graph23 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 0 - x 1) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (1)))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (1)))))
    rw [chi_sub_comm hm1 (x 0) (x 1)]
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 3 (by decide +kernel) graph21, hc]
  rw [reduce21 F hF hm1]
  rw [reduce23 F hF hm1]
  unfold q
  ring

theorem reduce25 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph25 = (-1 : ℝ) * (q F) ^ 2 + (4 : ℝ) * (q F) ^ 3 + (-3 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph25 = (1 : ℝ) * moment F ([(2, 3), (2, 4)] ++ graph19) := by
    apply moment_pointwise F graph25 ([(2, 3), (2, 4)] ++ graph19) (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))))
    ring
  have hc : moment F (identify 3 4 graph19) =
      (1 : ℝ) * moment F graph24 := by
    apply moment_pointwise F (identify 3 4 graph19) graph24 (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (1)))))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 2 3 4 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph19 (by decide +kernel), hc]
  rw [reduce19 F hF hm1]
  rw [reduce24 F hF hm1]
  unfold q
  ring

theorem reduce26 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph26 = (1 : ℝ) * (q F) ^ 2 + (-4 : ℝ) * (q F) ^ 3 + (3 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph26 = (-1 : ℝ) * moment F graph25 := by
    apply moment_relabel F graph26 graph25 perm4 (-1)
    intro x
    change chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 1 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 1) * (1)))))))) = (-1 : ℝ) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3)]
    ring
  rw [h, reduce25 F hF hm1]
  ring

theorem reduce27 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph27 = 0 := by
  exact moment_odd F hm1 graph27 (by decide +kernel)

theorem reduce28 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph28 = 0 := by
  have h : moment F graph28 = (-1 : ℝ) * moment F ([(4, 3), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph28 [(4, 3), (0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 3 - x 4) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, moment_leaf F hF hm1 4 3 (by decide +kernel)
    [(0, 2), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce29 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph29 = 0 := by
  exact moment_odd F hm1 graph29 (by decide +kernel)

theorem reduce30 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph30 = 0 := by
  exact moment_odd F hm1 graph30 (by decide +kernel)

theorem reduce31 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph31 = (1 : ℝ) * g5 F := by
  have h : moment F graph31 = (1 : ℝ) * moment F graph13 := by
    apply moment_relabel F graph31 graph13 perm5 (1)
    intro x
    change chi (x 0 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 0 - x 2) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 2)]
    ring
  rw [h, reduce13 F hF hm1]
  ring

theorem reduce32 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph32 = 0 := by
  have h : moment F graph32 = (-1 : ℝ) * moment F ([(3, 2), (2, 4)] : Graph) := by
    apply moment_pointwise F graph32 [(3, 2), (2, 4)] (-1)
    intro x
    change chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)) = (-1 : ℝ) * (chi (x 2 - x 3) * (chi (x 4 - x 2) * (1)))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 2 (by decide +kernel)
    [(2, 4)] (by decide +kernel), mul_zero]

theorem reduce33 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph33 = 0 := by
  have h : moment F graph33 = (1 : ℝ) * moment F ([(0, 2), (2, 3)] : Graph) := by
    apply moment_pointwise F graph33 [(0, 2), (2, 3)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 2) * (1)) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 2) * (1)))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(2, 3)] (by decide +kernel), mul_zero]

theorem reduce34 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph34 = 0 := by
  have h : moment F graph34 = (1 : ℝ) * moment F ([(0, 4), (0, 4)] ++ graph32) := by
    apply moment_pointwise F graph34 ([(0, 4), (0, 4)] ++ graph32) (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))
    ring
  have hc : moment F (identify 0 4 graph32) =
      (-1 : ℝ) * moment F graph33 := by
    apply moment_pointwise F (identify 0 4 graph32) graph33 (-1)
    intro x
    change chi (x 3 - x 2) * (chi (x 0 - x 2) * (1)) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 2) * (1)))
    rw [chi_sub_comm hm1 (x 0) (x 2)]
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 4 (by decide +kernel) graph32, hc]
  rw [reduce32 F hF hm1]
  rw [reduce33 F hF hm1]
  ring

theorem reduce35 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph35 = 0 := by
  have h : moment F graph35 = (1 : ℝ) * moment F ([(0, 2), (2, 4)] : Graph) := by
    apply moment_pointwise F graph35 [(0, 2), (2, 4)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 2) * (1)) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 2) * (1)))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(2, 4)] (by decide +kernel), mul_zero]

theorem reduce36 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph36 = (1 : ℝ) + (-1 : ℝ) * (q F) ^ 1 := by
  have h : moment F graph36 = (1 : ℝ) * moment F ([(0, 2), (0, 2)] ++ graph1) := by
    apply moment_pointwise F graph36 ([(0, 2), (0, 2)] ++ graph1) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 0) * (1)) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 0) * (1)))
    ring
  have hc : moment F (identify 0 2 graph1) =
      (1 : ℝ) * moment F graph1 := by
    apply moment_pointwise F (identify 0 2 graph1) graph1 (1)
    intro x
    change 1 = (1 : ℝ) * (1)
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 2 (by decide +kernel) graph1, hc]
  rw [reduce1 F hF hm1]
  unfold q
  ring

theorem reduce37 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph37 = (1 : ℝ) * (q F) ^ 1 + (-1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph37 = (1 : ℝ) * moment F ([(0, 4), (0, 4)] ++ graph35) := by
    apply moment_pointwise F graph37 ([(0, 4), (0, 4)] ++ graph35) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 2) * (1)))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 2) * (1)))))
    ring
  have hc : moment F (identify 0 4 graph35) =
      (-1 : ℝ) * moment F graph36 := by
    apply moment_pointwise F (identify 0 4 graph35) graph36 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 0 - x 2) * (1)) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 0) * (1)))
    rw [chi_sub_comm hm1 (x 0) (x 2)]
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 4 (by decide +kernel) graph35, hc]
  rw [reduce35 F hF hm1]
  rw [reduce36 F hF hm1]
  unfold q
  ring

theorem reduce38 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph38 = (1 : ℝ) * (q F) ^ 2 + (-1 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph38 = (1 : ℝ) * moment F ([(0, 3), (0, 3)] ++ graph34) := by
    apply moment_pointwise F graph38 ([(0, 3), (0, 3)] ++ graph34) (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))
    ring
  have hc : moment F (identify 0 3 graph34) =
      (-1 : ℝ) * moment F graph37 := by
    apply moment_pointwise F (identify 0 3 graph34) graph37 (-1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (1)))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 2) * (1)))))
    rw [chi_sub_comm hm1 (x 0) (x 2)]
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 3 (by decide +kernel) graph34, hc]
  rw [reduce34 F hF hm1]
  rw [reduce37 F hF hm1]
  unfold q
  ring

theorem reduce39 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph39 = 0 := by
  have h : moment F graph39 = (-1 : ℝ) * moment F ([(3, 0), (0, 4)] : Graph) := by
    apply moment_pointwise F graph39 [(3, 0), (0, 4)] (-1)
    intro x
    change chi (x 3 - x 0) * (chi (x 4 - x 0) * (1)) = (-1 : ℝ) * (chi (x 0 - x 3) * (chi (x 4 - x 0) * (1)))
    rw [chi_sub_comm hm1 (x 0) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 0 (by decide +kernel)
    [(0, 4)] (by decide +kernel), mul_zero]

end Sarkozy.Variance.WeightedIdentityCertificate
