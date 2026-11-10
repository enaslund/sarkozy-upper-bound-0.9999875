module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions01

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce40 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph40 = 0 := by
  have h : moment F graph40 = (1 : ℝ) * moment F ([(0, 0), (0, 3)] : Graph) := by
    apply moment_pointwise F graph40 [(0, 0), (0, 3)] (1)
    intro x
    change chi (x 0 - x 0) * (chi (x 3 - x 0) * (1)) = (1 : ℝ) * (chi (x 0 - x 0) * (chi (x 3 - x 0) * (1)))
    ring
  rw [h, moment_loop F 0 [(0, 3)], mul_zero]

theorem reduce41 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph41 = 0 := by
  have h : moment F graph41 = (1 : ℝ) * moment F ([(0, 4), (0, 4)] ++ graph39) := by
    apply moment_pointwise F graph41 ([(0, 4), (0, 4)] ++ graph39) (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (1)))))
    ring
  have hc : moment F (identify 0 4 graph39) =
      (1 : ℝ) * moment F graph40 := by
    apply moment_pointwise F (identify 0 4 graph39) graph40 (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 0 - x 0) * (1)) = (1 : ℝ) * (chi (x 0 - x 0) * (chi (x 3 - x 0) * (1)))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 4 (by decide +kernel) graph39, hc]
  rw [reduce39 F hF hm1]
  rw [reduce40 F hF hm1]
  ring

theorem reduce42 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph42 = 0 := by
  have h : moment F graph42 = (1 : ℝ) * moment F ([(0, 0), (0, 4), (0, 4), (0, 4)] : Graph) := by
    apply moment_pointwise F graph42 [(0, 0), (0, 4), (0, 4), (0, 4)] (1)
    intro x
    change chi (x 0 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))) = (1 : ℝ) * (chi (x 0 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))))
    ring
  rw [h, moment_loop F 0 [(0, 4), (0, 4), (0, 4)], mul_zero]

theorem reduce43 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph43 = 0 := by
  have h : moment F graph43 = (1 : ℝ) * moment F ([(0, 3), (0, 3)] ++ graph41) := by
    apply moment_pointwise F graph43 ([(0, 3), (0, 3)] ++ graph41) (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))))))
    ring
  have hc : moment F (identify 0 3 graph41) =
      (1 : ℝ) * moment F graph42 := by
    apply moment_pointwise F (identify 0 3 graph41) graph42 (1)
    intro x
    change chi (x 0 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))) = (1 : ℝ) * (chi (x 0 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 3 (by decide +kernel) graph41, hc]
  rw [reduce41 F hF hm1]
  rw [reduce42 F hF hm1]
  ring

theorem reduce44 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph44 = (1 : ℝ) * (q F) ^ 2 + (-1 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph44 = (1 : ℝ) * moment F ([(0, 2), (0, 2)] ++ graph38) := by
    apply moment_pointwise F graph44 ([(0, 2), (0, 2)] ++ graph38) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    ring
  have hc : moment F (identify 0 2 graph38) =
      (1 : ℝ) * moment F graph43 := by
    apply moment_pointwise F (identify 0 2 graph38) graph43 (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (1)))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 2 (by decide +kernel) graph38, hc]
  rw [reduce38 F hF hm1]
  rw [reduce43 F hF hm1]
  unfold q
  ring

theorem reduce45 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph45 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph45 = (1 : ℝ) * moment F ([(5, 0), (5, 1)] ++ graph31) := by
    apply moment_pointwise F graph45 ([(5, 0), (5, 1)] ++ graph31) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))) = (1 : ℝ) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  have hc : moment F (identify 0 1 graph31) =
      (1 : ℝ) * moment F graph44 := by
    apply moment_pointwise F (identify 0 1 graph31) graph44 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 5 0 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph31 (by decide +kernel), hc]
  rw [reduce31 F hF hm1]
  rw [reduce44 F hF hm1]
  unfold q
  ring

theorem reduce46 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph46 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph46 = (1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph46 graph45 perm4 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 2) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 1 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 1) * (1)))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

theorem reduce47 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph47 = 0 := by
  have h : moment F graph47 = (1 : ℝ) * moment F ([(1, 2), (0, 2), (0, 5), (2, 3), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph47 [(1, 2), (0, 2), (0, 5), (2, 3), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 1 2 (by decide +kernel)
    [(0, 2), (0, 5), (2, 3), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce48 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph48 = 0 := by
  exact moment_odd F hm1 graph48 (by decide +kernel)

theorem reduce49 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph49 = 0 := by
  exact moment_odd F hm1 graph49 (by decide +kernel)

theorem reduce50 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph50 = 0 := by
  have h : moment F graph50 = (-1 : ℝ) * moment F graph50 := by
    apply moment_relabel F graph50 graph50 perm6 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 2 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  linarith

theorem reduce51 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph51 = (1 : ℝ) * (q F) ^ 1 + (-1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph51 = (1 : ℝ) * moment F graph3 := by
    apply moment_relabel F graph51 graph3 perm7 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (1)))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (1)))))
    ring
  rw [h, reduce3 F hF hm1]
  ring

theorem reduce52 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph52 = (1 : ℝ) + (-2 : ℝ) * (q F) ^ 1 + (1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph52 = (1 : ℝ) * moment F ([(0, 4), (0, 4)] ++ graph22) := by
    apply moment_pointwise F graph52 ([(0, 4), (0, 4)] ++ graph22) (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))))
    ring
  have hc : moment F (identify 0 4 graph22) =
      (1 : ℝ) * moment F graph22 := by
    apply moment_pointwise F (identify 0 4 graph22) graph22 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 4 (by decide +kernel) graph22, hc]
  rw [reduce22 F hF hm1]
  unfold q
  ring

theorem reduce53 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph53 = (1 : ℝ) * (q F) ^ 2 + (-1 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph53 = (1 : ℝ) * moment F ([(0, 1), (0, 1)] ++ graph51) := by
    apply moment_pointwise F graph53 ([(0, 1), (0, 1)] ++ graph51) (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))
    ring
  have hc : moment F (identify 0 1 graph51) =
      (1 : ℝ) * moment F graph52 := by
    apply moment_pointwise F (identify 0 1 graph51) graph52 (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (1)))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 1 (by decide +kernel) graph51, hc]
  rw [reduce51 F hF hm1]
  rw [reduce52 F hF hm1]
  unfold q
  ring

theorem reduce54 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph54 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph54 = (1 : ℝ) * moment F ([(3, 1), (3, 2)] ++ graph50) := by
    apply moment_pointwise F graph54 ([(3, 1), (3, 2)] ++ graph50) (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  have hc : moment F (identify 1 2 graph50) =
      (1 : ℝ) * moment F graph53 := by
    apply moment_pointwise F (identify 1 2 graph50) graph53 (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 4 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 3 1 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph50 (by decide +kernel), hc]
  rw [reduce50 F hF hm1]
  rw [reduce53 F hF hm1]
  unfold q
  ring

theorem reduce55 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph55 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph55 = (-1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph55 graph54 perm8 (-1)
    intro x
    change chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 2 - x 4) * (chi (x 3 - x 2) * (chi (x 1 - x 3) * (chi (x 1 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce56 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph56 = 0 := by
  exact moment_odd F hm1 graph56 (by decide +kernel)

theorem reduce57 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph57 = 0 := by
  have h : moment F graph57 = (1 : ℝ) * moment F ([(4, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (2, 3), (3, 5)] : Graph) := by
    apply moment_pointwise F graph57 [(4, 5), (0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (2, 3), (3, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 4 5 (by decide +kernel)
    [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (2, 3), (3, 5)] (by decide +kernel), mul_zero]

theorem reduce58 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph58 = 0 := by
  have h : moment F graph58 = (-1 : ℝ) * moment F ([(3, 0), (0, 1), (0, 4), (1, 4)] : Graph) := by
    apply moment_pointwise F graph58 [(3, 0), (0, 1), (0, 4), (1, 4)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))) = (-1 : ℝ) * (chi (x 0 - x 3) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))))
    rw [chi_sub_comm hm1 (x 0) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 0 (by decide +kernel)
    [(0, 1), (0, 4), (1, 4)] (by decide +kernel), mul_zero]

theorem reduce59 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph59 = 0 := by
  have h : moment F graph59 = (1 : ℝ) * moment F ([(0, 4), (1, 4)] : Graph) := by
    apply moment_pointwise F graph59 [(0, 4), (1, 4)] (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))
    ring
  rw [h, moment_leaf F hF hm1 0 4 (by decide +kernel)
    [(1, 4)] (by decide +kernel), mul_zero]

end Sarkozy.Variance.WeightedIdentityCertificate
