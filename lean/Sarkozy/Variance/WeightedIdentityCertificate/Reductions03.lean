module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions02

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce60 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph60 = (-1 : ℝ) * (q F) ^ 1 + (1 : ℝ) * (q F) ^ 2 := by
  have h : moment F graph60 = (1 : ℝ) * moment F ([(0, 1), (0, 1)] ++ graph59) := by
    apply moment_pointwise F graph60 ([(0, 1), (0, 1)] ++ graph59) (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))))
    ring
  have hc : moment F (identify 0 1 graph59) =
      (1 : ℝ) * moment F graph5 := by
    apply moment_pointwise F (identify 0 1 graph59) graph5 (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (1)))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 1 (by decide +kernel) graph59, hc]
  rw [reduce5 F hF hm1]
  rw [reduce59 F hF hm1]
  unfold q
  ring

theorem reduce61 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph61 = (1 : ℝ) * (q F) ^ 2 + (-1 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph61 = (-1 : ℝ) * moment F ([(2, 1), (2, 3)] ++ graph58) := by
    apply moment_pointwise F graph61 ([(2, 1), (2, 3)] ++ graph58) (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (1)))))) = (-1 : ℝ) * (chi (x 1 - x 2) * (chi (x 3 - x 2) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))))))
    rw [chi_sub_comm hm1 (x 1) (x 2)]
    ring
  have hc : moment F (identify 1 3 graph58) =
      (1 : ℝ) * moment F graph60 := by
    apply moment_pointwise F (identify 1 3 graph58) graph60 (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 1) * (1)))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 2 1 3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph58 (by decide +kernel), hc]
  rw [reduce58 F hF hm1]
  rw [reduce60 F hF hm1]
  unfold q
  ring

theorem reduce62 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph62 = (1 : ℝ) * (q F) ^ 2 + (-1 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph62 = (1 : ℝ) * moment F graph61 := by
    apply moment_relabel F graph62 graph61 perm9 (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (1)))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 3 - x 2) * (1)))))))
    ring
  rw [h, reduce61 F hF hm1]
  ring

theorem reduce63 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph63 = 0 := by
  have h : moment F graph63 = (1 : ℝ) * moment F ([(2, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5)] : Graph) := by
    apply moment_pointwise F graph63 [(2, 2), (0, 1), (0, 2), (0, 5), (1, 2), (1, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 2) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 2) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (1)))))))
    ring
  rw [h, moment_loop F 2 [(0, 1), (0, 2), (0, 5), (1, 2), (1, 5)], mul_zero]

theorem reduce64 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph64 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph64 = (1 : ℝ) * moment F ([(4, 2), (4, 3)] ++ graph62) := by
    apply moment_pointwise F graph64 ([(4, 2), (4, 3)] ++ graph62) (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  have hc : moment F (identify 2 3 graph62) =
      (1 : ℝ) * moment F graph63 := by
    apply moment_pointwise F (identify 2 3 graph62) graph63 (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 2) * (1)))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 2) * (1)))))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 4 2 3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph62 (by decide +kernel), hc]
  rw [reduce62 F hF hm1]
  rw [reduce63 F hF hm1]
  unfold q
  ring

theorem reduce65 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph65 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph65 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph65 graph64 perm10 (-1)
    intro x
    change chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 3 - x 4) * (chi (x 2 - x 4) * (chi (x 2 - x 3) * (chi (x 1 - x 2) * (chi (x 1 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce66 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph66 = 0 := by
  exact moment_odd F hm1 graph66 (by decide +kernel)

theorem reduce67 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph67 = 0 := by
  exact moment_odd F hm1 graph67 (by decide +kernel)

theorem reduce68 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph68 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph68 = (1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph68 graph64 perm11 (1)
    intro x
    change chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 5) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 3 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce69 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph69 = 0 := by
  have h : moment F graph69 = (1 : ℝ) * moment F ([(1, 2), (0, 2), (0, 4), (0, 5), (2, 3), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph69 [(1, 2), (0, 2), (0, 4), (0, 5), (2, 3), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 2 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 3), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce70 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph70 = 0 := by
  exact moment_odd F hm1 graph70 (by decide +kernel)

theorem reduce71 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph71 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph71 = (1 : ℝ) * moment F graph54 := by
    apply moment_relabel F graph71 graph54 perm12 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 2 - x 4) * (chi (x 0 - x 4) * (chi (x 0 - x 2) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce54 F hF hm1]
  ring

theorem reduce72 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph72 = 0 := by
  exact moment_odd F hm1 graph72 (by decide +kernel)

theorem reduce73 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph73 = 0 := by
  exact moment_odd F hm1 graph73 (by decide +kernel)

theorem reduce74 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph74 = 0 := by
  have h : moment F graph74 = (-1 : ℝ) * moment F graph74 := by
    apply moment_relabel F graph74 graph74 perm9 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 4 - x 3) * (chi (x 4 - x 5) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce75 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph75 = 0 := by
  have h : moment F graph75 = (-1 : ℝ) * moment F ([(3, 2), (0, 2), (0, 5), (1, 2), (1, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph75 [(3, 2), (0, 2), (0, 5), (1, 2), (1, 5), (4, 5)] (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 3) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 2 (by decide +kernel)
    [(0, 2), (0, 5), (1, 2), (1, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce76 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph76 = 0 := by
  exact moment_odd F hm1 graph76 (by decide +kernel)

theorem reduce77 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph77 = 0 := by
  exact moment_odd F hm1 graph77 (by decide +kernel)

theorem reduce78 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph78 = 0 := by
  have h : moment F graph78 = (-1 : ℝ) * moment F ([(3, 2), (0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph78 [(3, 2), (0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (4, 5)] (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  rw [h, moment_leaf F hF hm1 3 2 (by decide +kernel)
    [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (1, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce79 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph79 = 0 := by
  exact moment_odd F hm1 graph79 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
