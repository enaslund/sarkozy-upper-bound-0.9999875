module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions20

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce420 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph420 = (-1 : ℝ) * (q F) ^ 2 + (3 : ℝ) * (q F) ^ 3 + (-2 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph420 = (1 : ℝ) * moment F graph112 := by
    apply moment_relabel F graph420 graph112 perm106 (1)
    intro x
    change chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 5 - x 0) * (chi (x 2 - x 0) * (chi (x 1 - x 5) * (chi (x 1 - x 2) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce112 F hF hm1]
  ring

theorem reduce421 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph421 = 0 := by
  exact moment_odd F hm1 graph421 (by decide +kernel)

theorem reduce422 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph422 = 0 := by
  have h : moment F graph422 = (1 : ℝ) * moment F ([(0, 2), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph422 [(0, 2), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce423 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph423 = 0 := by
  exact moment_odd F hm1 graph423 (by decide +kernel)

theorem reduce424 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph424 = 0 := by
  exact moment_odd F hm1 graph424 (by decide +kernel)

theorem reduce425 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph425 = (1 : ℝ) * g10 F := by
  have h : moment F graph425 = (1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph425 graph90 perm107 (1)
    intro x
    change chi (x 1 - x 4) * (chi (x 0 - x 4) * (chi (x 3 - x 4) * (chi (x 0 - x 1) * (chi (x 5 - x 1) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 2 - x 5) * (chi (x 2 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce426 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph426 = 0 := by
  have h : moment F graph426 = (1 : ℝ) * moment F ([(0, 2), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph426 [(0, 2), (1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 0 2 (by decide +kernel)
    [(1, 2), (1, 5), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce427 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph427 = 0 := by
  exact moment_odd F hm1 graph427 (by decide +kernel)

theorem reduce428 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph428 = 0 := by
  exact moment_odd F hm1 graph428 (by decide +kernel)

theorem reduce429 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph429 = (-1 : ℝ) * g10 F := by
  have h : moment F graph429 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph429 graph90 perm108 (-1)
    intro x
    change chi (x 3 - x 4) * (chi (x 0 - x 4) * (chi (x 1 - x 4) * (chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 1 - x 5) * (chi (x 2 - x 5) * (chi (x 2 - x 1) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 4), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5), chi_sub_comm hm1 (x 2) (x 5)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce430 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph430 = 0 := by
  exact moment_odd F hm1 graph430 (by decide +kernel)

theorem reduce431 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph431 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph431 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph431 graph120 perm109 (1)
    intro x
    change chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce432 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph432 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph432 = (1 : ℝ) * moment F graph120 := by
    apply moment_relabel F graph432 graph120 perm110 (1)
    intro x
    change chi (x 1 - x 5) * (chi (x 0 - x 5) * (chi (x 1 - x 3) * (chi (x 2 - x 3) * (chi (x 4 - x 3) * (chi (x 2 - x 1) * (chi (x 0 - x 1) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 0) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 1), chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce120 F hF hm1]
  ring

theorem reduce433 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph433 = 0 := by
  exact moment_odd F hm1 graph433 (by decide +kernel)

theorem reduce434 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph434 = (1 : ℝ) + (-3 : ℝ) * (q F) ^ 1 + (3 : ℝ) * (q F) ^ 2 + (-1 : ℝ) * (q F) ^ 3 := by
  have h : moment F graph434 = (1 : ℝ) * moment F ([(0, 3), (0, 3)] ++ graph52) := by
    apply moment_pointwise F graph434 ([(0, 3), (0, 3)] ++ graph52) (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))))))
    ring
  have hc : moment F (identify 0 3 graph52) =
      (1 : ℝ) * moment F graph52 := by
    apply moment_pointwise F (identify 0 3 graph52) graph52 (1)
    intro x
    change chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_double F 0 3 (by decide +kernel) graph52, hc]
  rw [reduce52 F hF hm1]
  unfold q
  ring

theorem reduce435 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph435 = (1 : ℝ) * (q F) ^ 1 + (-4 : ℝ) * (q F) ^ 2 + (6 : ℝ) * (q F) ^ 3 + (-3 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph435 = (1 : ℝ) * moment F ([(2, 0), (2, 1)] ++ graph19) := by
    apply moment_pointwise F graph435 ([(2, 0), (2, 1)] ++ graph19) (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))) = (1 : ℝ) * (chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2)]
    ring
  have hc : moment F (identify 0 1 graph19) =
      (1 : ℝ) * moment F graph434 := by
    apply moment_pointwise F (identify 0 1 graph19) graph434 (1)
    intro x
    change chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (1)))))) = (1 : ℝ) * (chi (x 3 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 0) * (1)))))))
    ring
  rw [h, List.cons_append, List.cons_append, List.nil_append,
    moment_degree_two F hF 2 0 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) graph19 (by decide +kernel), hc]
  rw [reduce19 F hF hm1]
  rw [reduce434 F hF hm1]
  unfold q
  ring

theorem reduce436 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph436 = (1 : ℝ) * (q F) ^ 1 + (-4 : ℝ) * (q F) ^ 2 + (6 : ℝ) * (q F) ^ 3 + (-3 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph436 = (1 : ℝ) * moment F graph435 := by
    apply moment_relabel F graph436 graph435 perm1 (1)
    intro x
    change chi (x 0 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 1 - x 3) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 4) * (chi (x 1 - x 5) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce435 F hF hm1]
  ring

theorem reduce437 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph437 = 0 := by
  exact moment_odd F hm1 graph437 (by decide +kernel)

theorem reduce438 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph438 = 0 := by
  exact moment_odd F hm1 graph438 (by decide +kernel)

theorem reduce439 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph439 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph439 = (1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph439 graph45 perm58 (1)
    intro x
    change chi (x 3 - x 2) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 1 - x 2) * (chi (x 0 - x 3) * (chi (x 1 - x 3) * (chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 5) * (chi (x 1 - x 4) * (1)))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
