module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term32 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 0 = 0 := by
  have h : moment F (termGraph 0 2 0) =
      (-1 : ℝ) * moment F graph75 := by
    apply moment_pointwise F (termGraph 0 2 0) graph75 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 0) = _
  rw [h, reduce75 F hF hm1]
  ring

theorem term33 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 1 = 0 := by
  have h : moment F (termGraph 0 2 1) =
      (-1 : ℝ) * moment F graph76 := by
    apply moment_pointwise F (termGraph 0 2 1) graph76 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 1) = _
  rw [h, reduce76 F hF hm1]
  ring

theorem term34 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 2 = 0 := by
  have h : moment F (termGraph 0 2 2) =
      (-1 : ℝ) * moment F graph77 := by
    apply moment_pointwise F (termGraph 0 2 2) graph77 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 2) = _
  rw [h, reduce77 F hF hm1]
  ring

theorem term35 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 3 = 0 := by
  have h : moment F (termGraph 0 2 3) =
      (-1 : ℝ) * moment F graph78 := by
    apply moment_pointwise F (termGraph 0 2 3) graph78 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 3) = _
  rw [h, reduce78 F hF hm1]
  ring

theorem term36 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 4 = 0 := by
  have h : moment F (termGraph 0 2 4) =
      (1 : ℝ) * moment F graph79 := by
    apply moment_pointwise F (termGraph 0 2 4) graph79 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 4) = _
  rw [h, reduce79 F hF hm1]
  ring

theorem term37 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 5 = 0 := by
  have h : moment F (termGraph 0 2 5) =
      (1 : ℝ) * moment F graph80 := by
    apply moment_pointwise F (termGraph 0 2 5) graph80 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 5) = _
  rw [h, reduce80 F hF hm1]
  ring

theorem term38 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 6 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 0 2 6) =
      (1 : ℝ) * moment F graph81 := by
    apply moment_pointwise F (termGraph 0 2 6) graph81 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 6) = _
  rw [h, reduce81 F hF hm1]
  ring

theorem term39 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 7 = 0 := by
  have h : moment F (termGraph 0 2 7) =
      (1 : ℝ) * moment F graph82 := by
    apply moment_pointwise F (termGraph 0 2 7) graph82 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 7) = _
  rw [h, reduce82 F hF hm1]
  ring

theorem term40 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 8 = 0 := by
  have h : moment F (termGraph 0 2 8) =
      (-1 : ℝ) * moment F graph83 := by
    apply moment_pointwise F (termGraph 0 2 8) graph83 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 8) = _
  rw [h, reduce83 F hF hm1]
  ring

theorem term41 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 9 = 0 := by
  have h : moment F (termGraph 0 2 9) =
      (-1 : ℝ) * moment F graph84 := by
    apply moment_pointwise F (termGraph 0 2 9) graph84 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 9) = _
  rw [h, reduce84 F hF hm1]
  ring

theorem term42 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 10 = 0 := by
  have h : moment F (termGraph 0 2 10) =
      (-1 : ℝ) * moment F graph85 := by
    apply moment_pointwise F (termGraph 0 2 10) graph85 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 10) = _
  rw [h, reduce85 F hF hm1]
  ring

theorem term43 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 11 = 0 := by
  have h : moment F (termGraph 0 2 11) =
      (-1 : ℝ) * moment F graph86 := by
    apply moment_pointwise F (termGraph 0 2 11) graph86 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 11) = _
  rw [h, reduce86 F hF hm1]
  ring

theorem term44 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 12 = 0 := by
  have h : moment F (termGraph 0 2 12) =
      (1 : ℝ) * moment F graph87 := by
    apply moment_pointwise F (termGraph 0 2 12) graph87 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 12) = _
  rw [h, reduce87 F hF hm1]
  ring

theorem term45 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 13 = 0 := by
  have h : moment F (termGraph 0 2 13) =
      (1 : ℝ) * moment F graph88 := by
    apply moment_pointwise F (termGraph 0 2 13) graph88 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 13) = _
  rw [h, reduce88 F hF hm1]
  ring

theorem term46 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 14 = 0 := by
  have h : moment F (termGraph 0 2 14) =
      (1 : ℝ) * moment F graph89 := by
    apply moment_pointwise F (termGraph 0 2 14) graph89 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 14) = _
  rw [h, reduce89 F hF hm1]
  ring

theorem term47 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 2 15 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 0 2 15) =
      (1 : ℝ) * moment F graph91 := by
    apply moment_pointwise F (termGraph 0 2 15) graph91 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 2 15) = _
  rw [h, reduce91 F hF hm1]
  ring

theorem block2 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 0 2 h) = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * g10 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term32 F hF hm1, term33 F hF hm1, term34 F hF hm1, term35 F hF hm1, term36 F hF hm1, term37 F hF hm1, term38 F hF hm1, term39 F hF hm1, term40 F hF hm1, term41 F hF hm1, term42 F hF hm1, term43 F hF hm1, term44 F hF hm1, term45 F hF hm1, term46 F hF hm1, term47 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
