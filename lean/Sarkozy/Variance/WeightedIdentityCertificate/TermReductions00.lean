module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term0 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 0 = (1 : ℝ) * (q F) ^ 1 + (-3 : ℝ) * (q F) ^ 2 + (2 : ℝ) * (q F) ^ 3 := by
  have h : moment F (termGraph 0 0 0) =
      (-1 : ℝ) * moment F graph8 := by
    apply moment_pointwise F (termGraph 0 0 0) graph8 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 0) = _
  rw [h, reduce8 F hF hm1]
  ring

theorem term1 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 1 = 0 := by
  have h : moment F (termGraph 0 0 1) =
      (-1 : ℝ) * moment F graph9 := by
    apply moment_pointwise F (termGraph 0 0 1) graph9 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 1) = _
  rw [h, reduce9 F hF hm1]
  ring

theorem term2 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 2 = 0 := by
  have h : moment F (termGraph 0 0 2) =
      (-1 : ℝ) * moment F graph10 := by
    apply moment_pointwise F (termGraph 0 0 2) graph10 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 2) = _
  rw [h, reduce10 F hF hm1]
  ring

theorem term3 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 3 = 0 := by
  have h : moment F (termGraph 0 0 3) =
      (-1 : ℝ) * moment F graph11 := by
    apply moment_pointwise F (termGraph 0 0 3) graph11 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 3) = _
  rw [h, reduce11 F hF hm1]
  ring

theorem term4 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 4 = 0 := by
  have h : moment F (termGraph 0 0 4) =
      (1 : ℝ) * moment F graph12 := by
    apply moment_pointwise F (termGraph 0 0 4) graph12 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 4) = _
  rw [h, reduce12 F hF hm1]
  ring

theorem term5 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 5 = (1 : ℝ) * g5 F := by
  have h : moment F (termGraph 0 0 5) =
      (1 : ℝ) * moment F graph14 := by
    apply moment_pointwise F (termGraph 0 0 5) graph14 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 5) = _
  rw [h, reduce14 F hF hm1]
  ring

theorem term6 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 6 = 0 := by
  have h : moment F (termGraph 0 0 6) =
      (1 : ℝ) * moment F graph15 := by
    apply moment_pointwise F (termGraph 0 0 6) graph15 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 6) = _
  rw [h, reduce15 F hF hm1]
  ring

theorem term7 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 7 = 0 := by
  have h : moment F (termGraph 0 0 7) =
      (1 : ℝ) * moment F graph16 := by
    apply moment_pointwise F (termGraph 0 0 7) graph16 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 7) = _
  rw [h, reduce16 F hF hm1]
  ring

theorem term8 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 8 = 0 := by
  have h : moment F (termGraph 0 0 8) =
      (-1 : ℝ) * moment F graph17 := by
    apply moment_pointwise F (termGraph 0 0 8) graph17 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 8) = _
  rw [h, reduce17 F hF hm1]
  ring

theorem term9 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 9 = 0 := by
  have h : moment F (termGraph 0 0 9) =
      (-1 : ℝ) * moment F graph18 := by
    apply moment_pointwise F (termGraph 0 0 9) graph18 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 9) = _
  rw [h, reduce18 F hF hm1]
  ring

theorem term10 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 10 = (-1 : ℝ) * (q F) ^ 2 + (4 : ℝ) * (q F) ^ 3 + (-3 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 0 0 10) =
      (-1 : ℝ) * moment F graph26 := by
    apply moment_pointwise F (termGraph 0 0 10) graph26 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 10) = _
  rw [h, reduce26 F hF hm1]
  ring

theorem term11 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 11 = 0 := by
  have h : moment F (termGraph 0 0 11) =
      (-1 : ℝ) * moment F graph27 := by
    apply moment_pointwise F (termGraph 0 0 11) graph27 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 11) = _
  rw [h, reduce27 F hF hm1]
  ring

theorem term12 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 12 = 0 := by
  have h : moment F (termGraph 0 0 12) =
      (1 : ℝ) * moment F graph28 := by
    apply moment_pointwise F (termGraph 0 0 12) graph28 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 12) = _
  rw [h, reduce28 F hF hm1]
  ring

theorem term13 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 13 = 0 := by
  have h : moment F (termGraph 0 0 13) =
      (1 : ℝ) * moment F graph29 := by
    apply moment_pointwise F (termGraph 0 0 13) graph29 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 13) = _
  rw [h, reduce29 F hF hm1]
  ring

theorem term14 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 14 = 0 := by
  have h : moment F (termGraph 0 0 14) =
      (1 : ℝ) * moment F graph30 := by
    apply moment_pointwise F (termGraph 0 0 14) graph30 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 14) = _
  rw [h, reduce30 F hF hm1]
  ring

theorem term15 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 0 15 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 0 0 15) =
      (1 : ℝ) * moment F graph46 := by
    apply moment_pointwise F (termGraph 0 0 15) graph46 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 0 15) = _
  rw [h, reduce46 F hF hm1]
  ring

theorem block0 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 0 0 h) = (1 : ℝ) * (q F) ^ 1 + (-4 : ℝ) * (q F) ^ 2 + (7 : ℝ) * (q F) ^ 3 + (-4 : ℝ) * (q F) ^ 4 + (1 : ℝ) * g5 F + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term0 F hF hm1, term1 F hF hm1, term2 F hF hm1, term3 F hF hm1, term4 F hF hm1, term5 F hF hm1, term6 F hF hm1, term7 F hF hm1, term8 F hF hm1, term9 F hF hm1, term10 F hF hm1, term11 F hF hm1, term12 F hF hm1, term13 F hF hm1, term14 F hF hm1, term15 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
