module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term16 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 0 = 0 := by
  have h : moment F (termGraph 0 1 0) =
      (-1 : ℝ) * moment F graph47 := by
    apply moment_pointwise F (termGraph 0 1 0) graph47 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 0) = _
  rw [h, reduce47 F hF hm1]
  ring

theorem term17 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 1 = 0 := by
  have h : moment F (termGraph 0 1 1) =
      (-1 : ℝ) * moment F graph48 := by
    apply moment_pointwise F (termGraph 0 1 1) graph48 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 1) = _
  rw [h, reduce48 F hF hm1]
  ring

theorem term18 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 2 = 0 := by
  have h : moment F (termGraph 0 1 2) =
      (-1 : ℝ) * moment F graph49 := by
    apply moment_pointwise F (termGraph 0 1 2) graph49 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 2) = _
  rw [h, reduce49 F hF hm1]
  ring

theorem term19 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 3 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 0 1 3) =
      (-1 : ℝ) * moment F graph55 := by
    apply moment_pointwise F (termGraph 0 1 3) graph55 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 3) = _
  rw [h, reduce55 F hF hm1]
  ring

theorem term20 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 4 = 0 := by
  have h : moment F (termGraph 0 1 4) =
      (1 : ℝ) * moment F graph56 := by
    apply moment_pointwise F (termGraph 0 1 4) graph56 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 4) = _
  rw [h, reduce56 F hF hm1]
  ring

theorem term21 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 5 = 0 := by
  have h : moment F (termGraph 0 1 5) =
      (1 : ℝ) * moment F graph57 := by
    apply moment_pointwise F (termGraph 0 1 5) graph57 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 5) = _
  rw [h, reduce57 F hF hm1]
  ring

theorem term22 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 6 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 0 1 6) =
      (1 : ℝ) * moment F graph65 := by
    apply moment_pointwise F (termGraph 0 1 6) graph65 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 6) = _
  rw [h, reduce65 F hF hm1]
  ring

theorem term23 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 7 = 0 := by
  have h : moment F (termGraph 0 1 7) =
      (1 : ℝ) * moment F graph66 := by
    apply moment_pointwise F (termGraph 0 1 7) graph66 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 7) = _
  rw [h, reduce66 F hF hm1]
  ring

theorem term24 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 8 = 0 := by
  have h : moment F (termGraph 0 1 8) =
      (-1 : ℝ) * moment F graph67 := by
    apply moment_pointwise F (termGraph 0 1 8) graph67 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 8) = _
  rw [h, reduce67 F hF hm1]
  ring

theorem term25 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 9 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 0 1 9) =
      (-1 : ℝ) * moment F graph68 := by
    apply moment_pointwise F (termGraph 0 1 9) graph68 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 9) = _
  rw [h, reduce68 F hF hm1]
  ring

theorem term26 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 10 = 0 := by
  have h : moment F (termGraph 0 1 10) =
      (-1 : ℝ) * moment F graph69 := by
    apply moment_pointwise F (termGraph 0 1 10) graph69 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 10) = _
  rw [h, reduce69 F hF hm1]
  ring

theorem term27 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 11 = 0 := by
  have h : moment F (termGraph 0 1 11) =
      (-1 : ℝ) * moment F graph70 := by
    apply moment_pointwise F (termGraph 0 1 11) graph70 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 11) = _
  rw [h, reduce70 F hF hm1]
  ring

theorem term28 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 12 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 0 1 12) =
      (1 : ℝ) * moment F graph71 := by
    apply moment_pointwise F (termGraph 0 1 12) graph71 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 12) = _
  rw [h, reduce71 F hF hm1]
  ring

theorem term29 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 13 = 0 := by
  have h : moment F (termGraph 0 1 13) =
      (1 : ℝ) * moment F graph72 := by
    apply moment_pointwise F (termGraph 0 1 13) graph72 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 13) = _
  rw [h, reduce72 F hF hm1]
  ring

theorem term30 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 14 = 0 := by
  have h : moment F (termGraph 0 1 14) =
      (1 : ℝ) * moment F graph73 := by
    apply moment_pointwise F (termGraph 0 1 14) graph73 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 14) = _
  rw [h, reduce73 F hF hm1]
  ring

theorem term31 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 1 15 = 0 := by
  have h : moment F (termGraph 0 1 15) =
      (1 : ℝ) * moment F graph74 := by
    apply moment_pointwise F (termGraph 0 1 15) graph74 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 0 1 15) = _
  rw [h, reduce74 F hF hm1]
  ring

theorem block1 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 0 1 h) = (4 : ℝ) * (q F) ^ 3 + (-4 : ℝ) * (q F) ^ 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term16 F hF hm1, term17 F hF hm1, term18 F hF hm1, term19 F hF hm1, term20 F hF hm1, term21 F hF hm1, term22 F hF hm1, term23 F hF hm1, term24 F hF hm1, term25 F hF hm1, term26 F hF hm1, term27 F hF hm1, term28 F hF hm1, term29 F hF hm1, term30 F hF hm1, term31 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
