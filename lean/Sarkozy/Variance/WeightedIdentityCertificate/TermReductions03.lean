module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term48 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 0 = 0 := by
  have h : moment F (termGraph 0 3 0) =
      (-1 : ℝ) * moment F graph92 := by
    apply moment_pointwise F (termGraph 0 3 0) graph92 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 0) = _
  rw [h, reduce92 F hF hm1]
  ring

theorem term49 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 1 = 0 := by
  have h : moment F (termGraph 0 3 1) =
      (-1 : ℝ) * moment F graph93 := by
    apply moment_pointwise F (termGraph 0 3 1) graph93 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 1) = _
  rw [h, reduce93 F hF hm1]
  ring

theorem term50 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 2 = 0 := by
  have h : moment F (termGraph 0 3 2) =
      (-1 : ℝ) * moment F graph94 := by
    apply moment_pointwise F (termGraph 0 3 2) graph94 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 2) = _
  rw [h, reduce94 F hF hm1]
  ring

theorem term51 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 3 = 0 := by
  have h : moment F (termGraph 0 3 3) =
      (-1 : ℝ) * moment F graph95 := by
    apply moment_pointwise F (termGraph 0 3 3) graph95 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 3) = _
  rw [h, reduce95 F hF hm1]
  ring

theorem term52 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 4 = 0 := by
  have h : moment F (termGraph 0 3 4) =
      (1 : ℝ) * moment F graph96 := by
    apply moment_pointwise F (termGraph 0 3 4) graph96 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 4) = _
  rw [h, reduce96 F hF hm1]
  ring

theorem term53 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 5 = 0 := by
  have h : moment F (termGraph 0 3 5) =
      (1 : ℝ) * moment F graph97 := by
    apply moment_pointwise F (termGraph 0 3 5) graph97 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 5) = _
  rw [h, reduce97 F hF hm1]
  ring

theorem term54 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 6 = 0 := by
  have h : moment F (termGraph 0 3 6) =
      (1 : ℝ) * moment F graph98 := by
    apply moment_pointwise F (termGraph 0 3 6) graph98 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 6) = _
  rw [h, reduce98 F hF hm1]
  ring

theorem term55 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 7 = 0 := by
  have h : moment F (termGraph 0 3 7) =
      (1 : ℝ) * moment F graph99 := by
    apply moment_pointwise F (termGraph 0 3 7) graph99 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 7) = _
  rw [h, reduce99 F hF hm1]
  ring

theorem term56 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 8 = 0 := by
  have h : moment F (termGraph 0 3 8) =
      (-1 : ℝ) * moment F graph100 := by
    apply moment_pointwise F (termGraph 0 3 8) graph100 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 8) = _
  rw [h, reduce100 F hF hm1]
  ring

theorem term57 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 9 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 0 3 9) =
      (-1 : ℝ) * moment F graph101 := by
    apply moment_pointwise F (termGraph 0 3 9) graph101 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 9) = _
  rw [h, reduce101 F hF hm1]
  ring

theorem term58 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 10 = 0 := by
  have h : moment F (termGraph 0 3 10) =
      (-1 : ℝ) * moment F graph102 := by
    apply moment_pointwise F (termGraph 0 3 10) graph102 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 10) = _
  rw [h, reduce102 F hF hm1]
  ring

theorem term59 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 11 = 0 := by
  have h : moment F (termGraph 0 3 11) =
      (-1 : ℝ) * moment F graph103 := by
    apply moment_pointwise F (termGraph 0 3 11) graph103 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 11) = _
  rw [h, reduce103 F hF hm1]
  ring

theorem term60 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 12 = 0 := by
  have h : moment F (termGraph 0 3 12) =
      (1 : ℝ) * moment F graph104 := by
    apply moment_pointwise F (termGraph 0 3 12) graph104 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 12) = _
  rw [h, reduce104 F hF hm1]
  ring

theorem term61 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 13 = 0 := by
  have h : moment F (termGraph 0 3 13) =
      (1 : ℝ) * moment F graph105 := by
    apply moment_pointwise F (termGraph 0 3 13) graph105 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 13) = _
  rw [h, reduce105 F hF hm1]
  ring

theorem term62 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 14 = 0 := by
  have h : moment F (termGraph 0 3 14) =
      (1 : ℝ) * moment F graph106 := by
    apply moment_pointwise F (termGraph 0 3 14) graph106 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 14) = _
  rw [h, reduce106 F hF hm1]
  ring

theorem term63 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 0 3 15 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 0 3 15) =
      (1 : ℝ) * moment F graph107 := by
    apply moment_pointwise F (termGraph 0 3 15) graph107 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 0 3 15) = _
  rw [h, reduce107 F hF hm1]
  ring

theorem block3 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 0 3 h) = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * g10 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term48 F hF hm1, term49 F hF hm1, term50 F hF hm1, term51 F hF hm1, term52 F hF hm1, term53 F hF hm1, term54 F hF hm1, term55 F hF hm1, term56 F hF hm1, term57 F hF hm1, term58 F hF hm1, term59 F hF hm1, term60 F hF hm1, term61 F hF hm1, term62 F hF hm1, term63 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
