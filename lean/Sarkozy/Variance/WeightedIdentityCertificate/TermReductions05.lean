module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term80 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 0 = 0 := by
  have h : moment F (termGraph 1 0 0) =
      (1 : ℝ) * moment F graph130 := by
    apply moment_pointwise F (termGraph 1 0 0) graph130 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 0) = _
  rw [h, reduce130 F hF hm1]
  ring

theorem term81 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 1 = 0 := by
  have h : moment F (termGraph 1 0 1) =
      (1 : ℝ) * moment F graph131 := by
    apply moment_pointwise F (termGraph 1 0 1) graph131 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 1) = _
  rw [h, reduce131 F hF hm1]
  ring

theorem term82 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 2 = 0 := by
  have h : moment F (termGraph 1 0 2) =
      (1 : ℝ) * moment F graph132 := by
    apply moment_pointwise F (termGraph 1 0 2) graph132 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 2) = _
  rw [h, reduce132 F hF hm1]
  ring

theorem term83 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 3 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 1 0 3) =
      (1 : ℝ) * moment F graph133 := by
    apply moment_pointwise F (termGraph 1 0 3) graph133 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 3) = _
  rw [h, reduce133 F hF hm1]
  ring

theorem term84 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 4 = 0 := by
  have h : moment F (termGraph 1 0 4) =
      (-1 : ℝ) * moment F graph134 := by
    apply moment_pointwise F (termGraph 1 0 4) graph134 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 4) = _
  rw [h, reduce134 F hF hm1]
  ring

theorem term85 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 5 = 0 := by
  have h : moment F (termGraph 1 0 5) =
      (-1 : ℝ) * moment F graph135 := by
    apply moment_pointwise F (termGraph 1 0 5) graph135 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 5) = _
  rw [h, reduce135 F hF hm1]
  ring

theorem term86 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 6 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 1 0 6) =
      (-1 : ℝ) * moment F graph136 := by
    apply moment_pointwise F (termGraph 1 0 6) graph136 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 6) = _
  rw [h, reduce136 F hF hm1]
  ring

theorem term87 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 7 = 0 := by
  have h : moment F (termGraph 1 0 7) =
      (-1 : ℝ) * moment F graph137 := by
    apply moment_pointwise F (termGraph 1 0 7) graph137 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 7) = _
  rw [h, reduce137 F hF hm1]
  ring

theorem term88 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 8 = 0 := by
  have h : moment F (termGraph 1 0 8) =
      (1 : ℝ) * moment F graph138 := by
    apply moment_pointwise F (termGraph 1 0 8) graph138 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 8) = _
  rw [h, reduce138 F hF hm1]
  ring

theorem term89 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 9 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 1 0 9) =
      (1 : ℝ) * moment F graph139 := by
    apply moment_pointwise F (termGraph 1 0 9) graph139 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 9) = _
  rw [h, reduce139 F hF hm1]
  ring

theorem term90 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 10 = 0 := by
  have h : moment F (termGraph 1 0 10) =
      (1 : ℝ) * moment F graph140 := by
    apply moment_pointwise F (termGraph 1 0 10) graph140 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 10) = _
  rw [h, reduce140 F hF hm1]
  ring

theorem term91 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 11 = 0 := by
  have h : moment F (termGraph 1 0 11) =
      (1 : ℝ) * moment F graph141 := by
    apply moment_pointwise F (termGraph 1 0 11) graph141 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 11) = _
  rw [h, reduce141 F hF hm1]
  ring

theorem term92 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 12 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 1 0 12) =
      (-1 : ℝ) * moment F graph142 := by
    apply moment_pointwise F (termGraph 1 0 12) graph142 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 12) = _
  rw [h, reduce142 F hF hm1]
  ring

theorem term93 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 13 = 0 := by
  have h : moment F (termGraph 1 0 13) =
      (-1 : ℝ) * moment F graph143 := by
    apply moment_pointwise F (termGraph 1 0 13) graph143 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 13) = _
  rw [h, reduce143 F hF hm1]
  ring

theorem term94 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 14 = 0 := by
  have h : moment F (termGraph 1 0 14) =
      (-1 : ℝ) * moment F graph144 := by
    apply moment_pointwise F (termGraph 1 0 14) graph144 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 14) = _
  rw [h, reduce144 F hF hm1]
  ring

theorem term95 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 0 15 = 0 := by
  have h : moment F (termGraph 1 0 15) =
      (-1 : ℝ) * moment F graph145 := by
    apply moment_pointwise F (termGraph 1 0 15) graph145 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 0 15) = _
  rw [h, reduce145 F hF hm1]
  ring

theorem block5 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 1 0 h) = (4 : ℝ) * (q F) ^ 3 + (-4 : ℝ) * (q F) ^ 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term80 F hF hm1, term81 F hF hm1, term82 F hF hm1, term83 F hF hm1, term84 F hF hm1, term85 F hF hm1, term86 F hF hm1, term87 F hF hm1, term88 F hF hm1, term89 F hF hm1, term90 F hF hm1, term91 F hF hm1, term92 F hF hm1, term93 F hF hm1, term94 F hF hm1, term95 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
