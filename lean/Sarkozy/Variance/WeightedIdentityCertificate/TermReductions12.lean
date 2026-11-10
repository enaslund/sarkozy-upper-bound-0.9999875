module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term192 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 0 = (1 : ℝ) * (q F) ^ 1 + (-3 : ℝ) * (q F) ^ 2 + (2 : ℝ) * (q F) ^ 3 := by
  have h : moment F (termGraph 2 2 0) =
      (-1 : ℝ) * moment F graph242 := by
    apply moment_pointwise F (termGraph 2 2 0) graph242 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 0) = _
  rw [h, reduce242 F hF hm1]
  ring

theorem term193 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 1 = 0 := by
  have h : moment F (termGraph 2 2 1) =
      (-1 : ℝ) * moment F graph243 := by
    apply moment_pointwise F (termGraph 2 2 1) graph243 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 1) = _
  rw [h, reduce243 F hF hm1]
  ring

theorem term194 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 2 = 0 := by
  have h : moment F (termGraph 2 2 2) =
      (-1 : ℝ) * moment F graph244 := by
    apply moment_pointwise F (termGraph 2 2 2) graph244 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 2) = _
  rw [h, reduce244 F hF hm1]
  ring

theorem term195 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 3 = (1 : ℝ) * g5 F := by
  have h : moment F (termGraph 2 2 3) =
      (-1 : ℝ) * moment F graph245 := by
    apply moment_pointwise F (termGraph 2 2 3) graph245 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 3) = _
  rw [h, reduce245 F hF hm1]
  ring

theorem term196 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 4 = 0 := by
  have h : moment F (termGraph 2 2 4) =
      (1 : ℝ) * moment F graph246 := by
    apply moment_pointwise F (termGraph 2 2 4) graph246 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 4) = _
  rw [h, reduce246 F hF hm1]
  ring

theorem term197 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 5 = 0 := by
  have h : moment F (termGraph 2 2 5) =
      (1 : ℝ) * moment F graph247 := by
    apply moment_pointwise F (termGraph 2 2 5) graph247 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 5) = _
  rw [h, reduce247 F hF hm1]
  ring

theorem term198 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 6 = 0 := by
  have h : moment F (termGraph 2 2 6) =
      (1 : ℝ) * moment F graph248 := by
    apply moment_pointwise F (termGraph 2 2 6) graph248 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 6) = _
  rw [h, reduce248 F hF hm1]
  ring

theorem term199 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 7 = 0 := by
  have h : moment F (termGraph 2 2 7) =
      (1 : ℝ) * moment F graph249 := by
    apply moment_pointwise F (termGraph 2 2 7) graph249 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 7) = _
  rw [h, reduce249 F hF hm1]
  ring

theorem term200 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 8 = 0 := by
  have h : moment F (termGraph 2 2 8) =
      (-1 : ℝ) * moment F graph250 := by
    apply moment_pointwise F (termGraph 2 2 8) graph250 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 8) = _
  rw [h, reduce250 F hF hm1]
  ring

theorem term201 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 9 = 0 := by
  have h : moment F (termGraph 2 2 9) =
      (-1 : ℝ) * moment F graph251 := by
    apply moment_pointwise F (termGraph 2 2 9) graph251 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 9) = _
  rw [h, reduce251 F hF hm1]
  ring

theorem term202 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 10 = 0 := by
  have h : moment F (termGraph 2 2 10) =
      (-1 : ℝ) * moment F graph252 := by
    apply moment_pointwise F (termGraph 2 2 10) graph252 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 10) = _
  rw [h, reduce252 F hF hm1]
  ring

theorem term203 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 11 = 0 := by
  have h : moment F (termGraph 2 2 11) =
      (-1 : ℝ) * moment F graph253 := by
    apply moment_pointwise F (termGraph 2 2 11) graph253 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 11) = _
  rw [h, reduce253 F hF hm1]
  ring

theorem term204 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 12 = (-1 : ℝ) * (q F) ^ 2 + (4 : ℝ) * (q F) ^ 3 + (-3 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 2 12) =
      (1 : ℝ) * moment F graph254 := by
    apply moment_pointwise F (termGraph 2 2 12) graph254 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 12) = _
  rw [h, reduce254 F hF hm1]
  ring

theorem term205 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 13 = 0 := by
  have h : moment F (termGraph 2 2 13) =
      (1 : ℝ) * moment F graph255 := by
    apply moment_pointwise F (termGraph 2 2 13) graph255 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 13) = _
  rw [h, reduce255 F hF hm1]
  ring

theorem term206 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 14 = 0 := by
  have h : moment F (termGraph 2 2 14) =
      (1 : ℝ) * moment F graph256 := by
    apply moment_pointwise F (termGraph 2 2 14) graph256 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 14) = _
  rw [h, reduce256 F hF hm1]
  ring

theorem term207 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 2 15 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 2 2 15) =
      (1 : ℝ) * moment F graph257 := by
    apply moment_pointwise F (termGraph 2 2 15) graph257 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 2 15) = _
  rw [h, reduce257 F hF hm1]
  ring

theorem block12 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 2 2 h) = (1 : ℝ) * (q F) ^ 1 + (-4 : ℝ) * (q F) ^ 2 + (7 : ℝ) * (q F) ^ 3 + (-4 : ℝ) * (q F) ^ 4 + (1 : ℝ) * g5 F + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term192 F hF hm1, term193 F hF hm1, term194 F hF hm1, term195 F hF hm1, term196 F hF hm1, term197 F hF hm1, term198 F hF hm1, term199 F hF hm1, term200 F hF hm1, term201 F hF hm1, term202 F hF hm1, term203 F hF hm1, term204 F hF hm1, term205 F hF hm1, term206 F hF hm1, term207 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
