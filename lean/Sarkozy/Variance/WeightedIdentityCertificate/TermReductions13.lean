module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term208 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 0 = 0 := by
  have h : moment F (termGraph 2 3 0) =
      (-1 : ℝ) * moment F graph258 := by
    apply moment_pointwise F (termGraph 2 3 0) graph258 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 0) = _
  rw [h, reduce258 F hF hm1]
  ring

theorem term209 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 1 = 0 := by
  have h : moment F (termGraph 2 3 1) =
      (-1 : ℝ) * moment F graph259 := by
    apply moment_pointwise F (termGraph 2 3 1) graph259 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 1) = _
  rw [h, reduce259 F hF hm1]
  ring

theorem term210 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 2 = 0 := by
  have h : moment F (termGraph 2 3 2) =
      (-1 : ℝ) * moment F graph260 := by
    apply moment_pointwise F (termGraph 2 3 2) graph260 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 2) = _
  rw [h, reduce260 F hF hm1]
  ring

theorem term211 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 3 = 0 := by
  have h : moment F (termGraph 2 3 3) =
      (-1 : ℝ) * moment F graph261 := by
    apply moment_pointwise F (termGraph 2 3 3) graph261 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 3) = _
  rw [h, reduce261 F hF hm1]
  ring

theorem term212 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 4 = 0 := by
  have h : moment F (termGraph 2 3 4) =
      (1 : ℝ) * moment F graph262 := by
    apply moment_pointwise F (termGraph 2 3 4) graph262 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 4) = _
  rw [h, reduce262 F hF hm1]
  ring

theorem term213 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 5 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 3 5) =
      (1 : ℝ) * moment F graph263 := by
    apply moment_pointwise F (termGraph 2 3 5) graph263 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 5) = _
  rw [h, reduce263 F hF hm1]
  ring

theorem term214 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 6 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 3 6) =
      (1 : ℝ) * moment F graph264 := by
    apply moment_pointwise F (termGraph 2 3 6) graph264 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 6) = _
  rw [h, reduce264 F hF hm1]
  ring

theorem term215 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 7 = 0 := by
  have h : moment F (termGraph 2 3 7) =
      (1 : ℝ) * moment F graph265 := by
    apply moment_pointwise F (termGraph 2 3 7) graph265 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 7) = _
  rw [h, reduce265 F hF hm1]
  ring

theorem term216 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 8 = 0 := by
  have h : moment F (termGraph 2 3 8) =
      (-1 : ℝ) * moment F graph266 := by
    apply moment_pointwise F (termGraph 2 3 8) graph266 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 8) = _
  rw [h, reduce266 F hF hm1]
  ring

theorem term217 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 9 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 3 9) =
      (-1 : ℝ) * moment F graph267 := by
    apply moment_pointwise F (termGraph 2 3 9) graph267 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 9) = _
  rw [h, reduce267 F hF hm1]
  ring

theorem term218 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 10 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 3 10) =
      (-1 : ℝ) * moment F graph268 := by
    apply moment_pointwise F (termGraph 2 3 10) graph268 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 10) = _
  rw [h, reduce268 F hF hm1]
  ring

theorem term219 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 11 = 0 := by
  have h : moment F (termGraph 2 3 11) =
      (-1 : ℝ) * moment F graph269 := by
    apply moment_pointwise F (termGraph 2 3 11) graph269 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 11) = _
  rw [h, reduce269 F hF hm1]
  ring

theorem term220 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 12 = 0 := by
  have h : moment F (termGraph 2 3 12) =
      (1 : ℝ) * moment F graph270 := by
    apply moment_pointwise F (termGraph 2 3 12) graph270 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 12) = _
  rw [h, reduce270 F hF hm1]
  ring

theorem term221 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 13 = 0 := by
  have h : moment F (termGraph 2 3 13) =
      (1 : ℝ) * moment F graph271 := by
    apply moment_pointwise F (termGraph 2 3 13) graph271 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 13) = _
  rw [h, reduce271 F hF hm1]
  ring

theorem term222 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 14 = 0 := by
  have h : moment F (termGraph 2 3 14) =
      (1 : ℝ) * moment F graph272 := by
    apply moment_pointwise F (termGraph 2 3 14) graph272 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 14) = _
  rw [h, reduce272 F hF hm1]
  ring

theorem term223 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 3 15 = 0 := by
  have h : moment F (termGraph 2 3 15) =
      (1 : ℝ) * moment F graph273 := by
    apply moment_pointwise F (termGraph 2 3 15) graph273 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 2 3 15) = _
  rw [h, reduce273 F hF hm1]
  ring

theorem block13 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 2 3 h) = (4 : ℝ) * (q F) ^ 3 + (-4 : ℝ) * (q F) ^ 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term208 F hF hm1, term209 F hF hm1, term210 F hF hm1, term211 F hF hm1, term212 F hF hm1, term213 F hF hm1, term214 F hF hm1, term215 F hF hm1, term216 F hF hm1, term217 F hF hm1, term218 F hF hm1, term219 F hF hm1, term220 F hF hm1, term221 F hF hm1, term222 F hF hm1, term223 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
