module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term240 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 0 = 0 := by
  have h : moment F (termGraph 3 0 0) =
      (1 : ℝ) * moment F graph290 := by
    apply moment_pointwise F (termGraph 3 0 0) graph290 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 0) = _
  rw [h, reduce290 F hF hm1]
  ring

theorem term241 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 1 = 0 := by
  have h : moment F (termGraph 3 0 1) =
      (1 : ℝ) * moment F graph291 := by
    apply moment_pointwise F (termGraph 3 0 1) graph291 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 1) = _
  rw [h, reduce291 F hF hm1]
  ring

theorem term242 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 2 = 0 := by
  have h : moment F (termGraph 3 0 2) =
      (1 : ℝ) * moment F graph292 := by
    apply moment_pointwise F (termGraph 3 0 2) graph292 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 2) = _
  rw [h, reduce292 F hF hm1]
  ring

theorem term243 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 3 = 0 := by
  have h : moment F (termGraph 3 0 3) =
      (1 : ℝ) * moment F graph293 := by
    apply moment_pointwise F (termGraph 3 0 3) graph293 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 3) = _
  rw [h, reduce293 F hF hm1]
  ring

theorem term244 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 4 = 0 := by
  have h : moment F (termGraph 3 0 4) =
      (-1 : ℝ) * moment F graph294 := by
    apply moment_pointwise F (termGraph 3 0 4) graph294 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 4) = _
  rw [h, reduce294 F hF hm1]
  ring

theorem term245 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 5 = 0 := by
  have h : moment F (termGraph 3 0 5) =
      (-1 : ℝ) * moment F graph295 := by
    apply moment_pointwise F (termGraph 3 0 5) graph295 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 5) = _
  rw [h, reduce295 F hF hm1]
  ring

theorem term246 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 6 = 0 := by
  have h : moment F (termGraph 3 0 6) =
      (-1 : ℝ) * moment F graph296 := by
    apply moment_pointwise F (termGraph 3 0 6) graph296 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 6) = _
  rw [h, reduce296 F hF hm1]
  ring

theorem term247 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 7 = 0 := by
  have h : moment F (termGraph 3 0 7) =
      (-1 : ℝ) * moment F graph297 := by
    apply moment_pointwise F (termGraph 3 0 7) graph297 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 7) = _
  rw [h, reduce297 F hF hm1]
  ring

theorem term248 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 8 = 0 := by
  have h : moment F (termGraph 3 0 8) =
      (1 : ℝ) * moment F graph298 := by
    apply moment_pointwise F (termGraph 3 0 8) graph298 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 8) = _
  rw [h, reduce298 F hF hm1]
  ring

theorem term249 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 9 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 3 0 9) =
      (1 : ℝ) * moment F graph299 := by
    apply moment_pointwise F (termGraph 3 0 9) graph299 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 9) = _
  rw [h, reduce299 F hF hm1]
  ring

theorem term250 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 10 = 0 := by
  have h : moment F (termGraph 3 0 10) =
      (1 : ℝ) * moment F graph300 := by
    apply moment_pointwise F (termGraph 3 0 10) graph300 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 10) = _
  rw [h, reduce300 F hF hm1]
  ring

theorem term251 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 11 = 0 := by
  have h : moment F (termGraph 3 0 11) =
      (1 : ℝ) * moment F graph301 := by
    apply moment_pointwise F (termGraph 3 0 11) graph301 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 11) = _
  rw [h, reduce301 F hF hm1]
  ring

theorem term252 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 12 = 0 := by
  have h : moment F (termGraph 3 0 12) =
      (-1 : ℝ) * moment F graph302 := by
    apply moment_pointwise F (termGraph 3 0 12) graph302 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 12) = _
  rw [h, reduce302 F hF hm1]
  ring

theorem term253 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 13 = 0 := by
  have h : moment F (termGraph 3 0 13) =
      (-1 : ℝ) * moment F graph303 := by
    apply moment_pointwise F (termGraph 3 0 13) graph303 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 13) = _
  rw [h, reduce303 F hF hm1]
  ring

theorem term254 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 14 = 0 := by
  have h : moment F (termGraph 3 0 14) =
      (-1 : ℝ) * moment F graph304 := by
    apply moment_pointwise F (termGraph 3 0 14) graph304 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 14) = _
  rw [h, reduce304 F hF hm1]
  ring

theorem term255 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 0 15 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 3 0 15) =
      (-1 : ℝ) * moment F graph305 := by
    apply moment_pointwise F (termGraph 3 0 15) graph305 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 0 15) = _
  rw [h, reduce305 F hF hm1]
  ring

theorem block15 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 3 0 h) = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * g10 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term240 F hF hm1, term241 F hF hm1, term242 F hF hm1, term243 F hF hm1, term244 F hF hm1, term245 F hF hm1, term246 F hF hm1, term247 F hF hm1, term248 F hF hm1, term249 F hF hm1, term250 F hF hm1, term251 F hF hm1, term252 F hF hm1, term253 F hF hm1, term254 F hF hm1, term255 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
