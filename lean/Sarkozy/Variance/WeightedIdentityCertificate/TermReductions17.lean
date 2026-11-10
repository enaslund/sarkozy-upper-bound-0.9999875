module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term272 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 0 = 0 := by
  have h : moment F (termGraph 3 2 0) =
      (1 : ℝ) * moment F graph322 := by
    apply moment_pointwise F (termGraph 3 2 0) graph322 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 0) = _
  rw [h, reduce322 F hF hm1]
  ring

theorem term273 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 1 = 0 := by
  have h : moment F (termGraph 3 2 1) =
      (1 : ℝ) * moment F graph323 := by
    apply moment_pointwise F (termGraph 3 2 1) graph323 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 1) = _
  rw [h, reduce323 F hF hm1]
  ring

theorem term274 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 2 = 0 := by
  have h : moment F (termGraph 3 2 2) =
      (1 : ℝ) * moment F graph324 := by
    apply moment_pointwise F (termGraph 3 2 2) graph324 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 2) = _
  rw [h, reduce324 F hF hm1]
  ring

theorem term275 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 3 = 0 := by
  have h : moment F (termGraph 3 2 3) =
      (1 : ℝ) * moment F graph325 := by
    apply moment_pointwise F (termGraph 3 2 3) graph325 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 3) = _
  rw [h, reduce325 F hF hm1]
  ring

theorem term276 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 4 = 0 := by
  have h : moment F (termGraph 3 2 4) =
      (-1 : ℝ) * moment F graph326 := by
    apply moment_pointwise F (termGraph 3 2 4) graph326 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 4) = _
  rw [h, reduce326 F hF hm1]
  ring

theorem term277 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 5 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 3 2 5) =
      (-1 : ℝ) * moment F graph327 := by
    apply moment_pointwise F (termGraph 3 2 5) graph327 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 5) = _
  rw [h, reduce327 F hF hm1]
  ring

theorem term278 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 6 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 3 2 6) =
      (-1 : ℝ) * moment F graph328 := by
    apply moment_pointwise F (termGraph 3 2 6) graph328 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 6) = _
  rw [h, reduce328 F hF hm1]
  ring

theorem term279 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 7 = 0 := by
  have h : moment F (termGraph 3 2 7) =
      (-1 : ℝ) * moment F graph329 := by
    apply moment_pointwise F (termGraph 3 2 7) graph329 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 7) = _
  rw [h, reduce329 F hF hm1]
  ring

theorem term280 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 8 = 0 := by
  have h : moment F (termGraph 3 2 8) =
      (1 : ℝ) * moment F graph330 := by
    apply moment_pointwise F (termGraph 3 2 8) graph330 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 8) = _
  rw [h, reduce330 F hF hm1]
  ring

theorem term281 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 9 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 3 2 9) =
      (1 : ℝ) * moment F graph331 := by
    apply moment_pointwise F (termGraph 3 2 9) graph331 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 9) = _
  rw [h, reduce331 F hF hm1]
  ring

theorem term282 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 10 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 3 2 10) =
      (1 : ℝ) * moment F graph332 := by
    apply moment_pointwise F (termGraph 3 2 10) graph332 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 10) = _
  rw [h, reduce332 F hF hm1]
  ring

theorem term283 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 11 = 0 := by
  have h : moment F (termGraph 3 2 11) =
      (1 : ℝ) * moment F graph333 := by
    apply moment_pointwise F (termGraph 3 2 11) graph333 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 11) = _
  rw [h, reduce333 F hF hm1]
  ring

theorem term284 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 12 = 0 := by
  have h : moment F (termGraph 3 2 12) =
      (-1 : ℝ) * moment F graph334 := by
    apply moment_pointwise F (termGraph 3 2 12) graph334 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 12) = _
  rw [h, reduce334 F hF hm1]
  ring

theorem term285 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 13 = 0 := by
  have h : moment F (termGraph 3 2 13) =
      (-1 : ℝ) * moment F graph335 := by
    apply moment_pointwise F (termGraph 3 2 13) graph335 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 13) = _
  rw [h, reduce335 F hF hm1]
  ring

theorem term286 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 14 = 0 := by
  have h : moment F (termGraph 3 2 14) =
      (-1 : ℝ) * moment F graph336 := by
    apply moment_pointwise F (termGraph 3 2 14) graph336 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 14) = _
  rw [h, reduce336 F hF hm1]
  ring

theorem term287 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 2 15 = 0 := by
  have h : moment F (termGraph 3 2 15) =
      (-1 : ℝ) * moment F graph337 := by
    apply moment_pointwise F (termGraph 3 2 15) graph337 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (-1 : ℝ) * moment F (termGraph 3 2 15) = _
  rw [h, reduce337 F hF hm1]
  ring

theorem block17 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 3 2 h) = (4 : ℝ) * (q F) ^ 3 + (-4 : ℝ) * (q F) ^ 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term272 F hF hm1, term273 F hF hm1, term274 F hF hm1, term275 F hF hm1, term276 F hF hm1, term277 F hF hm1, term278 F hF hm1, term279 F hF hm1, term280 F hF hm1, term281 F hF hm1, term282 F hF hm1, term283 F hF hm1, term284 F hF hm1, term285 F hF hm1, term286 F hF hm1, term287 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
