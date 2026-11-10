module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term224 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 0 = 0 := by
  have h : moment F (termGraph 2 4 0) =
      (-1 : ℝ) * moment F graph274 := by
    apply moment_pointwise F (termGraph 2 4 0) graph274 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 0) = _
  rw [h, reduce274 F hF hm1]
  ring

theorem term225 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 1 = 0 := by
  have h : moment F (termGraph 2 4 1) =
      (-1 : ℝ) * moment F graph275 := by
    apply moment_pointwise F (termGraph 2 4 1) graph275 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 1) = _
  rw [h, reduce275 F hF hm1]
  ring

theorem term226 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 2 = 0 := by
  have h : moment F (termGraph 2 4 2) =
      (-1 : ℝ) * moment F graph276 := by
    apply moment_pointwise F (termGraph 2 4 2) graph276 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 2) = _
  rw [h, reduce276 F hF hm1]
  ring

theorem term227 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 3 = 0 := by
  have h : moment F (termGraph 2 4 3) =
      (-1 : ℝ) * moment F graph277 := by
    apply moment_pointwise F (termGraph 2 4 3) graph277 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 3) = _
  rw [h, reduce277 F hF hm1]
  ring

theorem term228 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 4 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 4 4) =
      (1 : ℝ) * moment F graph278 := by
    apply moment_pointwise F (termGraph 2 4 4) graph278 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 4) = _
  rw [h, reduce278 F hF hm1]
  ring

theorem term229 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 5 = 0 := by
  have h : moment F (termGraph 2 4 5) =
      (1 : ℝ) * moment F graph279 := by
    apply moment_pointwise F (termGraph 2 4 5) graph279 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 5) = _
  rw [h, reduce279 F hF hm1]
  ring

theorem term230 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 6 = 0 := by
  have h : moment F (termGraph 2 4 6) =
      (1 : ℝ) * moment F graph280 := by
    apply moment_pointwise F (termGraph 2 4 6) graph280 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 6) = _
  rw [h, reduce280 F hF hm1]
  ring

theorem term231 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 7 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 2 4 7) =
      (1 : ℝ) * moment F graph281 := by
    apply moment_pointwise F (termGraph 2 4 7) graph281 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 7) = _
  rw [h, reduce281 F hF hm1]
  ring

theorem term232 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 8 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 4 8) =
      (-1 : ℝ) * moment F graph282 := by
    apply moment_pointwise F (termGraph 2 4 8) graph282 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 8) = _
  rw [h, reduce282 F hF hm1]
  ring

theorem term233 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 9 = 0 := by
  have h : moment F (termGraph 2 4 9) =
      (-1 : ℝ) * moment F graph283 := by
    apply moment_pointwise F (termGraph 2 4 9) graph283 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 9) = _
  rw [h, reduce283 F hF hm1]
  ring

theorem term234 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 10 = 0 := by
  have h : moment F (termGraph 2 4 10) =
      (-1 : ℝ) * moment F graph284 := by
    apply moment_pointwise F (termGraph 2 4 10) graph284 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 10) = _
  rw [h, reduce284 F hF hm1]
  ring

theorem term235 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 11 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 2 4 11) =
      (-1 : ℝ) * moment F graph285 := by
    apply moment_pointwise F (termGraph 2 4 11) graph285 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 11) = _
  rw [h, reduce285 F hF hm1]
  ring

theorem term236 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 12 = 0 := by
  have h : moment F (termGraph 2 4 12) =
      (1 : ℝ) * moment F graph286 := by
    apply moment_pointwise F (termGraph 2 4 12) graph286 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 12) = _
  rw [h, reduce286 F hF hm1]
  ring

theorem term237 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 13 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 2 4 13) =
      (1 : ℝ) * moment F graph287 := by
    apply moment_pointwise F (termGraph 2 4 13) graph287 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 13) = _
  rw [h, reduce287 F hF hm1]
  ring

theorem term238 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 14 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 2 4 14) =
      (1 : ℝ) * moment F graph288 := by
    apply moment_pointwise F (termGraph 2 4 14) graph288 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 14) = _
  rw [h, reduce288 F hF hm1]
  ring

theorem term239 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 4 15 = 0 := by
  have h : moment F (termGraph 2 4 15) =
      (1 : ℝ) * moment F graph289 := by
    apply moment_pointwise F (termGraph 2 4 15) graph289 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 4 15) = _
  rw [h, reduce289 F hF hm1]
  ring

theorem block14 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 2 4 h) = (2 : ℝ) * (q F) ^ 2 + (-6 : ℝ) * (q F) ^ 3 + (4 : ℝ) * (q F) ^ 4 + (2 : ℝ) * g10 F + (2 : ℝ) * (q F) ^ 1 * g5 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term224 F hF hm1, term225 F hF hm1, term226 F hF hm1, term227 F hF hm1, term228 F hF hm1, term229 F hF hm1, term230 F hF hm1, term231 F hF hm1, term232 F hF hm1, term233 F hF hm1, term234 F hF hm1, term235 F hF hm1, term236 F hF hm1, term237 F hF hm1, term238 F hF hm1, term239 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
