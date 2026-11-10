module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term176 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 0 = 0 := by
  have h : moment F (termGraph 2 1 0) =
      (-1 : ℝ) * moment F graph226 := by
    apply moment_pointwise F (termGraph 2 1 0) graph226 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 0) = _
  rw [h, reduce226 F hF hm1]
  ring

theorem term177 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 1 = 0 := by
  have h : moment F (termGraph 2 1 1) =
      (-1 : ℝ) * moment F graph227 := by
    apply moment_pointwise F (termGraph 2 1 1) graph227 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 1) = _
  rw [h, reduce227 F hF hm1]
  ring

theorem term178 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 2 = 0 := by
  have h : moment F (termGraph 2 1 2) =
      (-1 : ℝ) * moment F graph228 := by
    apply moment_pointwise F (termGraph 2 1 2) graph228 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 2) = _
  rw [h, reduce228 F hF hm1]
  ring

theorem term179 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 3 = 0 := by
  have h : moment F (termGraph 2 1 3) =
      (-1 : ℝ) * moment F graph229 := by
    apply moment_pointwise F (termGraph 2 1 3) graph229 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 3) = _
  rw [h, reduce229 F hF hm1]
  ring

theorem term180 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 4 = 0 := by
  have h : moment F (termGraph 2 1 4) =
      (1 : ℝ) * moment F graph230 := by
    apply moment_pointwise F (termGraph 2 1 4) graph230 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 4) = _
  rw [h, reduce230 F hF hm1]
  ring

theorem term181 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 5 = 0 := by
  have h : moment F (termGraph 2 1 5) =
      (1 : ℝ) * moment F graph231 := by
    apply moment_pointwise F (termGraph 2 1 5) graph231 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 5) = _
  rw [h, reduce231 F hF hm1]
  ring

theorem term182 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 6 = 0 := by
  have h : moment F (termGraph 2 1 6) =
      (1 : ℝ) * moment F graph232 := by
    apply moment_pointwise F (termGraph 2 1 6) graph232 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 6) = _
  rw [h, reduce232 F hF hm1]
  ring

theorem term183 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 7 = 0 := by
  have h : moment F (termGraph 2 1 7) =
      (1 : ℝ) * moment F graph233 := by
    apply moment_pointwise F (termGraph 2 1 7) graph233 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 7) = _
  rw [h, reduce233 F hF hm1]
  ring

theorem term184 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 8 = 0 := by
  have h : moment F (termGraph 2 1 8) =
      (-1 : ℝ) * moment F graph234 := by
    apply moment_pointwise F (termGraph 2 1 8) graph234 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 8) = _
  rw [h, reduce234 F hF hm1]
  ring

theorem term185 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 9 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 2 1 9) =
      (-1 : ℝ) * moment F graph235 := by
    apply moment_pointwise F (termGraph 2 1 9) graph235 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 9) = _
  rw [h, reduce235 F hF hm1]
  ring

theorem term186 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 10 = 0 := by
  have h : moment F (termGraph 2 1 10) =
      (-1 : ℝ) * moment F graph236 := by
    apply moment_pointwise F (termGraph 2 1 10) graph236 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 10) = _
  rw [h, reduce236 F hF hm1]
  ring

theorem term187 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 11 = 0 := by
  have h : moment F (termGraph 2 1 11) =
      (-1 : ℝ) * moment F graph237 := by
    apply moment_pointwise F (termGraph 2 1 11) graph237 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 11) = _
  rw [h, reduce237 F hF hm1]
  ring

theorem term188 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 12 = 0 := by
  have h : moment F (termGraph 2 1 12) =
      (1 : ℝ) * moment F graph238 := by
    apply moment_pointwise F (termGraph 2 1 12) graph238 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 12) = _
  rw [h, reduce238 F hF hm1]
  ring

theorem term189 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 13 = 0 := by
  have h : moment F (termGraph 2 1 13) =
      (1 : ℝ) * moment F graph239 := by
    apply moment_pointwise F (termGraph 2 1 13) graph239 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 13) = _
  rw [h, reduce239 F hF hm1]
  ring

theorem term190 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 14 = 0 := by
  have h : moment F (termGraph 2 1 14) =
      (1 : ℝ) * moment F graph240 := by
    apply moment_pointwise F (termGraph 2 1 14) graph240 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 14) = _
  rw [h, reduce240 F hF hm1]
  ring

theorem term191 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 2 1 15 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 2 1 15) =
      (1 : ℝ) * moment F graph241 := by
    apply moment_pointwise F (termGraph 2 1 15) graph241 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 2 1 15) = _
  rw [h, reduce241 F hF hm1]
  ring

theorem block11 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 2 1 h) = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * g10 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term176 F hF hm1, term177 F hF hm1, term178 F hF hm1, term179 F hF hm1, term180 F hF hm1, term181 F hF hm1, term182 F hF hm1, term183 F hF hm1, term184 F hF hm1, term185 F hF hm1, term186 F hF hm1, term187 F hF hm1, term188 F hF hm1, term189 F hF hm1, term190 F hF hm1, term191 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
