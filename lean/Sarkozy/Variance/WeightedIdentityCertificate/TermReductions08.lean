module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term128 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 0 = 0 := by
  have h : moment F (termGraph 1 3 0) =
      (1 : ℝ) * moment F graph178 := by
    apply moment_pointwise F (termGraph 1 3 0) graph178 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 0) = _
  rw [h, reduce178 F hF hm1]
  ring

theorem term129 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 1 = 0 := by
  have h : moment F (termGraph 1 3 1) =
      (1 : ℝ) * moment F graph179 := by
    apply moment_pointwise F (termGraph 1 3 1) graph179 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 1) = _
  rw [h, reduce179 F hF hm1]
  ring

theorem term130 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 2 = 0 := by
  have h : moment F (termGraph 1 3 2) =
      (1 : ℝ) * moment F graph180 := by
    apply moment_pointwise F (termGraph 1 3 2) graph180 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 2) = _
  rw [h, reduce180 F hF hm1]
  ring

theorem term131 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 3 = 0 := by
  have h : moment F (termGraph 1 3 3) =
      (1 : ℝ) * moment F graph181 := by
    apply moment_pointwise F (termGraph 1 3 3) graph181 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 3) = _
  rw [h, reduce181 F hF hm1]
  ring

theorem term132 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 4 = 0 := by
  have h : moment F (termGraph 1 3 4) =
      (-1 : ℝ) * moment F graph182 := by
    apply moment_pointwise F (termGraph 1 3 4) graph182 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 4) = _
  rw [h, reduce182 F hF hm1]
  ring

theorem term133 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 5 = 0 := by
  have h : moment F (termGraph 1 3 5) =
      (-1 : ℝ) * moment F graph183 := by
    apply moment_pointwise F (termGraph 1 3 5) graph183 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 5) = _
  rw [h, reduce183 F hF hm1]
  ring

theorem term134 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 6 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 1 3 6) =
      (-1 : ℝ) * moment F graph184 := by
    apply moment_pointwise F (termGraph 1 3 6) graph184 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 6) = _
  rw [h, reduce184 F hF hm1]
  ring

theorem term135 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 7 = 0 := by
  have h : moment F (termGraph 1 3 7) =
      (-1 : ℝ) * moment F graph185 := by
    apply moment_pointwise F (termGraph 1 3 7) graph185 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 7) = _
  rw [h, reduce185 F hF hm1]
  ring

theorem term136 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 8 = 0 := by
  have h : moment F (termGraph 1 3 8) =
      (1 : ℝ) * moment F graph186 := by
    apply moment_pointwise F (termGraph 1 3 8) graph186 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 8) = _
  rw [h, reduce186 F hF hm1]
  ring

theorem term137 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 9 = 0 := by
  have h : moment F (termGraph 1 3 9) =
      (1 : ℝ) * moment F graph187 := by
    apply moment_pointwise F (termGraph 1 3 9) graph187 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 9) = _
  rw [h, reduce187 F hF hm1]
  ring

theorem term138 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 10 = 0 := by
  have h : moment F (termGraph 1 3 10) =
      (1 : ℝ) * moment F graph188 := by
    apply moment_pointwise F (termGraph 1 3 10) graph188 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 10) = _
  rw [h, reduce188 F hF hm1]
  ring

theorem term139 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 11 = 0 := by
  have h : moment F (termGraph 1 3 11) =
      (1 : ℝ) * moment F graph189 := by
    apply moment_pointwise F (termGraph 1 3 11) graph189 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 11) = _
  rw [h, reduce189 F hF hm1]
  ring

theorem term140 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 12 = 0 := by
  have h : moment F (termGraph 1 3 12) =
      (-1 : ℝ) * moment F graph190 := by
    apply moment_pointwise F (termGraph 1 3 12) graph190 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 12) = _
  rw [h, reduce190 F hF hm1]
  ring

theorem term141 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 13 = 0 := by
  have h : moment F (termGraph 1 3 13) =
      (-1 : ℝ) * moment F graph191 := by
    apply moment_pointwise F (termGraph 1 3 13) graph191 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 13) = _
  rw [h, reduce191 F hF hm1]
  ring

theorem term142 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 14 = 0 := by
  have h : moment F (termGraph 1 3 14) =
      (-1 : ℝ) * moment F graph192 := by
    apply moment_pointwise F (termGraph 1 3 14) graph192 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 14) = _
  rw [h, reduce192 F hF hm1]
  ring

theorem term143 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 3 15 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 1 3 15) =
      (-1 : ℝ) * moment F graph193 := by
    apply moment_pointwise F (termGraph 1 3 15) graph193 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (-1 : ℝ) * moment F (termGraph 1 3 15) = _
  rw [h, reduce193 F hF hm1]
  ring

theorem block8 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 1 3 h) = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * g10 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term128 F hF hm1, term129 F hF hm1, term130 F hF hm1, term131 F hF hm1, term132 F hF hm1, term133 F hF hm1, term134 F hF hm1, term135 F hF hm1, term136 F hF hm1, term137 F hF hm1, term138 F hF hm1, term139 F hF hm1, term140 F hF hm1, term141 F hF hm1, term142 F hF hm1, term143 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
