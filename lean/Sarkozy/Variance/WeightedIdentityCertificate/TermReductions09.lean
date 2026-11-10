module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term144 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 0 = 0 := by
  have h : moment F (termGraph 1 4 0) =
      (1 : ℝ) * moment F graph194 := by
    apply moment_pointwise F (termGraph 1 4 0) graph194 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 0) = _
  rw [h, reduce194 F hF hm1]
  ring

theorem term145 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 1 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 1 4 1) =
      (1 : ℝ) * moment F graph195 := by
    apply moment_pointwise F (termGraph 1 4 1) graph195 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 1) = _
  rw [h, reduce195 F hF hm1]
  ring

theorem term146 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 2 = 0 := by
  have h : moment F (termGraph 1 4 2) =
      (1 : ℝ) * moment F graph196 := by
    apply moment_pointwise F (termGraph 1 4 2) graph196 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 2) = _
  rw [h, reduce196 F hF hm1]
  ring

theorem term147 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 3 = 0 := by
  have h : moment F (termGraph 1 4 3) =
      (1 : ℝ) * moment F graph197 := by
    apply moment_pointwise F (termGraph 1 4 3) graph197 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 3) = _
  rw [h, reduce197 F hF hm1]
  ring

theorem term148 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 4 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 1 4 4) =
      (-1 : ℝ) * moment F graph198 := by
    apply moment_pointwise F (termGraph 1 4 4) graph198 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 4) = _
  rw [h, reduce198 F hF hm1]
  ring

theorem term149 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 5 = 0 := by
  have h : moment F (termGraph 1 4 5) =
      (-1 : ℝ) * moment F graph199 := by
    apply moment_pointwise F (termGraph 1 4 5) graph199 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 5) = _
  rw [h, reduce199 F hF hm1]
  ring

theorem term150 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 6 = 0 := by
  have h : moment F (termGraph 1 4 6) =
      (-1 : ℝ) * moment F graph200 := by
    apply moment_pointwise F (termGraph 1 4 6) graph200 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 6) = _
  rw [h, reduce200 F hF hm1]
  ring

theorem term151 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 7 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 1 4 7) =
      (-1 : ℝ) * moment F graph201 := by
    apply moment_pointwise F (termGraph 1 4 7) graph201 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 7) = _
  rw [h, reduce201 F hF hm1]
  ring

theorem term152 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 8 = 0 := by
  have h : moment F (termGraph 1 4 8) =
      (1 : ℝ) * moment F graph202 := by
    apply moment_pointwise F (termGraph 1 4 8) graph202 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 8) = _
  rw [h, reduce202 F hF hm1]
  ring

theorem term153 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 9 = 0 := by
  have h : moment F (termGraph 1 4 9) =
      (1 : ℝ) * moment F graph203 := by
    apply moment_pointwise F (termGraph 1 4 9) graph203 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 9) = _
  rw [h, reduce203 F hF hm1]
  ring

theorem term154 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 10 = 0 := by
  have h : moment F (termGraph 1 4 10) =
      (1 : ℝ) * moment F graph204 := by
    apply moment_pointwise F (termGraph 1 4 10) graph204 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 10) = _
  rw [h, reduce204 F hF hm1]
  ring

theorem term155 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 11 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 1 4 11) =
      (1 : ℝ) * moment F graph205 := by
    apply moment_pointwise F (termGraph 1 4 11) graph205 (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 11) = _
  rw [h, reduce205 F hF hm1]
  ring

theorem term156 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 12 = 0 := by
  have h : moment F (termGraph 1 4 12) =
      (-1 : ℝ) * moment F graph206 := by
    apply moment_pointwise F (termGraph 1 4 12) graph206 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 12) = _
  rw [h, reduce206 F hF hm1]
  ring

theorem term157 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 13 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 1 4 13) =
      (-1 : ℝ) * moment F graph207 := by
    apply moment_pointwise F (termGraph 1 4 13) graph207 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 13) = _
  rw [h, reduce207 F hF hm1]
  ring

theorem term158 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 14 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 1 4 14) =
      (-1 : ℝ) * moment F graph208 := by
    apply moment_pointwise F (termGraph 1 4 14) graph208 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 14) = _
  rw [h, reduce208 F hF hm1]
  ring

theorem term159 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 1 4 15 = 0 := by
  have h : moment F (termGraph 1 4 15) =
      (-1 : ℝ) * moment F graph209 := by
    apply moment_pointwise F (termGraph 1 4 15) graph209 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 2 - x 3) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (1 : ℝ) * (1 : ℝ) * moment F (termGraph 1 4 15) = _
  rw [h, reduce209 F hF hm1]
  ring

theorem block9 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 1 4 h) = (2 : ℝ) * (q F) ^ 2 + (-6 : ℝ) * (q F) ^ 3 + (4 : ℝ) * (q F) ^ 4 + (2 : ℝ) * g10 F + (2 : ℝ) * (q F) ^ 1 * g5 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term144 F hF hm1, term145 F hF hm1, term146 F hF hm1, term147 F hF hm1, term148 F hF hm1, term149 F hF hm1, term150 F hF hm1, term151 F hF hm1, term152 F hF hm1, term153 F hF hm1, term154 F hF hm1, term155 F hF hm1, term156 F hF hm1, term157 F hF hm1, term158 F hF hm1, term159 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
