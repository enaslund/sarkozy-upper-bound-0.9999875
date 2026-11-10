module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions22
public import Sarkozy.Variance.WeightedIdentityCertificate.Terms

/-! Sixteen explicitly checked terms of the weighted character expansion. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem term304 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 0 = 0 := by
  have h : moment F (termGraph 3 4 0) =
      (1 : ℝ) * moment F graph354 := by
    apply moment_pointwise F (termGraph 3 4 0) graph354 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 0) = _
  rw [h, reduce354 F hF hm1]
  ring

theorem term305 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 1 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 3 4 1) =
      (1 : ℝ) * moment F graph355 := by
    apply moment_pointwise F (termGraph 3 4 1) graph355 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 1) = _
  rw [h, reduce355 F hF hm1]
  ring

theorem term306 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 2 = (1 : ℝ) * (q F) ^ 2 + (-3 : ℝ) * (q F) ^ 3 + (2 : ℝ) * (q F) ^ 4 := by
  have h : moment F (termGraph 3 4 2) =
      (1 : ℝ) * moment F graph356 := by
    apply moment_pointwise F (termGraph 3 4 2) graph356 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (1)))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 2) = _
  rw [h, reduce356 F hF hm1]
  ring

theorem term307 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 3 = 0 := by
  have h : moment F (termGraph 3 4 3) =
      (1 : ℝ) * moment F graph357 := by
    apply moment_pointwise F (termGraph 3 4 3) graph357 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 3) = _
  rw [h, reduce357 F hF hm1]
  ring

theorem term308 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 4 = 0 := by
  have h : moment F (termGraph 3 4 4) =
      (-1 : ℝ) * moment F graph358 := by
    apply moment_pointwise F (termGraph 3 4 4) graph358 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 4) = _
  rw [h, reduce358 F hF hm1]
  ring

theorem term309 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 5 = 0 := by
  have h : moment F (termGraph 3 4 5) =
      (-1 : ℝ) * moment F graph359 := by
    apply moment_pointwise F (termGraph 3 4 5) graph359 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 5) = _
  rw [h, reduce359 F hF hm1]
  ring

theorem term310 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 6 = 0 := by
  have h : moment F (termGraph 3 4 6) =
      (-1 : ℝ) * moment F graph360 := by
    apply moment_pointwise F (termGraph 3 4 6) graph360 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 6) = _
  rw [h, reduce360 F hF hm1]
  ring

theorem term311 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 7 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 3 4 7) =
      (-1 : ℝ) * moment F graph361 := by
    apply moment_pointwise F (termGraph 3 4 7) graph361 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 7) = _
  rw [h, reduce361 F hF hm1]
  ring

theorem term312 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 8 = 0 := by
  have h : moment F (termGraph 3 4 8) =
      (1 : ℝ) * moment F graph362 := by
    apply moment_pointwise F (termGraph 3 4 8) graph362 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 3) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 8) = _
  rw [h, reduce362 F hF hm1]
  ring

theorem term313 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 9 = 0 := by
  have h : moment F (termGraph 3 4 9) =
      (1 : ℝ) * moment F graph363 := by
    apply moment_pointwise F (termGraph 3 4 9) graph363 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 9) = _
  rw [h, reduce363 F hF hm1]
  ring

theorem term314 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 10 = 0 := by
  have h : moment F (termGraph 3 4 10) =
      (1 : ℝ) * moment F graph364 := by
    apply moment_pointwise F (termGraph 3 4 10) graph364 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1))))))))) = (1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 10) = _
  rw [h, reduce364 F hF hm1]
  ring

theorem term315 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 11 = (1 : ℝ) * g10 F := by
  have h : moment F (termGraph 3 4 11) =
      (1 : ℝ) * moment F graph365 := by
    apply moment_pointwise F (termGraph 3 4 11) graph365 (1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 3) * (1)))))))))) = (1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 11) = _
  rw [h, reduce365 F hF hm1]
  ring

theorem term316 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 12 = 0 := by
  have h : moment F (termGraph 3 4 12) =
      (-1 : ℝ) * moment F graph366 := by
    apply moment_pointwise F (termGraph 3 4 12) graph366 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))) = (-1 : ℝ) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 12) = _
  rw [h, reduce366 F hF hm1]
  ring

theorem term317 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 13 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 3 4 13) =
      (-1 : ℝ) * moment F graph367 := by
    apply moment_pointwise F (termGraph 3 4 13) graph367 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 13) = _
  rw [h, reduce367 F hF hm1]
  ring

theorem term318 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 14 = (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F (termGraph 3 4 14) =
      (-1 : ℝ) * moment F graph368 := by
    apply moment_pointwise F (termGraph 3 4 14) graph368 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 14) = _
  rw [h, reduce368 F hF hm1]
  ring

theorem term319 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    termValue F 3 4 15 = 0 := by
  have h : moment F (termGraph 3 4 15) =
      (-1 : ℝ) * moment F graph369 := by
    apply moment_pointwise F (termGraph 3 4 15) graph369 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 5 - x 0) * (chi (x 5 - x 3) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 1 - x 3) * (chi (x 4 - x 3) * (1))))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1))))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 2) (x 4)]
    ring
  change (-1 : ℝ) * (1 : ℝ) * moment F (termGraph 3 4 15) = _
  rw [h, reduce369 F hF hm1]
  ring

theorem block19 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    (∑ h : Fin 16, termValue F 3 4 h) = (2 : ℝ) * (q F) ^ 2 + (-6 : ℝ) * (q F) ^ 3 + (4 : ℝ) * (q F) ^ 4 + (2 : ℝ) * g10 F + (2 : ℝ) * (q F) ^ 1 * g5 F := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
    Fin.reduceSucc, add_zero]
  rw [term304 F hF hm1, term305 F hF hm1, term306 F hF hm1, term307 F hF hm1, term308 F hF hm1, term309 F hF hm1, term310 F hF hm1, term311 F hF hm1, term312 F hF hm1, term313 F hF hm1, term314 F hF hm1, term315 F hF hm1, term316 F hF hm1, term317 F hF hm1, term318 F hF hm1, term319 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
