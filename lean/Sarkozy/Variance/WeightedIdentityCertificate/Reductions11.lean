module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions10

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce220 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph220 = 0 := by
  have h : moment F graph220 = (-1 : ℝ) * moment F graph220 := by
    apply moment_relabel F graph220 graph220 perm52 (-1)
    intro x
    change chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 2 - x 4) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4)]
    ring
  linarith

theorem reduce221 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph221 = 0 := by
  exact moment_odd F hm1 graph221 (by decide +kernel)

theorem reduce222 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph222 = 0 := by
  have h : moment F graph222 = (-1 : ℝ) * moment F graph222 := by
    apply moment_relabel F graph222 graph222 perm53 (-1)
    intro x
    change chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 1) * (chi (x 0 - x 2) * (chi (x 0 - x 5) * (chi (x 3 - x 5) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 3) (x 5)]
    ring
  linarith

theorem reduce223 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph223 = 0 := by
  exact moment_odd F hm1 graph223 (by decide +kernel)

theorem reduce224 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph224 = 0 := by
  exact moment_odd F hm1 graph224 (by decide +kernel)

theorem reduce225 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph225 = (-1 : ℝ) * g10 F := by
  have h : moment F graph225 = (-1 : ℝ) * moment F graph90 := by
    apply moment_relabel F graph225 graph90 perm0 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 1) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 4) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce90 F hF hm1]
  ring

theorem reduce226 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph226 = 0 := by
  have h : moment F graph226 = (1 : ℝ) * moment F ([(1, 2), (0, 2), (0, 5), (2, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph226 [(1, 2), (0, 2), (0, 5), (2, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))
    ring
  rw [h, moment_leaf F hF hm1 1 2 (by decide +kernel)
    [(0, 2), (0, 5), (2, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce227 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph227 = 0 := by
  exact moment_odd F hm1 graph227 (by decide +kernel)

theorem reduce228 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph228 = 0 := by
  exact moment_odd F hm1 graph228 (by decide +kernel)

theorem reduce229 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph229 = 0 := by
  have h : moment F graph229 = (1 : ℝ) * moment F ([(3, 5), (0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (2, 4), (4, 5)] : Graph) := by
    apply moment_pointwise F graph229 [(3, 5), (0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (2, 4), (4, 5)] (1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 5 - x 3) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 3 5 (by decide +kernel)
    [(0, 1), (0, 2), (0, 4), (0, 5), (1, 2), (2, 4), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce230 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph230 = 0 := by
  exact moment_odd F hm1 graph230 (by decide +kernel)

theorem reduce231 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph231 = 0 := by
  have h : moment F graph231 = (-1 : ℝ) * moment F graph231 := by
    apply moment_relabel F graph231 graph231 perm54 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 1 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 3 - x 1) * (chi (x 5 - x 4) * (chi (x 5 - x 3) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2)]
    ring
  linarith

theorem reduce232 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph232 = 0 := by
  have h : moment F graph232 = (-1 : ℝ) * moment F graph232 := by
    apply moment_relabel F graph232 graph232 perm37 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 3) * (chi (x 1 - x 3) * (chi (x 4 - x 5) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce233 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph233 = 0 := by
  exact moment_odd F hm1 graph233 (by decide +kernel)

theorem reduce234 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph234 = 0 := by
  exact moment_odd F hm1 graph234 (by decide +kernel)

theorem reduce235 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph235 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 := by
  have h : moment F graph235 = (-1 : ℝ) * moment F graph64 := by
    apply moment_relabel F graph235 graph64 perm55 (-1)
    intro x
    change chi (x 5 - x 0) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 1 - x 5) * (chi (x 2 - x 1) * (chi (x 2 - x 4) * (chi (x 3 - x 4) * (chi (x 3 - x 2) * (1)))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (1)))))))))
    rw [chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce64 F hF hm1]
  ring

theorem reduce236 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph236 = 0 := by
  have h : moment F graph236 = (1 : ℝ) * moment F ([(1, 2), (0, 2), (0, 4), (0, 5), (2, 4), (3, 4), (3, 5), (4, 5)] : Graph) := by
    apply moment_pointwise F graph236 [(1, 2), (0, 2), (0, 4), (0, 5), (2, 4), (3, 4), (3, 5), (4, 5)] (1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))) = (1 : ℝ) * (chi (x 2 - x 1) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    ring
  rw [h, moment_leaf F hF hm1 1 2 (by decide +kernel)
    [(0, 2), (0, 4), (0, 5), (2, 4), (3, 4), (3, 5), (4, 5)] (by decide +kernel), mul_zero]

theorem reduce237 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph237 = 0 := by
  exact moment_odd F hm1 graph237 (by decide +kernel)

theorem reduce238 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph238 = 0 := by
  have h : moment F graph238 = (-1 : ℝ) * moment F graph238 := by
    apply moment_relabel F graph238 graph238 perm56 (-1)
    intro x
    change chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 2) * (chi (x 4 - x 5) * (chi (x 3 - x 5) * (chi (x 3 - x 4) * (1)))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4), chi_sub_comm hm1 (x 3) (x 5), chi_sub_comm hm1 (x 4) (x 5)]
    ring
  linarith

theorem reduce239 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph239 = 0 := by
  exact moment_odd F hm1 graph239 (by decide +kernel)

end Sarkozy.Variance.WeightedIdentityCertificate
