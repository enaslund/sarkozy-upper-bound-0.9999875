module

public import Sarkozy.Variance.WeightedIdentityCertificate.Reductions21

/-! Kernel-checked graph moment reductions. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem reduce440 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph440 = 0 := by
  exact moment_odd F hm1 graph440 (by decide +kernel)

theorem reduce441 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph441 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph441 = (-1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph441 graph45 perm105 (-1)
    intro x
    change chi (x 2 - x 3) * (chi (x 0 - x 3) * (chi (x 1 - x 3) * (chi (x 0 - x 2) * (chi (x 4 - x 2) * (chi (x 1 - x 2) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 1 - x 4) * (chi (x 1 - x 5) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 0) (x 2), chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

theorem reduce442 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph442 = 0 := by
  have h : moment F graph442 = (-1 : ℝ) * moment F graph442 := by
    apply moment_relabel F graph442 graph442 perm18 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 5 - x 3) * (chi (x 1 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 1) * (chi (x 5 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3)]
    ring
  linarith

theorem reduce443 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph443 = 0 := by
  exact moment_odd F hm1 graph443 (by decide +kernel)

theorem reduce444 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph444 = 0 := by
  exact moment_odd F hm1 graph444 (by decide +kernel)

theorem reduce445 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph445 = 0 := by
  have h : moment F graph445 = (-1 : ℝ) * moment F graph445 := by
    apply moment_relabel F graph445 graph445 perm44 (-1)
    intro x
    change chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 3 - x 2) * (chi (x 3 - x 4) * (chi (x 5 - x 4) * (chi (x 5 - x 3) * (1)))))))))) = (-1 : ℝ) * (chi (x 1 - x 0) * (chi (x 2 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (chi (x 5 - x 4) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 3) (x 4)]
    ring
  linarith

theorem reduce446 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph446 = (1 : ℝ) * (q F) ^ 3 + (-1 : ℝ) * (q F) ^ 4 + (-1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph446 = (1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph446 graph45 perm111 (1)
    intro x
    change chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 4 - x 0) * (chi (x 2 - x 0) * (chi (x 2 - x 4) * (chi (x 1 - x 4) * (chi (x 1 - x 2) * (1)))))))))) = (1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 2) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

theorem reduce447 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph447 = 0 := by
  exact moment_odd F hm1 graph447 (by decide +kernel)

theorem reduce448 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph448 = (-1 : ℝ) * (q F) ^ 3 + (1 : ℝ) * (q F) ^ 4 + (1 : ℝ) * (q F) ^ 1 * g5 F := by
  have h : moment F graph448 = (-1 : ℝ) * moment F graph45 := by
    apply moment_relabel F graph448 graph45 perm112 (-1)
    intro x
    change chi (x 0 - x 5) * (chi (x 1 - x 5) * (chi (x 0 - x 3) * (chi (x 2 - x 3) * (chi (x 1 - x 3) * (chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 4 - x 2) * (chi (x 1 - x 2) * (chi (x 1 - x 4) * (1)))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 3 - x 2) * (chi (x 4 - x 2) * (1)))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 0) (x 3), chi_sub_comm hm1 (x 1) (x 3), chi_sub_comm hm1 (x 2) (x 3), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 0) (x 5), chi_sub_comm hm1 (x 1) (x 5)]
    ring
  rw [h, reduce45 F hF hm1]
  ring

theorem reduce449 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph449 = 0 := by
  exact moment_odd F hm1 graph449 (by decide +kernel)

theorem reduce450 (_hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph450 = 0 := by
  exact moment_odd F hm1 graph450 (by decide +kernel)

theorem reduce451 (_hF : ringChar F ≠ 2) (_hm1 : quadraticChar F (-1) = -1) :
    moment F graph451 = (1 : ℝ) * g12 F := by
  simp only [g12, graph451, one_mul]

theorem reduce452 (hF : ringChar F ≠ 2) (hm1 : quadraticChar F (-1) = -1) :
    moment F graph452 = (-1 : ℝ) * g12 F := by
  have h : moment F graph452 = (-1 : ℝ) * moment F graph451 := by
    apply moment_relabel F graph452 graph451 perm113 (-1)
    intro x
    change chi (x 2 - x 0) * (chi (x 4 - x 0) * (chi (x 3 - x 0) * (chi (x 5 - x 0) * (chi (x 4 - x 2) * (chi (x 1 - x 2) * (chi (x 5 - x 2) * (chi (x 1 - x 4) * (chi (x 3 - x 4) * (chi (x 3 - x 1) * (chi (x 5 - x 1) * (chi (x 5 - x 3) * (1)))))))))))) = (-1 : ℝ) * (chi (x 2 - x 0) * (chi (x 3 - x 0) * (chi (x 4 - x 0) * (chi (x 5 - x 0) * (chi (x 2 - x 1) * (chi (x 3 - x 1) * (chi (x 4 - x 1) * (chi (x 5 - x 1) * (chi (x 4 - x 2) * (chi (x 5 - x 2) * (chi (x 4 - x 3) * (chi (x 5 - x 3) * (1)))))))))))))
    rw [chi_sub_comm hm1 (x 1) (x 2), chi_sub_comm hm1 (x 1) (x 4), chi_sub_comm hm1 (x 3) (x 4)]
    ring
  rw [h, reduce451 F hF hm1]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
