module

public import Sarkozy.Cuts.NormSums

/-! Combining three component bounds using the orthogonal energy of their inputs. -/

@[expose] public section

namespace Sarkozy.Cuts

open Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem three_component_bound (ν : FiniteLaw X) (μ : FiniteLaw Y)
    (f₁ f₂ f₃ : X → ℝ) (g g₁ g₂ g₃ : Y → ℝ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h₁ : nrm ν f₁ ≤ a * nrm μ g₁) (h₂ : nrm ν f₂ ≤ b * nrm μ g₂)
    (h₃ : nrm ν f₃ ≤ c * nrm μ g₃)
    (he : nrm μ g ^ 2 = nrm μ g₁ ^ 2 + nrm μ g₂ ^ 2 + nrm μ g₃ ^ 2) :
    nrm ν (fun x => f₁ x + f₂ x + f₃ x) ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) * nrm μ g := by
  have ht : nrm ν (fun x => f₁ x + f₂ x + f₃ x) ≤
      a * nrm μ g₁ + b * nrm μ g₂ + c * nrm μ g₃ :=
    (nrm_add_le ν (fun x => f₁ x + f₂ x) f₃).trans
      ((add_le_add (nrm_add_le ν f₁ f₂) le_rfl).trans
        (add_le_add (add_le_add h₁ h₂) h₃))
  have ht0 : 0 ≤ a * nrm μ g₁ + b * nrm μ g₂ + c * nrm μ g₃ :=
    add_nonneg (add_nonneg (mul_nonneg ha (nrm_nonneg _ _))
      (mul_nonneg hb (nrm_nonneg _ _))) (mul_nonneg hc (nrm_nonneg _ _))
  have hcs : (a * nrm μ g₁ + b * nrm μ g₂ + c * nrm μ g₃) ^ 2 ≤
      (a ^ 2 + b ^ 2 + c ^ 2) * nrm μ g ^ 2 := by
    rw [he]
    nlinarith only [sq_nonneg (a * nrm μ g₂ - b * nrm μ g₁),
      sq_nonneg (a * nrm μ g₃ - c * nrm μ g₁), sq_nonneg (b * nrm μ g₃ - c * nrm μ g₂)]
  apply ht.trans
  apply (abs_le_of_sq_le_sq' (b := Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) * nrm μ g) ?_
    (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _ _))).2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hcs

end Sarkozy.Cuts
