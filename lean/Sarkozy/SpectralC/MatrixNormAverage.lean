module

public import Sarkozy.SpectralC.MatrixNorms
public import Sarkozy.FiniteProbability

/-! A finite matrix norm bound acting on real, law-valued vectors. -/

@[expose] public section

namespace Sarkozy.SpectralC

open Finset
open scoped BigOperators

variable {I Z : Type*} [Fintype I] [Fintype Z]

theorem normLe_real {C : I → I → ℝ} {lam : ℝ}
    (hM : NormLe (fun a b => (C a b : ℂ)) lam) (u v : I → ℝ) :
    |∑ a, ∑ b, u a * C a b * v b| ≤
      lam * Real.sqrt (∑ a, u a ^ 2) * Real.sqrt (∑ b, v b ^ 2) := by
  simpa only [bform, vnorm, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      hM (fun a => (u a : ℂ)) (fun b => (v b : ℂ))

theorem normLe_average {C : I → I → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hM : NormLe (fun a b => (C a b : ℂ)) lam) (ν : FiniteLaw Z)
    (u v : I → Z → ℝ) :
    |ν.expect (fun z => ∑ a, ∑ b, u a z * C a b * v b z)| ≤
      lam * Real.sqrt (∑ a, ν.expect (fun z => u a z ^ 2)) *
        Real.sqrt (∑ b, ν.expect (fun z => v b z ^ 2)) := by
  let U := fun z => Real.sqrt (∑ a, u a z ^ 2)
  let V := fun z => Real.sqrt (∑ b, v b z ^ 2)
  have hsq (w : I → Z → ℝ) :
      ν.expect (fun z => (Real.sqrt (∑ a, w a z ^ 2)) ^ 2) =
        ∑ a, ν.expect (fun z => w a z ^ 2) := by
    simp only [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [FiniteLaw.expect, mul_sum]
    exact sum_comm
  have hcs := ν.abs_expect_mul_le U V
  rw [hsq u, hsq v] at hcs
  calc
    _ ≤ ν.expect (fun z => |∑ a, ∑ b, u a z * C a b * v b z|) := ν.abs_expect_le _
    _ ≤ ν.expect (fun z => lam * (U z * V z)) := ν.expect_mono fun z => by
      simpa only [mul_assoc] using normLe_real hM (fun a => u a z) (fun b => v b z)
    _ = lam * ν.expect (fun z => U z * V z) := ν.expect_const_mul _ _
    _ ≤ lam * |ν.expect (fun z => U z * V z)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hlam
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs hlam

end Sarkozy.SpectralC
