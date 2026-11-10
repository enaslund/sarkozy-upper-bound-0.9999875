module

public import Sarkozy.SpectralD.StarMatrixNorm

/-! One-sided matrix orders transfer through the Fourier block operator `M(Φ̂)`. -/

@[expose] public section

namespace Sarkozy.SpectralD.StarMatrix

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι]

theorem lower_conj {M : ι → ι → ℂ} {g : ℝ}
    (hM : ∀ x, -g * ∑ a, ‖x a‖ ^ 2 ≤ (qform M x).re) (x : ι → ℂ) :
    -g * ∑ a, ‖x a‖ ^ 2 ≤ (qform (fun a b => conj (M a b)) x).re := by
  change _ ≤ (bform (fun a b => conj (M a b)) x x).re
  rw [bform_conj, Complex.conj_re]
  simpa only [Complex.norm_conj, qform, bform] using hM (fun a => conj (x a))

variable {p : ℕ} [Fact p.Prime]

theorem blockForm_lower (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (M0 M1 : ι → ι → ℝ) {g : ℝ}
    (hM : ∀ x, -g * ∑ a, ‖x a‖ ^ 2 ≤ (qform (matI M0 M1) x).re)
    (u : ι → ZMod p → ℂ) (hu : ∀ a, meanC (u a) = 0) :
    -g * ∑ a, l2sq (u a) ≤ (blockForm M0 M1 u u).re := by
  have hmode : ∀ ξ : ZMod p,
      -g * ∑ a, ‖fcoef (u a) ξ‖ ^ 2 ≤
        (bform (fun a b => (M0 a b : ℂ) + chiC p ξ * epsG p * (M1 a b : ℂ))
          (fun a => fcoef (u a) ξ) (fun a => fcoef (u a) ξ)).re := by
    intro ξ
    by_cases hξ : ξ = 0
    · have h0 : ∀ a, fcoef (u a) ξ = 0 := by
        intro a
        rw [hξ, fcoef_zero]
        exact hu a
      simp [h0, bform]
    · have hχ : chiC p ξ = 1 ∨ chiC p ξ = -1 := by
        rw [chiC_apply]
        rcases quadraticChar_dichotomy hξ with h | h <;> rw [h] <;> simp
      have hσ : chiC p ξ * epsG p = I ∨ chiC p ξ * epsG p = -I := by
        rcases (epsG_cases hp2).2 hp3 with he | he <;> rcases hχ with hc | hc <;>
          rw [hc, he] <;> simp
      rcases hσ with h | h
      · rw [h]
        exact hM _
      · rw [h]
        have he : (fun a b => (M0 a b : ℂ) + -I * (M1 a b : ℂ)) =
            fun a b => conj (matI M0 M1 a b) := by
          funext a b
          unfold matI
          rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
        rw [he]
        exact lower_conj hM _
  have he : (∑ ξ, ∑ a, ‖fcoef (u a) ξ‖ ^ 2) = ∑ a, l2sq (u a) := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => (l2sq_eq_sum_fcoef (u a)).symm
  rw [blockForm_eq_modes hp2, Complex.re_sum, ← he, mul_sum]
  exact sum_le_sum fun ξ _ => hmode ξ

end Sarkozy.SpectralD.StarMatrix
