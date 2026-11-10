module

public import Sarkozy.SpectralD.StarMatrix
public import Sarkozy.Cuts.Actual

/-! The complex star-kernel forms agree exactly with finite-law real kernel forms. -/

@[expose] public section

namespace Sarkozy.SpectralD.StarMatrix

open Finset Sarkozy.Cuts
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

theorem muE_ofReal (μ : FiniteLaw (U → ZMod p)) (f : (U → ZMod p) → ℝ) :
    muE μ.weight (fun x => (f x : ℂ)) = (μ.expect f : ℂ) := by
  simp only [muE, FiniteLaw.expect, Complex.ofReal_sum, Complex.ofReal_mul]

theorem bil_ofReal (μ : FiniteLaw (U → ZMod p)) (K : (U → ZMod p) → (U → ZMod p) → ℝ)
    (f g : (U → ZMod p) → ℝ) :
    bil μ.weight (fun x => (f x : ℂ)) K (fun x => (g x : ℂ)) =
      (kernelForm μ μ K f g : ℂ) := by
  simp only [bil, kernelForm, LinearMap.mk₂_apply, Complex.conj_ofReal,
    Complex.ofReal_sum, Complex.ofReal_mul]

theorem real_energy (μ : FiniteLaw (U → ZMod p)) (f : (U → ZMod p) → ℝ) :
    (∑ x, μ.weight x * ‖(f x : ℂ)‖ ^ 2) = μ.expect (fun x => f x ^ 2) := by
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, FiniteLaw.expect]

end Sarkozy.SpectralD.StarMatrix
