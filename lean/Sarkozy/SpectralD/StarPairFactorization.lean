module

public import Sarkozy.SpectralD.StarMatrixNorm

/-! Exact trace-pair factorization into centered star features and star means. -/

@[expose] public section

namespace Sarkozy.SpectralD.StarMatrix

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

theorem ip_add_constants (f g : ZMod p → ℂ) (hf : meanC f = 0) (hg : meanC g = 0)
    (a b : ℂ) :
    ip (fun z => f z + a) (fun z => g z + b) = ip f g + conj a * b := by
  have hs (v : ZMod p → ℂ) (hv : meanC v = 0) : ∑ z, v z = 0 := by
    exact (mul_eq_zero.mp hv).resolve_left (inv_ne_zero p_ne_zero_C)
  have hf' : ∑ z, conj (f z) = 0 := by rw [← map_sum, hs f hf, map_zero]
  have he : (∑ z, conj (f z + a) * (g z + b)) =
      (∑ z, conj (f z) * g z) + (∑ z, conj (f z)) * b +
        conj a * (∑ z, g z) + (p : ℂ) * (conj a * b) := by
    simp only [map_add, add_mul, mul_add, sum_add_distrib, sum_const, card_univ,
      ZMod.card, nsmul_eq_mul, ← sum_mul, ← mul_sum]
    ring
  unfold ip
  rw [he, hf', hs g hg]
  field_simp [p_ne_zero_C (p := p)]
  ring

variable {U : Type*} [Fintype U] [DecidableEq U]

noncomputable def rawStarAdj (μ : (U → ZMod p) → ℝ) (S : Finset U)
    (f : (U → ZMod p) → ℂ) (z : ZMod p) : ℂ :=
  ∑ x, (μ x : ℂ) * (psi S z x : ℂ) * f x

noncomputable def meanStarAdj (μ : (U → ZMod p) → ℝ) (S : Finset U)
    (f : (U → ZMod p) → ℂ) : ℂ :=
  ∑ x, (μ x : ℂ) * (starMean S x : ℂ) * f x

theorem rawStarAdj_eq (μ : (U → ZMod p) → ℝ) (S : Finset U)
    (f : (U → ZMod p) → ℂ) :
    rawStarAdj μ S f = fun z => wAdj μ S f z + meanStarAdj μ S f := by
  funext z
  exact (sub_add_cancel _ _).symm

theorem ip_rawStarAdj (μ : (U → ZMod p) → ℝ) (S T : Finset U)
    (g f : (U → ZMod p) → ℂ) :
    ip (rawStarAdj μ S g) (rawStarAdj μ T f) =
      ip (wAdj μ S g) (wAdj μ T f) + conj (meanStarAdj μ S g) * meanStarAdj μ T f := by
  rw [rawStarAdj_eq, rawStarAdj_eq]
  exact ip_add_constants _ _ (meanC_wAdj μ S g) (meanC_wAdj μ T f) _ _

noncomputable def tracePair (S T : Finset U) (x y : U → ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * ∑ z, psi S z x * psi T z y

theorem bil_tracePair (μ : (U → ZMod p) → ℝ) (S T : Finset U)
    (g f : (U → ZMod p) → ℂ) :
    bil μ g (tracePair S T) f = ip (rawStarAdj μ S g) (rawStarAdj μ T f) := by
  unfold bil tracePair ip rawStarAdj
  simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]
  simp only [mul_sum, sum_mul]
  conv_lhs => arg 2; ext x; rw [sum_comm]
  rw [sum_comm]
  conv_rhs => arg 2; ext z; rw [sum_comm]
  apply sum_congr rfl
  intro z _
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  ring

/-- No asymptotic estimate or injectivity is used in this exact decomposition. -/
theorem tracePair_factor (μ : (U → ZMod p) → ℝ) (S T : Finset U)
    (g f : (U → ZMod p) → ℂ) :
    bil μ g (tracePair S T) f =
      ip (wAdj μ S g) (wAdj μ T f) + conj (meanStarAdj μ S g) * meanStarAdj μ T f := by
  rw [bil_tracePair, ip_rawStarAdj]

theorem tracePair_scaled_factor (μ : (U → ZMod p) → ℝ)
    (𝒮 : Finset (Finset U)) (S T : 𝒮) (g f : (U → ZMod p) → ℂ) :
    bil μ g (fun x y => (rp p)⁻¹ * tracePair S.val T.val x y) f =
      (rp p : ℂ) * ip (featAdj μ 𝒮 g (Sum.inr S)) (featAdj μ 𝒮 f (Sum.inr T)) +
        ((rp p : ℂ)⁻¹) * conj (meanStarAdj μ S.val g) * meanStarAdj μ T.val f := by
  rw [bil_smul, tracePair_factor]
  change _ = (rp p : ℂ) * ip
    (fun z => (rp p : ℂ)⁻¹ * wAdj μ S.val g z)
    (fun z => (rp p : ℂ)⁻¹ * wAdj μ T.val f z) + _
  rw [ip_smul_left, ip_smul_right', map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv]
  have hr : (rp p : ℂ) ≠ 0 := by exact_mod_cast (rp_ne_zero (p := p))
  field_simp

end Sarkozy.SpectralD.StarMatrix
