module

public import Sarkozy.SpectralD.TranslationAverage
public import Sarkozy.SpectralD.StarPairFactorization

/-! The nonzero-frequency feature adjoints annihilate the invariant translation sector. -/

@[expose] public section

namespace Sarkozy.SpectralD.StarMatrix

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

theorem eq_zero_of_ip_self (h : ZMod p → ℂ) (hh : ip h h = 0) : h = 0 := by
  have hc : (l2sq h : ℂ) = 0 := (l2sq_eq_re_ip h).trans hh
  have hr : l2sq h = 0 := by exact_mod_cast hc
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold l2sq at hr
  have hs := (mul_eq_zero.mp hr).resolve_left (inv_ne_zero hp)
  funext a
  have ha := (sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg ‖h z‖)).mp hs a (mem_univ a)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (h a)]

variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
theorem featKer_cov (𝒮 : Finset (Finset U)) (a : Feat U 𝒮) (s c : ZMod p)
    (hs : s ≠ 0) (hsq : IsSquare s) (h : ZMod p → ℂ) (x : U → ZMod p) :
    kerMap (featKer 𝒮 a) (fun z => h (s * z + c)) x =
      kerMap (featKer 𝒮 a) h (affLab s c x) := by
  cases a with
  | inl i => exact vertKer_cov i s c h x
  | inr S =>
    change kerMap (fun x z => (rp p)⁻¹ * starKer S.val x z) _ _ =
      kerMap (fun x z => (rp p)⁻¹ * starKer S.val x z) _ _
    rw [kerMap_smul, kerMap_smul, starKer_cov S.val s c hs hsq]

theorem featAdj_invariant (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ s c x, s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (𝒮 : Finset (Finset U)) (v : (U → ZMod p) → ℂ)
    (hv : ∀ c x, v (affLab 1 c x) = v x) : featAdj μ 𝒮 v = 0 := by
  funext a
  apply eq_zero_of_ip_self
  rw [← featKer_adjoint μ 𝒮 v a _ (meanC_featAdj μ 𝒮 v a)]
  have h := kerMap_orth_invariant (labAction μ hinv) (featKer 𝒮 a)
    (featKer_cov 𝒮 a) v hv (featAdj μ 𝒮 v a) (meanC_featAdj μ 𝒮 v a)
  have hc := congrArg (starRingEnd ℂ) h
  simp only [map_sum, map_mul, Complex.conj_ofReal, starRingEnd_self_apply, map_zero] at hc
  convert hc using 1
  apply sum_congr rfl
  intro x _
  ring

theorem featAdj_sub (μ : (U → ZMod p) → ℝ) (𝒮 : Finset (Finset U))
    (f g : (U → ZMod p) → ℂ) : featAdj μ 𝒮 (fun x => f x - g x) =
      fun a z => featAdj μ 𝒮 f a z - featAdj μ 𝒮 g a z := by
  funext a z
  cases a with
  | inl i =>
    unfold featAdj vAdj muE
    have hi (x : U → ZMod p) :
        (if x i = z then f x - g x else 0) =
          (if x i = z then f x else 0) - (if x i = z then g x else 0) := by
      split_ifs <;> ring
    simp only [hi, mul_sub, sum_sub_distrib]
    ring
  | inr S =>
    simp only [featAdj, wAdj, mul_sub, sum_sub_distrib]
    ring

theorem featAdj_residual (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ s c x, s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (𝒮 : Finset (Finset U)) (f : (U → ZMod p) → ℂ) :
    featAdj μ 𝒮 (translationResidual f) = featAdj μ 𝒮 f := by
  unfold translationResidual
  rw [featAdj_sub,
    featAdj_invariant μ hinv 𝒮 (translationAverage f) (translationAverage_invariant f)]
  funext a z
  exact sub_zero _

end Sarkozy.SpectralD.StarMatrix
