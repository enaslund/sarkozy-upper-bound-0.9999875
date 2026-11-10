module

public import Sarkozy.SpectralD.TranslationAverage
public import Sarkozy.SpectralD.StarPairFactorization

/-! Star means lie in the invariant translation sector. -/

@[expose] public section

namespace Sarkozy.SpectralD.StarMatrix

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
theorem starMean_translation (S : Finset U) (c : ZMod p) (x : U → ZMod p) :
    starMean S (affLab 1 c x) = starMean S x := by
  have h := starKer_cov S 1 c one_ne_zero isSquare_one' (fun _ => 1) x
  have he : ((starMean S x : ℝ) : ℂ) = (starMean S (affLab 1 c x) : ℂ) := by
    simpa only [kerMap, mul_one, ← Complex.ofReal_sum, starMean] using h
  exact Complex.ofReal_injective he.symm

theorem meanStarAdj_average (μ : (U → ZMod p) → ℝ)
    (hμ : ∀ c x, μ (affLab 1 c x) = μ x) (S : Finset U) (f : (U → ZMod p) → ℂ) :
    meanStarAdj μ S (translationAverage f) = meanStarAdj μ S f := by
  have h := weightedPair_average μ hμ (fun x => (starMean S x : ℂ)) f
    (fun c x => congrArg Complex.ofReal (starMean_translation S c x))
  simpa only [weightedPair, meanStarAdj, Complex.conj_ofReal] using h

theorem meanStarAdj_residual (μ : (U → ZMod p) → ℝ)
    (hμ : ∀ c x, μ (affLab 1 c x) = μ x) (S : Finset U) (f : (U → ZMod p) → ℂ) :
    meanStarAdj μ S (translationResidual f) = 0 := by
  unfold translationResidual meanStarAdj
  simp only [mul_sub, sum_sub_distrib]
  exact sub_eq_zero.mpr (meanStarAdj_average μ hμ S f).symm

end Sarkozy.SpectralD.StarMatrix
