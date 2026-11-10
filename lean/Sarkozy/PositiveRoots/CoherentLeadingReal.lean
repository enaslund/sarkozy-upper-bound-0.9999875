module

public import Sarkozy.PositiveRoots.CoherentLeadingSectors
public import Sarkozy.SpectralD.StarMatrixReal

/-! The two leading chamber orders in the paper's real finite-law form. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.StarMatrix
open Sarkozy.Labellings Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem chamber_old_star_real (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℝ) (hf : (graphLaw G6 hne).expect f = 0) :
    |kernelForm (graphLaw G6 hne) (graphLaw G6 hne) (softStarPart D20) f f| ≤
      (rp p * Real.sqrt 30 * (1 + 434 * rp p)) *
        (graphLaw G6 hne).expect (fun x => f x ^ 2) := by
  have hm : muE (graphWeight G6 hne) (fun x => (f x : ℂ)) = 0 := by
    change muE (graphLaw G6 hne).weight (fun x => (f x : ℂ)) = 0
    rw [muE_ofReal (graphLaw G6 hne), hf, Complex.ofReal_zero]
  have hc : cent (graphWeight G6 hne) (fun x => (f x : ℂ)) = fun x => (f x : ℂ) := by
    funext x
    simp only [cent, hm, sub_zero]
  have h := graph_starPart_norm hW hp hp3 G6 hne g6_degree D20 (softL D20) (softR D20)
    (Real.sqrt_nonneg 30) normLe_softM_D20 (fun x => (f x : ℂ)) (fun x => (f x : ℂ))
  rw [hc, ← softStarPart_eq D20] at h
  change ‖bil (graphLaw G6 hne).weight (fun x => (f x : ℂ)) (softStarPart D20)
    (fun x => (f x : ℂ))‖ ≤ _ at h
  rw [bil_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  change _ ≤ rp p * Real.sqrt 30 * (1 + 434 * rp p) *
    Real.sqrt (∑ x, (graphLaw G6 hne).weight x * ‖(f x : ℂ)‖ ^ 2) *
    Real.sqrt (∑ x, (graphLaw G6 hne).weight x * ‖(f x : ℂ)‖ ^ 2) at h
  rwa [real_energy, mul_assoc, Real.mul_self_sqrt ((graphLaw G6 hne).second_moment_nonneg f)] at h

theorem chamber_leading_real_norm (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) G6).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) (f : (Fin 6 → ZMod p) → ℝ)
    (hf : (graphLaw G6 hne).expect f = 0) :
    |kernelForm (graphLaw G6 hne) (graphLaw G6 hne) (leadingKernel t) f f| ≤
      (rp p * Real.sqrt 30 * (1 + 434 * rp p) +
        CoherentParameters.strength t * (chamberCubeDensity p * rp p / 3)) *
          (graphLaw G6 hne).expect (fun x => f x ^ 2) := by
  have hs := chamber_old_star_real hW hp hp3 hne f hf
  have hH := chamber_score_norm hp3 (by omega) hne f f
  rw [mul_assoc, ← pow_two, nrm_sq_expect] at hH
  have ht0 := CoherentParameters.strength_nonneg ht
  have he : kernelForm (graphLaw G6 hne) (graphLaw G6 hne) (leadingKernel t) f f =
      kernelForm (graphLaw G6 hne) (graphLaw G6 hne) (softStarPart D20) f f +
        CoherentParameters.strength t *
          kernelForm (graphLaw G6 hne) (graphLaw G6 hne)
            (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) f f := by
    simp only [kernelForm, LinearMap.mk₂_apply, leadingKernel, mul_add, add_mul,
      sum_add_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    ring
  rw [he]
  calc
    _ ≤ |kernelForm (graphLaw G6 hne) (graphLaw G6 hne) (softStarPart D20) f f| +
        CoherentParameters.strength t *
          |kernelForm (graphLaw G6 hne) (graphLaw G6 hne)
            (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) f f| := by
      simpa only [abs_mul, abs_of_nonneg ht0] using abs_add_le
        (kernelForm (graphLaw G6 hne) (graphLaw G6 hne) (softStarPart D20) f f)
        (CoherentParameters.strength t * kernelForm (graphLaw G6 hne) (graphLaw G6 hne)
          (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) f f)
    _ ≤ _ := by
      have h := add_le_add hs (mul_le_mul_of_nonneg_left hH ht0)
      convert h using 1
      ring

theorem selected_leading_real_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℝ) (hf : (graphLaw G6 hne).expect f = 0) :
    -(rp p * (541674864 / 100000000) * (1 + 434 * rp p)) *
      (graphLaw G6 hne).expect (fun x => f x ^ 2) ≤
        kernelForm (graphLaw G6 hne) (graphLaw G6 hne) (leadingKernel (67 / 40)) f f := by
  have hm : muE (graphWeight G6 hne) (fun x => (f x : ℂ)) = 0 := by
    change muE (graphLaw G6 hne).weight (fun x => (f x : ℂ)) = 0
    rw [muE_ofReal (graphLaw G6 hne), hf, Complex.ofReal_zero]
  have h := selected_physical_leading_centered_lower hW hp hp3 hne (fun x => (f x : ℂ)) hm
  change _ ≤ (bil (graphLaw G6 hne).weight (fun x => (f x : ℂ))
    (leadingKernel (67 / 40)) (fun x => (f x : ℂ))).re at h
  rw [bil_ofReal, Complex.ofReal_re] at h
  change -(rp p * (541674864 / 100000000) * (1 + 434 * rp p)) *
    (∑ x, (graphLaw G6 hne).weight x * ‖(f x : ℂ)‖ ^ 2) ≤ _ at h
  rwa [real_energy] at h

end Sarkozy.PositiveRoots.CoherentFrame
