module

public import Sarkozy.PositiveRoots.CoherentMeanFrames
public import Sarkozy.PositiveRoots.CoherentMeanCollection
public import Sarkozy.SpectralC.FiniteFrameComplex

/-! The invariant part of the physical score inherits the certified mean-matrix orders. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.Labellings Sarkozy.L20Cap
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem chamber_core_mean_complex (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hne : (injLabellings (ZMod p) G6).Nonempty) (f : (Fin 6 → ZMod p) → ℂ) :
    (∑ i : Fin 5, ‖StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .core i) f‖ ^ 2) ≤
      (chamberCubeDensity p * (p : ℝ)⁻¹) * ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 :=
  finiteFrame_complex_analysis (graphLaw G6 hne) (fun i x => starMean (meanSupport .core i) x)
    (chamber_core_mean_analysis hp3 hp7 hne) f

theorem chamber_mixed_mean_complex (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    (hp6 : 6 ≤ p) (hne : (injLabellings (ZMod p) G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℂ) :
    (∑ i : Fin 10, ‖StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .mixed i) f‖ ^ 2) ≤
      (mixedMeanPrice p * (p : ℝ)⁻¹) * ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 :=
  finiteFrame_complex_analysis (graphLaw G6 hne) (fun i x => starMean (meanSupport .mixed i) x)
    (chamber_mixed_mean_analysis hW hp3 hp6 hne) f

noncomputable def invariantMeanPrice (p : ℕ) : ℝ :=
  (7 / 100) * chamberCubeDensity p + (21 / 100) * mixedMeanPrice p

theorem chamber_scoreMeanForm_lower (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    (hp7 : 7 < p) (hne : (injLabellings (ZMod p) G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℂ) :
    -(rp p * invariantMeanPrice p) * ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 ≤
      (scoreMeanForm (graphWeight G6 hne) f f).re := by
  have hc := CoherentMean.core_mean_bound
    (fun i => StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .core i) f)
  have hm := CoherentMean.mixed_mean_bound
    (fun i => StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .mixed i) f)
  have hcF := chamber_core_mean_complex hp3 hp7 hne f
  have hmF := chamber_mixed_mean_complex hW hp3 (by omega) hne f
  have hb : -(invariantMeanPrice p * (p : ℝ)⁻¹) *
      (∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2) ≤
      (bform (CoherentMean.leading .core)
          (fun i => StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .core i) f)
          (fun i => StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .core i) f) +
        bform (CoherentMean.leading .mixed)
          (fun i => StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .mixed i) f)
          (fun i => StarMatrix.meanStarAdj (graphWeight G6 hne) (meanSupport .mixed i) f)).re := by
    simp only [Complex.add_re]
    change _ ≤ (qform _ _).re + (qform _ _).re
    have hc' := (mul_le_mul_of_nonpos_left hcF (by norm_num : -(7 / 100 : ℝ) ≤ 0)).trans hc
    have hm' := (mul_le_mul_of_nonpos_left hmF (by norm_num : -(21 / 100 : ℝ) ≤ 0)).trans hm
    unfold invariantMeanPrice
    convert add_le_add hc' hm' using 1
    · ring
    · rfl
  rw [scoreMeanForm_blocks, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  have h := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (rp_nonneg (p := p)))
  have hr : rp p ≠ 0 := by exact_mod_cast (rp_ne_zero (p := p))
  have he : (rp p)⁻¹ * (p : ℝ)⁻¹ = rp p := by rw [← rp_sq]; field_simp
  convert h using 1
  calc
    _ = -((rp p)⁻¹ * (p : ℝ)⁻¹ * invariantMeanPrice p) *
        ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 := by rw [he]
    _ = _ := by ring

end Sarkozy.PositiveRoots.CoherentFrame
