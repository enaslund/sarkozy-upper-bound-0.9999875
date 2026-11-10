module

public import Sarkozy.PositiveRoots.CoherentTraceMatrix

/-! The exact physical coherent score splits into its certified feature matrix and star means. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.StarMatrix
open scoped BigOperators ComplexConjugate

local notation "𝒮₆" => StarMatrix.supports (Fin 6)

variable {p : ℕ} [Fact p.Prime]

theorem bil_list_sum {α : Type*} (l : List α) (μ : (Fin 6 → ZMod p) → ℝ)
    (K : α → (Fin 6 → ZMod p) → (Fin 6 → ZMod p) → ℝ)
    (g f : (Fin 6 → ZMod p) → ℂ) :
    bil μ g (fun x y => (l.map fun a => K a x y).sum) f =
      (l.map fun a => bil μ g (K a) f).sum := by
  induction l with
  | nil => simp [bil]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, bil_add, ih]

theorem chamber_trace_factor (μ : (Fin 6 → ZMod p) → ℝ)
    (sc : Support × ℚ) (hsc : sc ∈ dictionary39) (g f : (Fin 6 → ZMod p) → ℂ) :
    bil μ g (fun x y => (rp p)⁻¹ *
      tracePair (chamberSupport true sc.1) (chamberSupport false sc.1) x y) f =
      (rp p : ℂ) * ip (featAdj μ 𝒮₆ g (chamberFeature true sc.1))
        (featAdj μ 𝒮₆ f (chamberFeature false sc.1)) +
      (rp p : ℂ)⁻¹ * conj (meanStarAdj μ (chamberSupport true sc.1) g) *
        meanStarAdj μ (chamberSupport false sc.1) f := by
  have hL : 2 ≤ (chamberSupport true sc.1).card := by
    have := (chamber_support_sizes sc hsc).1
    omega
  have hR : 2 ≤ (chamberSupport false sc.1).card := by
    have := (chamber_support_sizes sc hsc).2
    omega
  change _ = (rp p : ℂ) * ip
    (featAdj μ 𝒮₆ g (supportFeature (chamberSupport true sc.1)))
    (featAdj μ 𝒮₆ f (supportFeature (chamberSupport false sc.1))) + _
  rw [supportFeature_star _ hL, supportFeature_star _ hR]
  exact tracePair_scaled_factor μ 𝒮₆
    ⟨chamberSupport true sc.1, mem_filter.mpr ⟨mem_univ _, hL⟩⟩
    ⟨chamberSupport false sc.1, mem_filter.mpr ⟨mem_univ _, hR⟩⟩ g f

noncomputable def scoreFeatureForm (μ : (Fin 6 → ZMod p) → ℝ)
    (g f : (Fin 6 → ZMod p) → ℂ) : ℂ :=
  (rp p : ℂ) * ∑ a, ∑ b, (chamberCoeff a b : ℂ) *
    ip (featAdj μ 𝒮₆ g a) (featAdj μ 𝒮₆ f b)

noncomputable def scoreMeanForm (μ : (Fin 6 → ZMod p) → ℝ)
    (g f : (Fin 6 → ZMod p) → ℂ) : ℂ :=
  (rp p : ℂ)⁻¹ * (dictionary39.map fun sc => (sc.2 : ℂ) *
    conj (meanStarAdj μ (chamberSupport true sc.1) g) *
      meanStarAdj μ (chamberSupport false sc.1) f).sum

theorem chamber_score_factor (μ : (Fin 6 → ZMod p) → ℝ)
    (g f : (Fin 6 → ZMod p) → ℂ) :
    bil μ g (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) f =
      scoreFeatureForm μ g f + scoreMeanForm μ g f := by
  rw [show (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) =
    (fun x y => (dictionary39.map fun sc => (sc.2 : ℝ) * (rp p)⁻¹ *
      tracePair (chamberSupport true sc.1) (chamberSupport false sc.1) x y).sum)
    from funext fun x => funext fun y => score_chamber x y]
  rw [bil_list_sum]
  have he : (dictionary39.map fun sc => bil μ g (fun x y =>
      (sc.2 : ℝ) * (rp p)⁻¹ *
        tracePair (chamberSupport true sc.1) (chamberSupport false sc.1) x y) f).sum =
      (dictionary39.map fun sc =>
        (rp p : ℂ) * ((sc.2 : ℂ) * ip (featAdj μ 𝒮₆ g (chamberFeature true sc.1))
          (featAdj μ 𝒮₆ f (chamberFeature false sc.1))) +
        (rp p : ℂ)⁻¹ * ((sc.2 : ℂ) * conj (meanStarAdj μ (chamberSupport true sc.1) g) *
          meanStarAdj μ (chamberSupport false sc.1) f)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro sc hsc
    rw [show (fun x y => (sc.2 : ℝ) * (rp p)⁻¹ *
      tracePair (chamberSupport true sc.1) (chamberSupport false sc.1) x y) =
      (fun x y => (sc.2 : ℝ) * ((rp p)⁻¹ *
        tracePair (chamberSupport true sc.1) (chamberSupport false sc.1) x y))
      from funext fun x => funext fun y => mul_assoc _ _ _]
    rw [bil_smul, chamber_trace_factor μ sc hsc]
    push_cast
    ring
  rw [he, List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left]
  unfold scoreFeatureForm scoreMeanForm
  rw [chamberCoeff_eval]

end Sarkozy.PositiveRoots.CoherentFrame
