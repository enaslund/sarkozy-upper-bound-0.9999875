module

public import Sarkozy.PositiveRoots.CoherentTraceFactor

/-! Identify the certified leading form in the physical chamber star-plus-score kernel. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.StarMatrix Sarkozy.L20Cap
open scoped BigOperators ComplexConjugate

local notation "𝒮₆" => StarMatrix.supports (Fin 6)

theorem chamber_old_real (a b : Feature) :
    (CoherentEndpoint.starReal .chamber (CoherentOldChamber.index a)
      (CoherentOldChamber.index b) : ℝ) = starM0 (softL D20) (softR D20) 𝒮₆ a b := by
  have h := congrArg Complex.re (CoherentOldChamber.old_restricted a b)
  simpa [CoherentParameters.old, gaussian, softM, matI] using h

theorem chamber_old_imag (a b : Feature) :
    leading1 .chamber a b = starM1 D20 𝒮₆ a b := by
  have h := congrArg Complex.im (CoherentOldChamber.old_restricted a b)
  simpa [leading1, CoherentParameters.old, gaussian, softM, matI] using h

theorem chamber_leading0 (t : ℝ) (a b : Feature) :
    leading0 .chamber t a b = starM0 (softL D20) (softR D20) 𝒮₆ a b +
      CoherentParameters.strength t * (chamberCoeff a b : ℝ) := by
  have hc : (chamberCoeff a b : ℝ) =
      (CoherentEndpoint.numerator .chamber (CoherentOldChamber.index a)
        (CoherentOldChamber.index b) : ℝ) / 15 := by
    rw [chamberCoeff_eq, CoherentMatrix.coefficient_eq]
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, CoherentEndpoint.numerator]
  unfold leading0
  rw [chamber_old_real, hc]
  ring

variable {p : ℕ} [Fact p.Prime]

theorem chamber_leading_block (t : ℝ) (u v : Feature → ZMod p → ℂ) :
    blockForm (leading0 .chamber t) (leading1 .chamber) u v =
      blockForm (starM0 (softL D20) (softR D20) 𝒮₆) (starM1 D20 𝒮₆) u v +
        (CoherentParameters.strength t : ℂ) *
          ∑ a, ∑ b, (chamberCoeff a b : ℂ) * ip (u a) (v b) := by
  rw [blockForm_expand, blockForm_expand, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  rw [chamber_leading0, chamber_old_imag]
  push_cast
  ring

theorem featAdj_cent (μ : (Fin 6 → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ s c x, s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (f : (Fin 6 → ZMod p) → ℂ) :
    featAdj μ 𝒮₆ (cent μ f) = featAdj μ 𝒮₆ f := by
  funext a
  cases a with
  | inl i => exact vAdj_cent μ hμ1 hinv i f
  | inr S =>
    change (fun z => (rp p : ℂ)⁻¹ * wAdj μ S.val (cent μ f) z) = _
    rw [wAdj_cent μ hinv S.val f]
    rfl

theorem scoreFeatureForm_cent (μ : (Fin 6 → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ s c x, s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (g f : (Fin 6 → ZMod p) → ℂ) :
    scoreFeatureForm μ (cent μ g) (cent μ f) = scoreFeatureForm μ g f := by
  unfold scoreFeatureForm
  rw [featAdj_cent μ hμ1 hinv g, featAdj_cent μ hμ1 hinv f]

noncomputable def leadingKernel (t : ℝ) (x y : Fin 6 → ZMod p) : ℝ :=
  softStarPart D20 x y + CoherentParameters.strength t *
    coherentScore p dictionary39 (chamberConfiguration x y)

theorem physical_leading_identity (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (μ : (Fin 6 → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ s c x, s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (t : ℝ) (f : (Fin 6 → ZMod p) → ℂ) :
    bil μ (cent μ f) (leadingKernel t) (cent μ f) =
      leadingForm .chamber t μ f + (CoherentParameters.strength t : ℂ) *
        scoreMeanForm μ (cent μ f) (cent μ f) := by
  unfold leadingKernel
  rw [bil_add, bil_smul, chamber_score_factor, scoreFeatureForm_cent μ hμ1 hinv,
    softStar_factor hp2 hp3 μ hμ1 hinv]
  unfold leadingForm scoreFeatureForm
  rw [chamber_leading_block]
  ring

/-- The selected physical leading order with the invariant star-mean term displayed exactly. -/
theorem selected_physical_leading_lower (hW : Sarkozy.Labellings.WeilBound (ZMod p))
    (hp : 4096 ≤ p) (hp3 : p % 4 = 3)
    (hne : (Sarkozy.Labellings.injLabellings (ZMod p) G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℂ) :
    -(rp p * (541674864 / 100000000) * (1 + 434 * rp p)) *
      ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 ≤
        (bil (graphWeight G6 hne) (cent (graphWeight G6 hne) f)
          (leadingKernel (67 / 40)) (cent (graphWeight G6 hne) f) -
          (CoherentParameters.strength (67 / 40) : ℂ) *
            scoreMeanForm (graphWeight G6 hne) (cent (graphWeight G6 hne) f)
              (cent (graphWeight G6 hne) f)).re := by
  rw [physical_leading_identity (by omega) hp3 (graphWeight G6 hne)
    (graphWeight_total G6 hne) (graphWeight_inv G6 hne), add_sub_cancel_right]
  exact selected_chamber_lower hW hp hp3 hne f

end Sarkozy.PositiveRoots.CoherentFrame
