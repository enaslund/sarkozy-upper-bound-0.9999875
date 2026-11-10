module

public import Sarkozy.PositiveRoots.CoherentLeadingIdentity
public import Sarkozy.PositiveRoots.CoherentMeanNumerics
public import Sarkozy.SpectralD.TranslationFeatures
public import Sarkozy.SpectralD.TranslationMeans

/-! The full physical leading order, including the invariant translation sector. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.StarMatrix
open Sarkozy.Labellings Sarkozy.L20Cap
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem scoreMeanForm_average (μ : (Fin 6 → ZMod p) → ℝ)
    (hμ : ∀ c x, μ (affLab 1 c x) = μ x) (f : (Fin 6 → ZMod p) → ℂ) :
    scoreMeanForm μ (translationAverage f) (translationAverage f) = scoreMeanForm μ f f := by
  unfold scoreMeanForm
  simp only [meanStarAdj_average μ hμ]

theorem leadingForm_residual (μ : (Fin 6 → ZMod p) → ℝ)
    (hinv : ∀ s c x, s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (t : ℝ) (f : (Fin 6 → ZMod p) → ℂ) :
    leadingForm .chamber t μ (translationResidual f) = leadingForm .chamber t μ f := by
  unfold leadingForm
  rw [featAdj_residual μ hinv]

/-- The invariant branch is supplied, rather than left as an additional operator hypothesis. -/
theorem physical_leading_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) G6).Nonempty)
    {t g : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 12 / 5) (hg : 18 / 5 ≤ g)
    (hM : ∀ x, -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform (CoherentParameters.leading .chamber t) x).re)
    (f : (Fin 6 → ZMod p) → ℂ) (hf : muE (graphWeight G6 hne) f = 0) :
    -(rp p * g * (1 + 434 * rp p)) * ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 ≤
      (bil (graphWeight G6 hne) f (leadingKernel t) f).re := by
  have hg0 : 0 ≤ g := by linarith
  have hr := rp_nonneg (p := p)
  have hs := CoherentParameters.strength_nonneg ht0
  have hμ (c : ZMod p) (x : Fin 6 → ZMod p) :
      graphWeight G6 hne (affLab 1 c x) = graphWeight G6 hne x :=
    graphWeight_inv G6 hne 1 c x one_ne_zero isSquare_one'
  have hn := graph_leadingForm_lower hW hp hp3 G6 hne g6_degree .chamber t hg0 hM
    (translationResidual f)
  have hi := chamber_scoreMeanForm_lower hW hp3 (by omega) hne (translationAverage f)
  have ha : 0 ≤ ∑ x, graphWeight G6 hne x * ‖translationAverage f x‖ ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (graphWeight_nonneg G6 hne x) (sq_nonneg _)
  have hgΓ : g ≤ g * (1 + 434 * rp p) := by nlinarith [mul_nonneg hg0 hr]
  have hprice := (invariant_branch_below hp ht0 ht1).trans (hg.trans hgΓ)
  have henergy := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprice hr) ha
  have hi' : -(rp p * g * (1 + 434 * rp p)) *
      (∑ x, graphWeight G6 hne x * ‖translationAverage f x‖ ^ 2) ≤
        CoherentParameters.strength t *
          (scoreMeanForm (graphWeight G6 hne) (translationAverage f) (translationAverage f)).re := by
    calc
      _ = -(rp p * (g * (1 + 434 * rp p)) *
          ∑ x, graphWeight G6 hne x * ‖translationAverage f x‖ ^ 2) := by ring
      _ ≤ -(rp p * (CoherentParameters.strength t * invariantMeanPrice p) *
          ∑ x, graphWeight G6 hne x * ‖translationAverage f x‖ ^ 2) := neg_le_neg henergy
      _ = CoherentParameters.strength t * (-(rp p * invariantMeanPrice p) *
          ∑ x, graphWeight G6 hne x * ‖translationAverage f x‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hi hs
  have hc : cent (graphWeight G6 hne) f = f := by
    funext x
    simp only [cent, hf, sub_zero]
  have hid := physical_leading_identity (by omega : p ≠ 2) hp3 (graphWeight G6 hne)
    (graphWeight_total G6 hne) (graphWeight_inv G6 hne) t f
  rw [hc] at hid
  rw [hid, Complex.add_re, Complex.re_ofReal_mul]
  calc
    _ = -(rp p * g * (1 + 434 * rp p)) *
        (∑ x, graphWeight G6 hne x * ‖translationResidual f x‖ ^ 2) +
        -(rp p * g * (1 + 434 * rp p)) *
        (∑ x, graphWeight G6 hne x * ‖translationAverage f x‖ ^ 2) := by
      rw [← translation_energy_split (graphWeight G6 hne) hμ f]
      ring
    _ ≤ (leadingForm .chamber t (graphWeight G6 hne) (translationResidual f)).re +
        CoherentParameters.strength t *
          (scoreMeanForm (graphWeight G6 hne) (translationAverage f) (translationAverage f)).re :=
      add_le_add hn hi'
    _ = _ := by rw [leadingForm_residual _ (graphWeight_inv G6 hne), scoreMeanForm_average _ hμ]

theorem selected_physical_leading_centered_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℂ) (hf : muE (graphWeight G6 hne) f = 0) :
    -(rp p * (541674864 / 100000000) * (1 + 434 * rp p)) *
      ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 ≤
        (bil (graphWeight G6 hne) f (leadingKernel (67 / 40)) f).re :=
  physical_leading_lower hW hp hp3 hne (by norm_num) (by norm_num) (by norm_num)
    CoherentParameters.selected_chamber_bound f hf

theorem parameter_physical_leading_centered_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) G6).Nonempty)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 12 / 5)
    (f : (Fin 6 → ZMod p) → ℂ) (hf : muE (graphWeight G6 hne) f = 0) :
    -(rp p * CoherentParameters.chamberCap t * (1 + 434 * rp p)) *
      ∑ x, graphWeight G6 hne x * ‖f x‖ ^ 2 ≤
        (bil (graphWeight G6 hne) f (leadingKernel t) f).re := by
  have hg : 18 / 5 ≤ CoherentParameters.chamberCap t :=
    (by norm_num : (18 / 5 : ℝ) ≤ 5413 / 1000).trans
      (CoherentParameters.chamberCap_lower ht0 ht1)
  exact physical_leading_lower hW hp hp3 hne ht0 ht1 hg
    (CoherentParameters.chamber_bound ht0 ht1) f hf

end Sarkozy.PositiveRoots.CoherentFrame
