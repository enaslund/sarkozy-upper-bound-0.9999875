module

public import Sarkozy.PositiveRoots.CoherentFrame
public import Sarkozy.PositiveRoots.CoherentParameterBounds
public import Sarkozy.PositiveRoots.FiniteMatrixRestriction
public import Sarkozy.SpectralD.StarMatrixOrder

/-!
The certified coherent matrices on the actual feature frame. These bounds concern the
leading feature form; identifying the complete physical kernel also requires the score's
invariant part and the finite-prime remainder estimates.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.Labellings Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators ComplexConjugate

local notation "𝒮₆" => StarMatrix.supports (Fin 6)

noncomputable def leading0 (c : CoherentEndpoint.Cut) (t : ℝ) (a b : Feature) : ℝ :=
  (CoherentEndpoint.starReal c (CoherentOldChamber.index a) (CoherentOldChamber.index b) : ℝ) +
    CoherentParameters.strength t *
      (CoherentEndpoint.numerator c (CoherentOldChamber.index a)
        (CoherentOldChamber.index b) : ℝ) / 15

noncomputable def leading1 (c : CoherentEndpoint.Cut) (a b : Feature) : ℝ :=
  CoherentEndpoint.starImag c (CoherentOldChamber.index a) (CoherentOldChamber.index b)

theorem leading_matrix (c : CoherentEndpoint.Cut) (t : ℝ) (a b : Feature) :
    StarMatrix.matI (leading0 c t) (leading1 c) a b =
      CoherentParameters.leading c t (CoherentOldChamber.index a)
        (CoherentOldChamber.index b) := by
  apply Complex.ext <;>
    simp [StarMatrix.matI, leading0, leading1, CoherentParameters.leading,
      CoherentParameters.old, gaussian]

theorem restricted_lower (c : CoherentEndpoint.Cut) (t : ℝ) {g : ℝ}
    (hM : ∀ x, -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform (CoherentParameters.leading c t) x).re)
    (x : Feature → ℂ) :
    -g * ∑ a, ‖x a‖ ^ 2 ≤ (qform (StarMatrix.matI (leading0 c t) (leading1 c)) x).re := by
  rw [show StarMatrix.matI (leading0 c t) (leading1 c) =
    (fun a b => CoherentParameters.leading c t (CoherentOldChamber.index a)
      (CoherentOldChamber.index b)) from funext fun a => funext fun b => leading_matrix c t a b]
  exact lower_bound_submatrix _ CoherentOldChamber.embedding hM x

variable {p : ℕ} [Fact p.Prime]

noncomputable def leadingForm (c : CoherentEndpoint.Cut) (t : ℝ)
    (μ : (Fin 6 → ZMod p) → ℝ) (f : (Fin 6 → ZMod p) → ℂ) : ℂ :=
  (rp p : ℂ) * StarMatrix.blockForm (leading0 c t) (leading1 c)
    (StarMatrix.featAdj μ 𝒮₆ f) (StarMatrix.featAdj μ 𝒮₆ f)

theorem graph_leadingForm_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (G : OrientedGraph (Fin 6))
    (hne : (injLabellings (ZMod p) G).Nonempty)
    (hdeg : ∀ j, nbrCount G (univ.erase j) j ≤ 2)
    (c : CoherentEndpoint.Cut) (t : ℝ) {g : ℝ} (hg : 0 ≤ g)
    (hM : ∀ x, -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform (CoherentParameters.leading c t) x).re)
    (f : (Fin 6 → ZMod p) → ℂ) :
    -(rp p * g * (1 + 434 * rp p)) * ∑ x, graphWeight G hne x * ‖f x‖ ^ 2 ≤
      (leadingForm c t (graphWeight G hne) f).re := by
  have hb := StarMatrix.blockForm_lower (by omega : p ≠ 2) hp3
    (leading0 c t) (leading1 c) (restricted_lower c t hM)
    (StarMatrix.featAdj (graphWeight G hne) 𝒮₆ f) (StarMatrix.meanC_featAdj _ _ _)
  have ha := graph_analysis hW hp hp3 G hne hdeg f
  have hc := mul_le_mul_of_nonpos_left ha
    (neg_nonpos.mpr (mul_nonneg (rp_nonneg (p := p)) hg))
  have hs := mul_le_mul_of_nonneg_left hb (rp_nonneg (p := p))
  unfold leadingForm
  rw [Complex.re_ofReal_mul]
  nlinarith

/-- The selected `5.41674864 Γ r` negative price on the actual chamber feature frame. -/
theorem selected_chamber_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) Sarkozy.L20Cap.G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℂ) :
    -(rp p * (541674864 / 100000000) * (1 + 434 * rp p)) *
      ∑ x, graphWeight Sarkozy.L20Cap.G6 hne x * ‖f x‖ ^ 2 ≤
        (leadingForm .chamber (67 / 40) (graphWeight Sarkozy.L20Cap.G6 hne) f).re :=
  graph_leadingForm_lower hW hp hp3 _ hne g6_degree .chamber (67 / 40)
    (by norm_num) CoherentParameters.selected_chamber_bound f

theorem chamber_parameter_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) Sarkozy.L20Cap.G6).Nonempty)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 12 / 5) (f : (Fin 6 → ZMod p) → ℂ) :
    -(rp p * CoherentParameters.chamberCap t * (1 + 434 * rp p)) *
      ∑ x, graphWeight Sarkozy.L20Cap.G6 hne x * ‖f x‖ ^ 2 ≤
        (leadingForm .chamber t (graphWeight Sarkozy.L20Cap.G6 hne) f).re := by
  have hg : 0 ≤ CoherentParameters.chamberCap t :=
    (by norm_num : (0 : ℝ) ≤ 5413 / 1000).trans
      (CoherentParameters.chamberCap_lower ht0 ht1)
  exact graph_leadingForm_lower hW hp hp3 _ hne g6_degree .chamber t hg
    (CoherentParameters.chamber_bound ht0 ht1) f

theorem graph_layer_lower (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (G : OrientedGraph (Fin 6))
    (hne : (injLabellings (ZMod p) G).Nonempty)
    (hdeg : ∀ j, nbrCount G (univ.erase j) j ≤ 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 12 / 5) (f : (Fin 6 → ZMod p) → ℂ) :
    -(rp p * (219 / 100) * (1 + 434 * rp p)) *
      ∑ x, graphWeight G hne x * ‖f x‖ ^ 2 ≤
        (leadingForm .layer t (graphWeight G hne) f).re :=
  graph_leadingForm_lower hW hp hp3 G hne hdeg .layer t (by norm_num)
    (CoherentParameters.layer_bound ht0 ht1) f

end Sarkozy.PositiveRoots.CoherentFrame
