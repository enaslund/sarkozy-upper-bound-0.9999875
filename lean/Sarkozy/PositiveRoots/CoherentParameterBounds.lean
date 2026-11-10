module

public import Sarkozy.PositiveRoots.CoherentEndpointBounds
public import Sarkozy.PositiveRoots.CoherentOldChamber
public import Sarkozy.PositiveRoots.CoherentOldLayer
public import Sarkozy.PositiveRoots.CoherentMeanBounds
public import Sarkozy.PositiveRoots.CoherentMatrixBound
public import Sarkozy.PositiveRoots.FiniteMatrixInterpolation

/-!
# Leading matrix bounds throughout the coherent parameter interval

These are the matrix and invariant-mean coefficient statements of
`imp:local:coherent-parameter`. The physical feature frames and finite-prime
error estimates are separate analytic assertions.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentParameters

open Finset Sarkozy.SpectralC

noncomputable def chamberCap (t : ℝ) : ℝ :=
  (1 - alpha t) * Real.sqrt 30 + alpha t * (5413 / 1000)

theorem chamber_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 12 / 5) (x : Fin 64 → ℂ) :
    -chamberCap t * ∑ i, ‖x i‖ ^ 2 ≤ (qform (leading .chamber t) x).re := by
  rw [funext (fun i => funext (fun j => interpolation .chamber t i j))]
  exact lower_bound_convex _ _ (alpha_bounds h0 h1).1 (alpha_bounds h0 h1).2
    CoherentOldChamber.old_chamber_bound CoherentEndpoint.chamber_bound x

theorem layer_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 12 / 5) (x : Fin 64 → ℂ) :
    -((219 : ℝ) / 100) * ∑ i, ‖x i‖ ^ 2 ≤ (qform (leading .layer t) x).re := by
  rw [funext (fun i => funext (fun j => interpolation .layer t i j))]
  have h := lower_bound_convex _ _ (alpha_bounds h0 h1).1 (alpha_bounds h0 h1).2
    CoherentOldLayer.old_layer_bound CoherentEndpoint.layer_bound x
  convert h using 1
  ring

theorem chamberCap_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 12 / 5) :
    (5413 : ℝ) / 1000 ≤ chamberCap t := by
  have hs : (5413 : ℝ) / 1000 ≤ Real.sqrt 30 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr (alpha_bounds h0 h1).2)
  unfold chamberCap
  nlinarith

theorem mean_bound {t : ℝ} (h0 : 0 ≤ t) (k : CoherentMean.Kind)
    (x : Fin (CoherentMean.size k) → ℂ) :
    -(strength t * (CoherentMean.cap k : ℝ)) * ∑ i, ‖x i‖ ^ 2 ≤
      (qform (fun i j => (strength t : ℂ) * CoherentMean.leading k i j) x).re :=
  lower_bound_scalar _ (strength_nonneg h0) (CoherentMean.mean_bound k) x

theorem mean_prices_below {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 12 / 5) :
    strength t * (16 * (7 / 100) + 21 / 100) < chamberCap t ∧
      strength t * (21 / 100) < (219 : ℝ) / 100 := by
  have hc := chamberCap_lower h0 h1
  have hs := strength_le_endpoint h1
  constructor <;> linarith

theorem selected_matrix (i j : Fin 64) :
    leading .chamber (67 / 40) i j = CoherentMatrix.leading i j := by
  unfold leading old CoherentMatrix.leading
  rw [selected_values.2, CoherentMatrix.coefficient_eq]
  simp only [CoherentMatrix.strength, CoherentEndpoint.numerator,
    CoherentEndpoint.starReal, CoherentEndpoint.starImag, CoherentEndpoint.sign,
    CoherentMatrix.starReal, CoherentMatrix.starImag]
  push_cast
  ring

theorem selected_chamber_bound (x : Fin 64 → ℂ) :
    -((541674864 : ℝ) / 100000000) * ∑ i, ‖x i‖ ^ 2 ≤
      (qform (leading .chamber (67 / 40)) x).re := by
  rw [funext (fun i => funext (fun j => selected_matrix i j))]
  exact CoherentMatrix.selected_chamber_bound x

theorem selected_mean_price :
    strength (67 / 40) * (16 * (7 / 100) + 21 / 100) < (541674864 : ℝ) / 100000000 := by
  rw [selected_values.2]
  norm_num

end Sarkozy.PositiveRoots.CoherentParameters
