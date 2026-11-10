module

public import Sarkozy.PositiveRoots.CoherentOldLayerChecks
public import Sarkozy.PositiveRoots.CoherentEndpointSupport
public import Sarkozy.PositiveRoots.CoherentParameters
public import Sarkozy.PositiveRoots.FiniteMatrixBound

/-! The untilted layer matrix has the same rational cap as the endpoint. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentOldLayer

open Finset Sarkozy.SpectralD Sarkozy.SpectralC CoherentEndpoint

theorem model_eq_shift (i j : Fin 27) :
    gaussian (modelR i j) (modelI i j) =
      (100 : ℂ) * ((if i = j then (219 / 100 : ℂ) else 0) +
        CoherentParameters.old .layer (index .layer i) (index .layer j)) := by
  unfold modelR modelI CoherentParameters.old
  split_ifs <;> apply Complex.ext <;> simp [gaussian]
  ring

theorem restricted_bound (x : Fin 27 → ℂ) :
    -((219 : ℝ) / 100) * ∑ i, ‖x i‖ ^ 2 ≤
      (qform (fun i j => CoherentParameters.old .layer (index .layer i) (index .layer j)) x).re := by
  apply lower_bound_of_scaled_nonneg _ modelR modelI (s := 100) (by norm_num)
    _ checked_matrix_nonneg x
  intro i j
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using model_eq_shift i j

theorem old_zero (i j : Fin 64)
    (h : i ∉ univ.map (embedding .layer) ∨ j ∉ univ.map (embedding .layer)) :
    CoherentParameters.old .layer i j = 0 := by
  rcases support_checks .layer i j with ha | hz
  · rcases h with hi | hj
    · exact False.elim (hi ((mem_active_iff .layer i).mp ha.1))
    · exact False.elim (hj ((mem_active_iff .layer j).mp ha.2))
  · apply Complex.ext <;> simp [CoherentParameters.old, hz.1, hz.2.1, gaussian]

theorem old_layer_bound (x : Fin 64 → ℂ) :
    -((219 : ℝ) / 100) * ∑ i, ‖x i‖ ^ 2 ≤
      (qform (CoherentParameters.old .layer) x).re := by
  exact lower_bound_of_restriction _ (embedding .layer) (by norm_num)
    old_zero restricted_bound x

end Sarkozy.PositiveRoots.CoherentOldLayer
