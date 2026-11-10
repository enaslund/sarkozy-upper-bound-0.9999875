module

public import Sarkozy.Comparison.Criterion
public import Sarkozy.Comparison.ClosingNumerics





@[expose] public section

open Filter
open scoped Topology

namespace Sarkozy.Sanity

open Sarkozy Sarkozy.Comparison

/-- Some ledger satisfies the fourteen primitive bounds. -/
theorem primitiveLedger_bounds_inhabited : ∃ l : PrimitiveLedger, l.Bounds :=
  ⟨⟨0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 1, 1, 1, 0⟩, by constructor <;> norm_num⟩

/-- For the zero functional there are no counterexamples: `C L^{-decay} α^ϑ < 0` is impossible. -/
theorem atCounterexamples_zero (P : ℕ → Finset ℤ → Prop) :
    AtCounterexamples (fun _ _ => (0 : ℝ)) P := by
  refine Filter.Eventually.of_forall (fun L C hC _ A _ hlt => ?_)
  exfalso
  have h0 : 0 ≤ C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  linarith

/-- `ClosingEstimates` is inhabited (by the zero functional), for any closing data. -/
noncomputable def closingEstimates_zero (k : ℕ) (L₀ J W H : ℝ) :
    ClosingEstimates (fun _ _ => (0 : ℝ)) k L₀ J W H where
  Yfs := fun _ _ => 0
  Yν := fun _ _ => 0
  Jν := fun _ _ => 0
  eL := fun _ _ => 0
  eR := fun _ _ => 0
  VL := fun _ _ => 0
  VR := fun _ _ => 0
  εwrap := fun _ => 0
  εenv := fun _ => 0
  εfirst := fun _ => 0
  εjoint := fun _ => 0
  cwrap := 0
  cenv := 0
  cfirst := 0
  cjoint := 0
  εwrap_tendsto := tendsto_const_nhds
  εenv_tendsto := tendsto_const_nhds
  εfirst_tendsto := tendsto_const_nhds
  εjoint_tendsto := tendsto_const_nhds
  cwrap_nonneg := le_rfl
  cenv_nonneg := le_rfl
  cfirst_nonneg := le_rfl
  cjoint_nonneg := le_rfl
  wrap := atCounterexamples_zero _
  frame := atCounterexamples_zero _
  envelopeL := atCounterexamples_zero _
  envelopeR := atCounterexamples_zero _
  firstStage := atCounterexamples_zero _
  joint := atCounterexamples_zero _

end Sarkozy.Sanity
