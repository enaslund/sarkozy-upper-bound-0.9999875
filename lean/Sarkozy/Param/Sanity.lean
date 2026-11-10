module

public import Sarkozy.Param.Anchor

@[expose] public section

/-!
# Non-vacuity checks for the parametrized endgame

* `Params.paper_valid`, `Params.anchor_valid`, `Params.paper_inPaperRange`,
  `Params.anchor_inPaperRange` (in `Sarkozy.Param.Params`): the side conditions hold at both
  instances, and `InPaperRange.valid` shows they hold on the whole range
  `eq:density:parameter-range`.
* `atCounterexamples_zero`, `closingEstimates_zero`: for the zero functional there are no
  counterexamples, so `ClosingEstimates P` is inhabited for every `P` and all closing data
  (the parametrized form of `Sarkozy.Sanity.closingEstimates_zero`).
* `reflection_density_pow`, `globalMomentBound_density_pow`: the functional `Y = α^{72}`
  satisfies the reflection lower bound and the global moment bound together, for every `P`
  with `η ≥ 0`.

**Why there is no joint toy instance.** The conclusion `Target.SarkozyBound ε` of the endgame
does not mention the functional `Y`. A functional satisfying *all* hypotheses (reflection, the
global moment bound and the closing estimates with `Θ < 1`) at some valid `P` would therefore
prove `s(N) ≪ N^{1 − a/(72 − ϑ)}`. The checks above are the separate consistency checks that do
not amount to the theorem: the zero functional meets everything except reflection, and `α^{72}`
meets reflection and the global moment bound.
-/

open Filter
open scoped Topology

namespace Sarkozy.Param

/-- For the zero functional there are no counterexamples: `C L^{-a} α^ϑ < 0` is impossible. -/
theorem atCounterexamples_zero (P : Params) (Q : ℕ → Finset ℤ → Prop) :
    AtCounterexamples P (fun _ _ => (0 : ℝ)) Q := by
  refine Filter.Eventually.of_forall (fun L C hC _ A _ hlt => ?_)
  exfalso
  have h0 : 0 ≤ C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  linarith

/-- `ClosingEstimates P` is inhabited (by the zero functional), for every `P` and any closing
data. -/
noncomputable def closingEstimates_zero (P : Params) (k : ℕ) (L₀ J W H : ℝ) :
    ClosingEstimates P (fun _ _ => (0 : ℝ)) k L₀ J W H where
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
  wrap := atCounterexamples_zero P _
  frame := atCounterexamples_zero P _
  envelopeL := atCounterexamples_zero P _
  envelopeR := atCounterexamples_zero P _
  firstStage := atCounterexamples_zero P _
  joint := atCounterexamples_zero P _

/-- The zero functional meets the global moment bound, for every `P`. -/
theorem globalMomentBound_zero (P : Params) :
    GlobalMomentBound P (fun _ _ => (0 : ℝ)) 1 := by
  intro L _ A _
  have : (0 : ℝ) ≤ (L : ℝ) ^ P.momentSlack := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

/-- `Y = α^{72}` meets the reflection lower bound (with equality). -/
theorem reflection_density_pow (P : Params) :
    ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
      density (P.blockScale * L) A ^ slots ≤
        (fun L A => density (P.blockScale * L) A ^ slots) L A :=
  fun _ _ _ _ => le_rfl

/-- `Y = α^{72}` meets the global moment bound with `M = 1`, for every valid `P` with `η ≥ 0`. -/
theorem globalMomentBound_density_pow (P : Params) (hP : P.Valid) (hη : 0 ≤ P.momentSlack) :
    GlobalMomentBound P (fun L A => density (P.blockScale * L) A ^ slots) 1 := by
  intro L hL A hA
  have hKL : 1 ≤ P.blockScale * L := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero hP.blockScale_pos.ne' (by omega))
  have hδ0 := density_nonneg (P.blockScale * L) A
  have hδ1 := density_le_one hKL hA.1
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ P.momentSlack :=
    Real.one_le_rpow (by exact_mod_cast hL) hη
  have hpow : density (P.blockScale * L) A ^ slots ≤ density (P.blockScale * L) A ^ 2 :=
    pow_le_pow_of_le_one hδ0 hδ1 (by norm_num [slots])
  have hsq : 0 ≤ density (P.blockScale * L) A ^ 2 := sq_nonneg _
  calc density (P.blockScale * L) A ^ slots ≤ density (P.blockScale * L) A ^ 2 := hpow
    _ ≤ 1 * (L : ℝ) ^ P.momentSlack * density (P.blockScale * L) A ^ 2 := by
      nlinarith

/-- The anchor instance of the previous check. -/
theorem anchor_globalMomentBound_density_pow :
    GlobalMomentBound Params.anchor
      (fun L A => density (Params.anchor.blockScale * L) A ^ slots) 1 :=
  globalMomentBound_density_pow _ Params.anchor_valid (by
    norm_num [Params.anchor, Params.ofDecay, Sarkozy.momentSlack])

end Sarkozy.Param
