module

public import Sarkozy.Param.Compat

@[expose] public section

/-!
# Monotonicity in the price exponent

For `a ≤ a'`, a least normalized counterexample `(C, L, A)` for the exponent `a` is a least
normalized counterexample `(C L^{a'−a}, L, A)` for the exponent `a'`
(`def:record:counterexample`): at the scale `L` the two lower bounds coincide,
`C L^{a'−a} L^{-a'} α^ϑ = C L^{-a} α^ϑ`, and at smaller scales `ℓ < L`,
`C ℓ^{-a} α^ϑ ≤ C L^{a'−a} ℓ^{-a'} α^ϑ`. Since the closing estimates are uniform in the
induction constant `C ≥ 1`, estimates at `a'` imply the same estimates, with the same closing
data, at `a`.

* `atCounterexamples_mono`, `ClosingEstimates.mono`: this transfer along `Params.ofDecay`.
* `anchor_closingEstimates_of_record`: the hard-coded closing estimates (record exponent) give
  the closing estimates at the anchor `a₀`, with the same closing data. So the hypotheses of
  the endgame at `a₀` are implied by those at the record exponent: they are not stronger.
* `sarkozyBound_epsAnchor_of_record`: the hypotheses of the hard-coded endgame give
  `Target.SarkozyBound Param.anchorSaving` through the endgame at `a₀`.

This is a consistency check of the parametrization, not a route to the anchor: the point of
`a₀` is that the estimates at `a₀` carry the smaller prices of `a₀` (`t = e^{2(a−a₀)570} = 1`
in `sec:four-routes-closing`, and the selection factors `p^{2a}` of `Sarkozy.TheoremC`), hence
more closing margin; the transfer goes from `a'` to `a ≤ a'` with unchanged closing data.
-/

open Filter
open scoped Topology

namespace Sarkozy.Param

open Sarkozy.Comparison (jointTheta)

/-- **Least counterexamples are monotone in the price exponent.** For `a ≤ a'`, a property of
the least counterexamples for `a'` (uniform in `C ≥ 1`) holds at the least counterexamples
for `a`. -/
theorem atCounterexamples_mono {a a' : ℝ} (haa : a ≤ a') {Y : ℕ → Finset ℤ → ℝ}
    {Q : ℕ → Finset ℤ → Prop} (hQ : AtCounterexamples (Params.ofDecay a') Y Q) :
    AtCounterexamples (Params.ofDecay a) Y Q := by
  filter_upwards [hQ, eventually_ge_atTop 1] with L hL hL1
  intro C hC hind A hA hcounter
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hgap : 0 ≤ a' - a := sub_nonneg.mpr haa
  have hfac : 1 ≤ (L : ℝ) ^ (a' - a) := Real.one_le_rpow hL1' hgap
  have hC' : 1 ≤ C * (L : ℝ) ^ (a' - a) := by nlinarith
  apply hL (C * (L : ℝ) ^ (a' - a)) hC'
  · intro k hk hkL A' hA'
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hb := hind k hk hkL A' hA'
    have hw : 0 ≤ (k : ℝ) ^ (-a') * density (blockScale * k) A' ^ densityExponent :=
      mul_nonneg (Real.rpow_nonneg hkpos.le _) (Real.rpow_nonneg (density_nonneg _ _) _)
    have hkL' : (k : ℝ) ^ (a' - a) ≤ (L : ℝ) ^ (a' - a) :=
      Real.rpow_le_rpow hkpos.le (by exact_mod_cast hkL.le) hgap
    have hsplit : (k : ℝ) ^ (-a) = (k : ℝ) ^ (a' - a) * (k : ℝ) ^ (-a') := by
      rw [← Real.rpow_add hkpos]
      congr 1
      ring
    have hC0 : 0 ≤ C := by linarith
    calc Y k A' ≤ C * (k : ℝ) ^ (-a) * density (blockScale * k) A' ^ densityExponent := hb
      _ = C * (k : ℝ) ^ (a' - a) *
          ((k : ℝ) ^ (-a') * density (blockScale * k) A' ^ densityExponent) := by
        rw [hsplit]
        ring
      _ ≤ C * (L : ℝ) ^ (a' - a) *
          ((k : ℝ) ^ (-a') * density (blockScale * k) A' ^ densityExponent) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkL' hC0) hw
      _ = C * (L : ℝ) ^ (a' - a) * (k : ℝ) ^ (-a') *
          density (blockScale * k) A' ^ densityExponent := by ring
  · exact hA
  · have hsplit : (L : ℝ) ^ (-a) = (L : ℝ) ^ (a' - a) * (L : ℝ) ^ (-a') := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    have heq : C * (L : ℝ) ^ (a' - a) * (L : ℝ) ^ (-a') *
        density (blockScale * L) A ^ densityExponent =
        C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent := by
      rw [hsplit]
      ring
    change C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent < Y L A at hcounter
    change C * (L : ℝ) ^ (a' - a) * (L : ℝ) ^ (-a') *
      density (blockScale * L) A ^ densityExponent < Y L A
    rw [heq]
    exact hcounter

/-- **The closing estimates are monotone in the price exponent**: estimates at `a'` are
estimates at every `a ≤ a'`, with the same energies, errors and closing data. -/
noncomputable def ClosingEstimates.mono {a a' : ℝ} (haa : a ≤ a') {Y : ℕ → Finset ℤ → ℝ}
    {k : ℕ} {L₀ J W H : ℝ} (e : ClosingEstimates (Params.ofDecay a') Y k L₀ J W H) :
    ClosingEstimates (Params.ofDecay a) Y k L₀ J W H where
  Yfs := e.Yfs
  Yν := e.Yν
  Jν := e.Jν
  eL := e.eL
  eR := e.eR
  VL := e.VL
  VR := e.VR
  εwrap := e.εwrap
  εenv := e.εenv
  εfirst := e.εfirst
  εjoint := e.εjoint
  cwrap := e.cwrap
  cenv := e.cenv
  cfirst := e.cfirst
  cjoint := e.cjoint
  εwrap_tendsto := e.εwrap_tendsto
  εenv_tendsto := e.εenv_tendsto
  εfirst_tendsto := e.εfirst_tendsto
  εjoint_tendsto := e.εjoint_tendsto
  cwrap_nonneg := e.cwrap_nonneg
  cenv_nonneg := e.cenv_nonneg
  cfirst_nonneg := e.cfirst_nonneg
  cjoint_nonneg := e.cjoint_nonneg
  wrap := atCounterexamples_mono haa e.wrap
  frame := atCounterexamples_mono haa e.frame
  envelopeL := atCounterexamples_mono haa e.envelopeL
  envelopeR := atCounterexamples_mono haa e.envelopeR
  firstStage := atCounterexamples_mono haa e.firstStage
  joint := atCounterexamples_mono haa e.joint

/-- The hard-coded closing estimates (record exponent) give the closing estimates at the anchor
`a₀ < a`, with the same closing data. -/
noncomputable def anchor_closingEstimates_of_record {Y : ℕ → Finset ℤ → ℝ} {k : ℕ}
    {L₀ J W H : ℝ} (e : Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H) :
    ClosingEstimates Params.anchor Y k L₀ J W H :=
  ClosingEstimates.mono Params.anchorDecay_lt_decay.le e.toParam

/-- **The hypotheses of the hard-coded endgame give the bound at `ε′`** through the endgame at
`a₀`: the anchor's hypotheses are implied by the record's. (The conclusion also follows from the
record bound itself, since `ε′ < ε`: `sarkozyBound_mono`, `epsAnchor_lt_epsPaper`.) -/
theorem sarkozyBound_epsAnchor_of_record
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H M : ℝ}
    (hθ : jointTheta k L₀ J W H < 1) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : Sarkozy.GlobalMomentBound Y M)
    (e : Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H) :
    Target.SarkozyBound Param.anchorSaving :=
  sarkozyBound_epsAnchor_of_closingEstimates hθ hM hreflection hglobal
    (anchor_closingEstimates_of_record e)

end Sarkozy.Param
