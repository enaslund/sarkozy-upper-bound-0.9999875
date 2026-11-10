module

public import Sarkozy.Param.Anchor
public import Sarkozy.TargetConclusion
public import Sarkozy.Structured.Counterexample

@[expose] public section

/-!
# Compatibility: the hard-coded endgame is the instance at the record exponents

The parametrized definitions at `Params.paper` (the record `a = 1814179/(2·10⁹)`, with the
paper's `ϑ, K, σ, η`) are the hard-coded ones, by `rfl`; and the hard-coded endgame theorems are
re-proved from the parametrized ones at `Params.paper`. Each theorem `…_viaParam` below has, by
construction (`type_of% @…`), exactly the statement of the hard-coded theorem it names.

The global moment bound and the remainders involve only `(K, σ, η)`, so at every
`Params.ofDecay a`, in particular at the anchor, they are the hard-coded notions
(`globalMomentBound_ofDecay`, `remainder_ofDecay`): the existing proofs of the global moment bound
(`Sarkozy.FourierModel.globalMomentBound_of_mixed`) apply at `a₀` unchanged.
-/

open Filter
open scoped Topology

namespace Sarkozy.Param

open Sarkozy.Comparison (jointTheta PrimitiveLedger)

/-! ## The definitions agree at the record exponents -/

theorem energyUpperBoundAt_paper :
    EnergyUpperBoundAt Params.paper = Sarkozy.EnergyUpperBoundAt := rfl

theorem scaledEnergyEstimate_paper :
    ScaledEnergyEstimate Params.paper = Sarkozy.ScaledEnergyEstimate := rfl

theorem globalMomentBound_paper :
    GlobalMomentBound Params.paper = Sarkozy.GlobalMomentBound := rfl

theorem rawComparison_paper : RawComparison Params.paper = Sarkozy.RawComparison := rfl

theorem atCounterexamples_paper :
    AtCounterexamples Params.paper = Sarkozy.Comparison.AtCounterexamples := rfl

theorem remainder_paper : remainder Params.paper = Sarkozy.Comparison.remainder := rfl

theorem powerSavingBound_paper : PowerSavingBound Params.paper ↔ Sarkozy.PowerSavingBound := by
  unfold PowerSavingBound Sarkozy.PowerSavingBound
  rw [Params.paper_saving]

/-- At the record price exponent the target form is `Target.SarkozyBound Sarkozy.saving`
(since 7 November 2026 at `ϑ = 1`, so `Sarkozy.saving < Target.epsPaper`). -/
theorem paper_saving_eq_saving : Params.paper.saving = Sarkozy.saving :=
  Params.paper_saving

/-- Only the `a`-dependent notions change along `Params.ofDecay`: the global moment bound and
the remainders are the hard-coded ones for every `a`. -/
theorem globalMomentBound_ofDecay (a : ℝ) :
    GlobalMomentBound (Params.ofDecay a) = Sarkozy.GlobalMomentBound := rfl

theorem remainder_ofDecay (a : ℝ) :
    remainder (Params.ofDecay a) = Sarkozy.Comparison.remainder := rfl

/-! ## The closing estimates agree at the record exponents -/

/-- A hard-coded `ClosingEstimates` is a parametrized one at `Params.paper`. -/
noncomputable def _root_.Sarkozy.Comparison.ClosingEstimates.toParam
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (e : Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H) :
    ClosingEstimates Params.paper Y k L₀ J W H where
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
  wrap := e.wrap
  frame := e.frame
  envelopeL := e.envelopeL
  envelopeR := e.envelopeR
  firstStage := e.firstStage
  joint := e.joint

/-- A parametrized `ClosingEstimates` at `Params.paper` is a hard-coded one. -/
noncomputable def ClosingEstimates.toComparison
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (e : ClosingEstimates Params.paper Y k L₀ J W H) :
    Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H where
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
  wrap := e.wrap
  frame := e.frame
  envelopeL := e.envelopeL
  envelopeR := e.envelopeR
  firstStage := e.firstStage
  joint := e.joint

theorem ClosingEstimates.toComparison_toParam {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (e : Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H) : e.toParam.toComparison = e := rfl

theorem ClosingEstimates.toParam_toComparison {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (e : ClosingEstimates Params.paper Y k L₀ J W H) : e.toComparison.toParam = e := rfl

/-- The recurrence coefficients agree. -/
theorem ClosingEstimates.coefficient_toParam {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (e : Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H) :
    e.toParam.coefficient = e.coefficient := rfl

theorem ClosingEstimates.remainderConstant_toParam {Y : ℕ → Finset ℤ → ℝ} {k : ℕ}
    {L₀ J W H : ℝ} (e : Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H) :
    e.toParam.remainderConstant = e.remainderConstant := rfl

/-! ## The hard-coded theorems are the instances at `Params.paper` -/

theorem energyUpperBound_of_contraction_viaParam :
    type_of% @Sarkozy.energyUpperBound_of_contraction := by
  intro Y C q L₀ error hC hinit hrec hmargin
  exact energyUpperBound_of_contraction Params.paper hC hinit hrec hmargin

theorem powerSavingBound_of_scaledEnergyEstimate_viaParam :
    type_of% @Sarkozy.powerSavingBound_of_scaledEnergyEstimate := by
  intro Y hY
  exact powerSavingBound_paper.mp
    (powerSavingBound_of_scaledEnergyEstimate Params.paper_valid hY)

theorem exists_initialization_constant_viaParam :
    type_of% @Sarkozy.exists_initialization_constant := by
  intro Y hzero L₀
  exact exists_initialization_constant Params.paper_valid Y hzero L₀

theorem inverse_density_bound_viaParam : type_of% @Sarkozy.inverse_density_bound := by
  intro δ M L hδ hM hL h
  exact inverse_density_bound Params.paper_valid hδ hM hL h

theorem relative_error_bound_viaParam : type_of% @Sarkozy.relative_error_bound := by
  intro δ M L C E Y hδ hM hL hC hE hcounter hglobal
  exact relative_error_bound Params.paper_valid hδ hM hL hC hE hcounter hglobal

theorem scaledEnergyEstimate_of_rawComparison_viaParam :
    type_of% @Sarkozy.scaledEnergyEstimate_of_rawComparison := by
  intro Y M E θ q hM hE hθ hreflection hglobal hrec hq
  exact scaledEnergyEstimate_of_rawComparison Params.paper_valid hM hE hθ hreflection hglobal
    hrec hq

theorem powerSavingBound_of_rawComparison_viaParam :
    type_of% @Sarkozy.powerSavingBound_of_rawComparison := by
  intro l hledger Y M E q hM hE hreflection hglobal hrec hq
  exact powerSavingBound_paper.mp
    (powerSavingBound_of_rawComparison_ledger Params.paper_valid hledger hM hE hreflection
      hglobal hrec hq)

theorem powerSavingBound_of_jointClosing_viaParam :
    type_of% @Sarkozy.powerSavingBound_of_jointClosing := by
  intro l hledger Y C L₀ error hC hreflection hinit hrec herror
  exact powerSavingBound_paper.mp
    (powerSavingBound_of_jointClosing Params.paper_valid hledger hC hreflection hinit hrec
      herror)

theorem rawComparison_viaParam :
    type_of% @Sarkozy.Comparison.ClosingEstimates.rawComparison := by
  intro Y k L₀ J W H e
  exact e.toParam.rawComparison

/-- **Compatibility of the endgame**: `Sarkozy.Comparison.powerSavingBound_of_closingEstimates`
is `Sarkozy.Param.powerSavingBound_of_closingEstimates` at `Params.paper`. -/
theorem powerSavingBound_of_closingEstimates_viaParam :
    type_of% @Sarkozy.Comparison.powerSavingBound_of_closingEstimates := by
  intro Y k L₀ J W H M hθ hM hreflection hglobal e
  exact powerSavingBound_paper.mp
    (powerSavingBound_of_closingEstimates Params.paper_valid hθ hM hreflection hglobal e.toParam)

theorem powerSavingBound_of_rawComparison_primitive_viaParam :
    type_of% @Sarkozy.Comparison.powerSavingBound_of_rawComparison_primitive := by
  intro l hledger Y M E q hM hE hreflection hglobal hrec hq
  exact powerSavingBound_paper.mp
    (powerSavingBound_of_rawComparison_primitive Params.paper_valid hledger hM hE hreflection
      hglobal hrec hq)

theorem powerSavingBound_of_closingEstimates_primitive_viaParam :
    type_of% @Sarkozy.Comparison.powerSavingBound_of_closingEstimates_primitive := by
  intro Y M l hledger hM hreflection hglobal e
  exact powerSavingBound_paper.mp
    (powerSavingBound_of_closingEstimates_primitive Params.paper_valid hledger hM hreflection
      hglobal e.toParam)

theorem prefixedResidueModel_powerSavingBound_of_closingEstimates_viaParam :
    type_of% @Sarkozy.Comparison.PrefixedResidueModel.powerSavingBound_of_closingEstimates := by
  intro J _ _ p _ X₀ _ _ model ha hprefix hzero hm hp C hC hmixed l hledger e
  exact powerSavingBound_paper.mp
    (PrefixedResidueModel.powerSavingBound_of_closingEstimates Params.paper_valid model ha
      hprefix hzero hm hp hC hmixed hledger e.toParam)

/-! ## WP-R's least normalized counterexamples (`Sarkozy.Structured`)

`Sarkozy.Structured.ScaleBound` and `Sarkozy.Structured.IsLeastCounterexample`
(`def:record:counterexample`) are parametric in `(a, θ)` with `K = blockScale`. Along
`Params.ofDecay a` they are the parametrized notions of this package. -/

theorem scaleBound_iff_energyUpperBoundAt (a : ℝ) (Y : ℕ → Finset ℤ → ℝ) (C : ℝ) (ℓ : ℕ) :
    Structured.ScaleBound Y a densityExponent C ℓ ↔ EnergyUpperBoundAt (Params.ofDecay a) Y C ℓ :=
  Iff.rfl

/-- `AtCounterexamples (ofDecay a)` quantifies exactly over WP-R's least normalized
counterexamples for `(a, ϑ)`, at every sufficiently large scale and uniformly in `C ≥ 1`. -/
theorem atCounterexamples_ofDecay_iff (a : ℝ) (Y : ℕ → Finset ℤ → ℝ)
    (Q : ℕ → Finset ℤ → Prop) :
    AtCounterexamples (Params.ofDecay a) Y Q ↔
      ∀ᶠ L : ℕ in atTop, ∀ C : ℝ, 1 ≤ C → ∀ A : Finset ℤ,
        Structured.IsLeastCounterexample Y a densityExponent C L A → Q L A := by
  unfold AtCounterexamples
  refine eventually_congr (Eventually.of_forall fun L => ?_)
  constructor
  · intro h C hC A hA
    exact h C hC (fun k hk hkL => hA.2.2 k hk hkL) A hA.1 hA.2.1
  · intro h C hC hind A hA hcounter
    exact h C hC A ⟨hA, hcounter, fun k hk hkL => hind k hk hkL⟩

/-- At the record price exponent, the target-form endgame concludes the hard-coded exponent
`Sarkozy.saving` (at `ϑ = 1`). -/
theorem sarkozyBound_saving_of_closingEstimates
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H M : ℝ}
    (hθ : jointTheta k L₀ J W H < 1) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : Sarkozy.GlobalMomentBound Y M)
    (e : Sarkozy.Comparison.ClosingEstimates Y k L₀ J W H) :
    Target.SarkozyBound Sarkozy.saving := by
  rw [← paper_saving_eq_saving]
  exact sarkozyBound_of_closingEstimates Params.paper_valid hθ hM hreflection hglobal e.toParam

end Sarkozy.Param
