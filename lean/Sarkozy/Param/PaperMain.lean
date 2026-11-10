module

public import Sarkozy.Param.Primitive
public import Sarkozy.Comparison.PaperMain
public import Sarkozy.Comparison.ConcreteFrame
public import Sarkozy.PaperFrame.Reference

@[expose] public section

/-!
# The conditional main theorem for the paper's functional, for a free price exponent

Parametrized copies of

* `Sarkozy.Comparison.ClosingEstimates.ofConcrete` (`Sarkozy/Comparison/ConcreteFrame.lean`):
  the closing estimates with the concrete energies, the frame estimate `eq:cp:mean-step` being
  proved from the brackets (CP6) (`Sarkozy.Comparison.frame_of_brackets`, reused);
* `Sarkozy.Comparison.paperMain_powerSavingBound` (`Sarkozy/Comparison/PaperMain.lean`): the
  paper's group, lift and reference law `μ₀ ⊗ ⊗_{p tail} μ_p`;
* WP-FI's closing-number forms in `Sarkozy/TheoremC/MainTheta.lean` and
  `Sarkozy/TheoremC/Energy.lean`: `paperMain_powerSavingBound_theta`,
  `paperMain_powerSavingBound_theta_ref`, and the energy forms
  `prefixedFunctional_scaledEnergyEstimate_theta` and `paperMain_scaledEnergyEstimate_theta`
  (the first conclusion `α^{72} ≤ Y ≤ C L^{-a} α^ϑ` of `thm:density:induction`). These are the
  entry points a generalized `Sarkozy.TheoremC` would call.

They are stated at `Params.ofDecay a`, the paper's `(ϑ, K, σ, η)` with a free price exponent
`a`, because the lift, the cutoff and the global moment bound of the paper's model are built at
`K = blockScale` and `η = momentSlack`; none of them involves `a`. The `_theta` forms take
arbitrary closing data `(L₀, J, W, H)` for `k` queries, with the closing number
`jointTheta k L₀ J W H < 1` as the hypothesis; `paperMain_powerSavingBound` takes the primitive
ledger, as the hard-coded theorem does.
-/

open Filter Finset
open scoped Topology

namespace Sarkozy.Param

open Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.IndexSupport Sarkozy.PaperFrame
open Sarkozy.Comparison (jointTheta PrimitiveLedger CoupledIndex energyFirst energyComparison
  energyMean signedIndexForm inclusionEnergyL inclusionEnergyR frame_of_brackets paperLaw
  primeTailLaw_mixed)

section Concrete

variable (P : Params)
  {E : Type} [Fintype E] [DecidableEq E] {Kq : E → Type} [∀ e, Fintype (Kq e)]
  [∀ e, DecidableEq (Kq e)] {Ωc : ∀ e, Kq e → Type} [∀ e j, Fintype (Ωc e j)]
  [∀ e j, DecidableEq (Ωc e j)] [∀ e j, Nonempty (Ωc e j)]
  {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]
  (I : CoupledIndex E Kq Ωc)
  (lam ML ν MR : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
  (φ ψ : ∀ L : ℕ, Finset ℤ → ∀ e, (∀ j, Ωc e j) → (∀ b, Xb L b) → ℝ)
  (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)

/-- **The closing estimates with concrete energies** at the exponents `P`
(`Sarkozy.Comparison.ClosingEstimates.ofConcrete` in general). The frame estimate
(`eq:cp:mean-step`) is proved from the brackets (CP6) and the mean identities
(`lem:twointerval`); the wrap, envelope, first-stage and joint estimates are hypotheses. -/
noncomputable def ClosingEstimates.ofConcrete {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (hφ : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => φ L A e η y) = F L A y)
    (hψ : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => ψ L A e η y) = F L A y)
    (εwrap εenv εfirst εjoint : ℕ → ℝ) (cwrap cenv cfirst cjoint : ℝ)
    (hεwrap : Tendsto εwrap atTop (𝓝 0)) (hεenv : Tendsto εenv atTop (𝓝 0))
    (hεfirst : Tendsto εfirst atTop (𝓝 0)) (hεjoint : Tendsto εjoint atTop (𝓝 0))
    (hcwrap : 0 ≤ cwrap) (hcenv : 0 ≤ cenv) (hcfirst : 0 ≤ cfirst) (hcjoint : 0 ≤ cjoint)
    (wrap : AtCounterexamples P Y fun L A =>
      2 ^ k * energyComparison ν F L A ≤ signedIndexForm I ν φ ψ F L A +
        (2 ^ k * W + εwrap L) * Y L A + remainder P cwrap L A)
    (envelopeL : AtCounterexamples P Y fun L A =>
      inclusionEnergyL I ML φ F L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder P cenv L A)
    (envelopeR : AtCounterexamples P Y fun L A =>
      inclusionEnergyR I MR ψ F L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder P cenv L A)
    (firstStage : AtCounterexamples P Y fun L A =>
      (1 - L₀ - εfirst L) * Y L A - remainder P cfirst L A ≤ energyFirst lam F L A)
    (joint : AtCounterexamples P Y fun L A =>
      (2 ^ k - 1) * (energyFirst lam F L A - energyComparison ν F L A) -
          (energyMean F ML L A + energyMean F MR L A) / 2 ≤
        (2 ^ k * H - 1 + εjoint L) * Y L A + remainder P cjoint L A) :
    ClosingEstimates P Y k L₀ J W H where
  Yfs := energyFirst lam F
  Yν := energyComparison ν F
  Jν := signedIndexForm I ν φ ψ F
  eL := energyMean F ML
  eR := energyMean F MR
  VL := inclusionEnergyL I ML φ F
  VR := inclusionEnergyR I MR ψ F
  εwrap := εwrap
  εenv := εenv
  εfirst := εfirst
  εjoint := εjoint
  cwrap := cwrap
  cenv := cenv
  cfirst := cfirst
  cjoint := cjoint
  εwrap_tendsto := hεwrap
  εenv_tendsto := hεenv
  εfirst_tendsto := hεfirst
  εjoint_tendsto := hεjoint
  cwrap_nonneg := hcwrap
  cenv_nonneg := hcenv
  cfirst_nonneg := hcfirst
  cjoint_nonneg := hcjoint
  wrap := wrap
  frame := AtCounterexamples.of_forall P fun L A =>
    frame_of_brackets I ML ν MR φ ψ F hbr hφ hψ L A
  envelopeL := envelopeL
  envelopeR := envelopeR
  firstStage := firstStage
  joint := joint

end Concrete

section PaperMain

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The energy form for the paper's functional, free price exponent, any closing number
below one**: `α^{72} ≤ Y(L, A) ≤ C L^{-a} α^ϑ` for the paper's functional `Y`
(`thm:density:induction`, first conclusion). For the paper's group, lift and reference law
`μ₀ ⊗ ⊗_{p tail} μ_p`, the hypotheses on the laws (uniform marginals, reflection positivity at
the seven sorting cuts, eventual unit mixed `L³⁶` norm of the prime laws), the closing number
`jointTheta k L₀ Jn W H < 1` and the five robust closing estimates at the exponents
`Params.ofDecay a` suffice. The lift-moment estimate, the global moment bound and the
reflection lower bound are proved, as in the hard-coded theorems. -/
theorem prefixedFunctional_scaledEnergyEstimate_theta {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {k : ℕ} {L₀ Jn W H : ℝ} (hθ : jointTheta k L₀ Jn W H < 1)
    (e : ClosingEstimates (Params.ofDecay a) (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) k
      L₀ Jn W H) :
    ScaledEnergyEstimate (Params.ofDecay a) (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) := by
  classical
  obtain ⟨p₀, hp₀unit⟩ := hunit
  set law := paperLaw m₀ p μ₀ μp
  set model := paperPrefixedModel m₀ p law
  -- The estimates for the paper's functional are estimates for the model's energy.
  have hY : ∀ L A, Admissible ((Params.ofDecay a).blockScale * L) A →
      prefixedFunctional m₀ p law L A = model.toFourierModel.energy L A :=
    fun L A hA => (paperPrefixedModel_energy m₀ p hp law L hA.1).symm
  have e' : ClosingEstimates (Params.ofDecay a) model.toFourierModel.energy k L₀ Jn W H :=
    e.transfer hY
  set Ct : ℝ := ((p₀ : ℝ) ^ 2) ^ p₀
  set C₀ : ℝ := (Fintype.card (ResidueSpace m₀) : ℝ) ^ ((Fintype.card Slot : ℝ) / 36)
  have hC₀ : 0 ≤ C₀ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCt : 0 ≤ Ct := pow_nonneg (sq_nonneg _) _
  have hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 (1 + C₀ * Ct) := by
    intro L _
    have h := (mixedLpBound_finite_alphabet μ₀ (p := 36) (by norm_num)).slotProduct
      (primeTailLaw_mixed p hinj μp p₀ hp₀unit hp L) hCt (by norm_num)
    exact h.mono_constant (by linarith)
  have hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L) := by
    intro L _
    exact hm₀.slotProduct (tensor_uniform_marginals _ fun j => hmp _ (hp L j))
  have hrp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight) := by
    intro L _
    exact slotReflectionPositive_slotProduct hp₀ (tensor_slot_reflection_positive _ fun j =>
      hpp _ (hp L j))
  have hprefix : (1 : AddChar (ResidueSpace m₀) ℂ) ∈ model.prefixSet :=
    mem_image.mpr ⟨0, mem_univ _, productCharacter_zero m₀⟩
  have hzero : ∀ L : ℕ, 1 ≤ L → (∅ : Finset (J L)) ∈ model.supports L 1 := by
    intro L hL
    have hN : 1 ≤ blockScale * L :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by norm_num [blockScale]) (by omega))
    simp only [model, paperPrefixedModel, tailSupports, mem_filter, mem_univ, true_and,
      prod_empty, mul_one]
    have h1 : prefixLabel m₀ 1 = 0 := by
      rw [← productCharacter_zero m₀, prefixLabel_productCharacter]
    rw [h1, conductor_zero, Nat.cast_one]
    exact one_le_paperCutoff hN
  have hS := Sarkozy.Param.PrefixedResidueModel.scaledEnergyEstimate_of_closingEstimates_theta
    hP model (paperPrefixedModel_arithmetic m₀ p hp hinj law) hprefix hzero hm hrp
    (by positivity) hmixed hθ e'
  exact ScaledEnergyEstimate.transfer (fun L A hA => (hY L A hA).symm) hS

/-- **The conditional main theorem for the paper's functional, free price exponent, any
closing number below one** (`Sarkozy.TheoremC.paperMain_powerSavingBound_theta` and
`Sarkozy.Comparison.paperMain_powerSavingBound` at `Params.ofDecay a`): the hypotheses of
`prefixedFunctional_scaledEnergyEstimate_theta` give `s(N) ≤ C N^{1 − a/(72 − ϑ)}`. -/
theorem paperMain_powerSavingBound_theta {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {k : ℕ} {L₀ Jn W H : ℝ} (hθ : jointTheta k L₀ Jn W H < 1)
    (e : ClosingEstimates (Params.ofDecay a) (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) k
      L₀ Jn W H) :
    PowerSavingBound (Params.ofDecay a) :=
  powerSavingBound_of_scaledEnergyEstimate hP
    (prefixedFunctional_scaledEnergyEstimate_theta m₀ p hP hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit
      hθ e)

/-- The energy form with the paper's functional written as the frame energy
`energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p)` of the reference laws over the atoms
(`Sarkozy.TheoremC.paperMain_scaledEnergyEstimate_theta` at `Params.ofDecay a`). -/
theorem paperMain_scaledEnergyEstimate_theta {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {k : ℕ} {L₀ Jn W H : ℝ} (hθ : jointTheta k L₀ Jn W H < 1)
    (e : ClosingEstimates (Params.ofDecay a) (energyFirst (Atom := PaperAtom J)
      (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) k L₀ Jn W H) :
    ScaledEnergyEstimate (Params.ofDecay a) (energyFirst (Atom := PaperAtom J)
      (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) :=
  ScaledEnergyEstimate.transfer (fun L A _ => (energyFirst_refLaws m₀ p μ₀ μp L A).symm)
    (prefixedFunctional_scaledEnergyEstimate_theta m₀ p hP hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit
      hθ (e.transfer fun L A _ => energyFirst_refLaws m₀ p μ₀ μp L A))

/-- The conditional main theorem over one atom set, free price exponent, any closing number
below one (`Sarkozy.TheoremC.paperMain_powerSavingBound_theta_ref` at `Params.ofDecay a`). -/
theorem paperMain_powerSavingBound_theta_ref {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {k : ℕ} {L₀ Jn W H : ℝ} (hθ : jointTheta k L₀ Jn W H < 1)
    (e : ClosingEstimates (Params.ofDecay a) (energyFirst (Atom := PaperAtom J)
      (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) k L₀ Jn W H) :
    PowerSavingBound (Params.ofDecay a) :=
  paperMain_powerSavingBound_theta m₀ p hP hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit hθ
    (e.transfer fun L A _ => energyFirst_refLaws m₀ p μ₀ μp L A)

/-- The conditional main theorem for the paper's functional with the primitive ledger, free
price exponent (`Sarkozy.Comparison.paperMain_powerSavingBound` in general). -/
theorem paperMain_powerSavingBound {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {l : PrimitiveLedger} (hledger : l.Bounds)
    (e : ClosingEstimates (Params.ofDecay a) (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) 6
      l.L₀ l.J l.W l.jointConstant) :
    PowerSavingBound (Params.ofDecay a) :=
  paperMain_powerSavingBound_theta m₀ p hP hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit
    (l.jointTheta_lt_one hledger) e

end PaperMain

end Sarkozy.Param
