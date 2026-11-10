module

public import Sarkozy.PaperFrame.Reference

@[expose] public section

/-!
# The conditional main theorem for an arbitrary closing number below one

`Sarkozy.Comparison.paperMain_powerSavingBound` concludes the power saving from the five
robust closing estimates at the closing data of the primitive ledger of Part V
(`k = 6`, `H = l.jointConstant`, `PrimitiveLedger.Bounds`). Theorem C (`thm:comparison`,
`paper/sections/09_comparison_theorem.tex`) is stated for any comparison data whose closing
number is below one; its proof (`paper/sections/11_comparison_proof.tex`) is the closing
inequality `thm:record:criterion` (in the joint form `cor:joint-closing`) followed by the
linear-density induction `thm:record:lineardensity` of Part II.

This file restates the conditional main theorem with the ledger replaced by the single
hypothesis `jointTheta k L₀ J W H < 1`, for any number `k` of queries:

* `prefixedResidueModel_powerSavingBound_theta`: for a prefixed residue model with the
  structural properties of `PrefixedResidueModel.powerSavingBound_of_closingEstimates`;
* `paperMain_powerSavingBound_theta`: for the paper's functional
  `prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)`, with the hypotheses on the reference
  law of `paperMain_powerSavingBound`;
* `paperMain_powerSavingBound_theta_ref`: the same with the functional written as the frame
  energy `energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p)` of the reference laws over the
  atoms (`Sarkozy.PaperFrame.energyFirst_refLaws`), which is the form produced by the
  closing estimates with concrete energies.

The proofs are those of `paperMain_powerSavingBound` and
`PrefixedResidueModel.powerSavingBound_of_closingEstimates`, with
`Sarkozy.Comparison.powerSavingBound_of_closingEstimates` (general closing number) in place
of `powerSavingBound_of_closingEstimates_primitive` (the ledger).
-/

open Filter Finset
open scoped Topology

namespace Sarkozy.TheoremC

open Sarkozy.Comparison Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame

/-- **Theorem C's conclusion for a prefixed residue model, at any closing number below one.**
The structural hypotheses are those of
`Sarkozy.Comparison.PrefixedResidueModel.powerSavingBound_of_closingEstimates`; the ledger is
replaced by `jointTheta k L₀ Jn W H < 1`. -/
theorem prefixedResidueModel_powerSavingBound_theta
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {X₀ : Type} [AddCommGroup X₀] [Fintype X₀]
    (model : Sarkozy.PrefixedResidueModel p X₀) (ha : model.Arithmetic p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {C : ℝ} (hC : 0 < C)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    {k : ℕ} {L₀ Jn W H : ℝ} (hθ : jointTheta k L₀ Jn W H < 1)
    (e : ClosingEstimates (model.toFourierModel p X₀).energy k L₀ Jn W H) :
    PowerSavingBound := by
  obtain ⟨D, hD, hlift⟩ := model.exists_liftMomentBound p X₀ ha
  have hr := model.regular p X₀ hprefix hzero hm hp
  exact powerSavingBound_of_closingEstimates hθ (mul_pos hC (pow_pos hD 2))
    (fun L hL A _ => (model.toFourierModel p X₀).density_pow_le_energy hr L hL A)
    ((model.toFourierModel p X₀).globalMomentBound_of_mixed hC.le hmixed hlift) e

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The conditional main theorem for the paper's functional, at any closing number below
one** (`thm:comparison`, conclusion). The hypotheses on the reference law
`μ₀ ⊗ ⊗_{p tail} μ_p` are those of `Sarkozy.Comparison.paperMain_powerSavingBound`; the
primitive ledger is replaced by `jointTheta k L₀ Jn W H < 1`, for `k` queries. -/
theorem paperMain_powerSavingBound_theta (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {k : ℕ} {L₀ Jn W H : ℝ} (hθ : jointTheta k L₀ Jn W H < 1)
    (e : ClosingEstimates (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) k L₀ Jn W H) :
    PowerSavingBound := by
  classical
  obtain ⟨p₀, hp₀unit⟩ := hunit
  set law := paperLaw m₀ p μ₀ μp
  set model := paperPrefixedModel m₀ p law
  -- The estimates for the paper's functional are estimates for the model's energy.
  have e' : ClosingEstimates model.toFourierModel.energy k L₀ Jn W H :=
    e.transfer fun L A hA => (paperPrefixedModel_energy m₀ p hp law L hA.1).symm
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
  exact prefixedResidueModel_powerSavingBound_theta model
    (paperPrefixedModel_arithmetic m₀ p hp hinj law) hprefix hzero hm hrp (by positivity) hmixed
    hθ e'

/-- **The conditional main theorem over one atom set, at any closing number below one.**
`paperMain_powerSavingBound_theta` with the paper's functional written as the frame energy
`energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p)` of the reference laws over the atoms
(`energyFirst_refLaws`): this is the functional of the closing estimates with concrete
energies (`ClosingEstimates.ofConcrete`, `paperMain_powerSavingBound_concrete_ref`). -/
theorem paperMain_powerSavingBound_theta_ref (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {k : ℕ} {L₀ Jn W H : ℝ} (hθ : jointTheta k L₀ Jn W H < 1)
    (e : ClosingEstimates (energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p)
      (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) k L₀ Jn W H) :
    PowerSavingBound :=
  paperMain_powerSavingBound_theta m₀ p hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit hθ
    (e.transfer fun L A _ => energyFirst_refLaws m₀ p μ₀ μp L A)

end Sarkozy.TheoremC
