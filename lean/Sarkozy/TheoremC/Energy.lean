module

public import Sarkozy.TheoremC.Main

@[expose] public section

/-!
# Theorem C, first conclusion: `𝒴(L, A) ≤ C L^{-a} α^θ`

`thm:comparison` concludes first that there is a constant `C`, depending only on the
comparison data, with `𝒴(L, A) ≤ C L^{-a} α^θ` for every `L ≥ 1` and every
square-difference-free `A ⊆ [KL]`, and then `s(N) ≤ C' N^{1 − a/(d − θ)}`. `theoremC`
(`Sarkozy.TheoremC.Main`) gives the second; here is the first, as the project's
`ScaledEnergyEstimate` (which also records the reflection lower bound `α^{72} ≤ 𝒴`).

The proof is that of `paperMain_powerSavingBound_theta` (`MainTheta.lean`), stopped at
`scaledEnergyEstimate_of_rawComparison`, before `powerSavingBound_of_scaledEnergyEstimate`.
-/

open Filter Finset Function
open scoped Topology

namespace Sarkozy.TheoremC

open Sarkozy.Comparison Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame

/-- `ScaledEnergyEstimate` only sees the functional at `L ≥ 1` on admissible sets. -/
theorem ScaledEnergyEstimate.transfer {Y Y' : ℕ → Finset ℤ → ℝ}
    (h : ∀ L A, Admissible (blockScale * L) A → Y L A = Y' L A) (hY : ScaledEnergyEstimate Y) :
    ScaledEnergyEstimate Y' := by
  obtain ⟨C, hC, hb⟩ := hY
  refine ⟨C, hC, fun L hL A hA => ?_⟩
  rw [← h L A hA]
  exact hb L hL A hA

/-- The energy estimate for a prefixed residue model at any closing number below one. -/
theorem prefixedResidueModel_scaledEnergyEstimate_theta
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
    ScaledEnergyEstimate (model.toFourierModel p X₀).energy := by
  obtain ⟨D, hD, hlift⟩ := model.exists_liftMomentBound p X₀ ha
  have hr := model.regular p X₀ hprefix hzero hm hp
  exact scaledEnergyEstimate_of_rawComparison (mul_pos hC (pow_pos hD 2))
    e.remainderConstant_nonneg hθ
    (fun L hL A _ => (model.toFourierModel p X₀).density_pow_le_energy hr L hL A)
    ((model.toFourierModel p X₀).globalMomentBound_of_mixed hC.le hmixed hlift)
    e.rawComparison e.coefficient_tendsto

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The energy estimate for the paper's functional at any closing number below one.** -/
theorem paperMain_scaledEnergyEstimate_theta (hp : ∀ L j, (p L j).Prime)
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
    ScaledEnergyEstimate (energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p)
      (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) := by
  classical
  obtain ⟨p₀, hp₀unit⟩ := hunit
  set law := paperLaw m₀ p μ₀ μp
  set model := paperPrefixedModel m₀ p law
  have hY : ∀ L A, Admissible (blockScale * L) A →
      energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p) L A = model.toFourierModel.energy L A := fun L A hA =>
    (energyFirst_refLaws m₀ p μ₀ μp L A).trans
      (paperPrefixedModel_energy m₀ p hp law L hA.1).symm
  have e' : ClosingEstimates model.toFourierModel.energy k L₀ Jn W H := e.transfer hY
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
  have hS := prefixedResidueModel_scaledEnergyEstimate_theta model
    (paperPrefixedModel_arithmetic m₀ p hp hinj law) hprefix hzero hm hrp (by positivity) hmixed
    hθ e'
  exact ScaledEnergyEstimate.transfer (fun L A hA => (hY L A hA).symm) hS

namespace ComparisonData

variable {m₀ p} {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ}
  [∀ q, NeZero (pr q ^ h q)] {E : Type} [Fintype E] [DecidableEq E]
  (D : ComparisonData m₀ p pr h E) (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Theorem C, first conclusion**: under the hypotheses of `theoremC`, there is a constant
`C` with `α^{72} ≤ 𝒴(L, A) ≤ C L^{-a} α^θ` for every `L ≥ 1` and every
square-difference-free `A ⊆ [KL]`. -/
theorem theoremC_energy {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    ScaledEnergyEstimate D.Y := by
  obtain ⟨e⟩ := D.closingEstimates hcop h𝓔 hE1 hSF hcan hwr henv
  exact paperMain_scaledEnergyEstimate_theta m₀ p D.S.p_prime D.S.p_inj D.R.μ₀ D.R.μp
    D.R.unif₀ D.R.rp₀.slot D.R.unifp (fun q _ hq => (D.R.rpp q hq).slot) hunit
    (by rw [D.jointTheta_eq_Theta]; exact hΘ) e

end ComparisonData

end Sarkozy.TheoremC
