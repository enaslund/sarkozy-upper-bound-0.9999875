module

public import Sarkozy.EnvelopeInputs.EnvelopeE1Mixed
public import Sarkozy.Moments.Product
public import Sarkozy.Moments.CliqueCopies

/-!
# The density moment of the whole-group weight from that of the selected weight

The input `hdmom` of `abs_envelope_energy_le_unchanged_mixed` is stated for the whole-group
weight `ρ_F = ρ ⊗ Unif(X_𝒮)` (`liftWeight E ρ (uniformRest E)`), with `ρ` the selected
weight `⊗_{supp ω} D`. Lifting by the uniform rest preserves unit mixed bounds at `p ≥ 1`:

* `expect_variationLaw_liftWeight`: the variation law of `ρ ⊗ κ` is the image of
  `(|ρ|/‖ρ‖) ⊗_slot κ` under joining the labels;
* `mixedLpBound_liftWeight_uniform`: unit mixed `L^p` of `|ρ|/‖ρ‖` gives unit mixed `L^p` of
  `|ρ_F|/‖ρ_F‖`, by `MixedLpBound.slotProduct` with the uniform rest
  (`mixedLpBound_independent`, raised to `p`) and `MixedLpBound.map_equiv`;
* `mixedLpBound_selectedWeight`: unit mixed `L^p` of every selected factor `|ν_b|/‖ν_b‖` gives
  unit mixed `L^p` of the selected product (`MixedLpBound.tensor`);
* `abs_envelope_energy_le_unchanged_selected`, `abs_envelope_energy_le_unchanged_atoms`,
  `abs_envelope_energy_le_unchanged_two_scales_atoms`: (E1), first bound, at `θ = ϑ`, for the
  envelopes with outside law `μ`, with the Part V input stated for the selected weight, or for
  each selected factor (the last with WP-FI's two-scale restoration).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic

section Lift

variable {J : Type*} [Fintype J] [DecidableEq J] {Xa : J → Type*} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- **The variation law of a lifted weight** is the image of `(|ρ|/‖ρ‖) ⊗_slot κ` under
joining the selected and the remaining labels. -/
theorem expect_variationLaw_liftWeight (E : Finset J)
    (ρ : (Slot → ∀ b : {b // b ∈ E}, Xa b) → ℝ) (κ : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (h : 0 < totalVariation ρ) (h' : 0 < totalVariation (liftWeight E ρ κ))
    (F : (Slot → ∀ b, Xa b) → ℝ) :
    (variationLaw (liftWeight E ρ κ) h').expect F =
      ((variationLaw ρ h).slotProduct κ).expect
        (fun zw => F (fun v => (splitPoint E).symm (zw v))) := by
  rw [FiniteLaw.expect_slotProduct]
  unfold FiniteLaw.expect
  simp only [variationLaw]
  rw [sum_splitSlots E, totalVariation_liftWeight]
  apply sum_congr rfl
  intro z _
  rw [mul_sum]
  apply sum_congr rfl
  intro w _
  simp only [liftWeight, sel_join, rest_join, abs_mul, abs_of_nonneg (κ.nonneg _)]
  change _ = _ * (_ * F (fun v => joinLabels E (z v) (w v)))
  ring

variable [∀ b, Nonempty (Xa b)]

/-- **Lifting by the uniform rest preserves unit mixed bounds** (`p ≥ 1`): if `|ρ|/‖ρ‖` has unit
mixed `L^p`, so does `|ρ ⊗ Unif(X_𝒮)|/‖ρ ⊗ Unif(X_𝒮)‖`. -/
theorem mixedLpBound_liftWeight_uniform (E : Finset J)
    (ρ : (Slot → ∀ b : {b // b ∈ E}, Xa b) → ℝ) (h : 0 < totalVariation ρ) {p : ℝ}
    (hp : 1 ≤ p) (hρ : MixedLpBound (variationLaw ρ h) p 1)
    (h' : 0 < totalVariation (liftWeight E ρ (uniformRest (Xa := Xa) E))) :
    MixedLpBound (variationLaw (liftWeight E ρ (uniformRest (Xa := Xa) E)) h') p 1 := by
  have hU : MixedLpBound (uniformRest (Xa := Xa) E) p 1 :=
    (mixedLpBound_independent).mono_exponent zero_le_one zero_lt_one hp
  have hprod := (hρ.slotProduct hU zero_le_one (by linarith : (0 : ℝ) < p).ne').map_equiv
    (splitPoint E).symm
  rw [one_mul] at hprod
  intro f
  rw [expect_variationLaw_liftWeight E ρ _ h h']
  have hf := hprod f
  rw [FiniteLaw.expect_map] at hf
  exact hf

omit [Fintype J] in
/-- **The density moment of a selected product from those of its atoms**: if every selected
atom's variation law `|ν_b|/‖ν_b‖` has unit mixed `L^p`, so has the variation law of
`⊗_{b ∈ E} ν_b` (`MixedLpBound.tensor`). -/
theorem mixedLpBound_selectedWeight (E : Finset J) (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    {p : ℝ} (hp : 0 < p)
    (hν : ∀ (b : {b // b ∈ E}) (hb : 0 < totalVariation (lawDensity (ν b))),
      MixedLpBound (variationLaw _ hb) p 1)
    (h : 0 < totalVariation (selectedWeight E ν)) :
    MixedLpBound (variationLaw (selectedWeight E ν) h) p 1 := by
  have hb : ∀ b : {b // b ∈ E}, 0 < totalVariation (lawDensity (ν b)) := by
    intro b
    rcases (totalVariation_nonneg (lawDensity (ν b))).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [totalVariation_selectedWeight, Finset.prod_eq_zero (mem_univ b) heq.symm] at h
      exact lt_irrefl _ h
  have hw : ∀ z, (variationLaw (selectedWeight E ν) h).weight z =
      (FiniteLaw.tensor fun b : {b // b ∈ E} => variationLaw _ (hb b)).weight z := by
    intro z
    rw [tensor_weight]
    simp only [variationLaw]
    rw [totalVariation_selectedWeight]
    unfold selectedWeight
    rw [Finset.abs_prod, ← Finset.prod_div_distrib]
    rfl
  have he : ∀ F, (variationLaw (selectedWeight E ν) h).expect F =
      (FiniteLaw.tensor fun b : {b // b ∈ E} => variationLaw _ (hb b)).expect F := by
    intro F
    unfold FiniteLaw.expect
    exact sum_congr rfl fun z _ => by rw [hw z]
  intro f
  rw [he]
  have ht := MixedLpBound.tensor (fun b : {b // b ∈ E} => variationLaw _ (hb b)) hp
    (fun _ => 1) (fun _ => zero_le_one) (fun b => hν b (hb b)) f
  rwa [Finset.prod_const_one] at ht

end Lift

section Envelope

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- `72/θ ≥ 1` when `2θ/72 ≤ 1`. -/
theorem one_le_72_div {θ : ℝ} (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) : 1 ≤ 72 / θ := by
  rw [le_div_iff₀ hθ]
  linarith

/-- **(E1), first bound, at `θ = ϑ`, for an envelope with outside law `μ` and unchanged inputs,
with the Part V input on the selected weight**: `abs_envelope_energy_le_unchanged_mixed` with
`hdmom` obtained from the unit mixed `L^{72/θ}` of `|ρ|/‖ρ‖`, `ρ = ⊗_{supp ω} D`
(`mixedLpBound_liftWeight_uniform`). For `D_{supp ω} ≠ 1`,
`|Y_{(⊗_{supp ω} D) ⊗ μ_{-supp ω}}(F_A)| ≤ ∏_{supp ω} ‖D_b‖ [(1 + u_L) R_E^a Y + C_dc L^{-σ} α]`.
-/
theorem abs_envelope_energy_le_unchanged_selected (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    {T : J → Type*}
    (D : ∀ b, T b → RecordExpansion.ChangeType → ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ)
    (ω : RecordExpansion.Choice T) (E : Finset J) (hE : RecordExpansion.Choice.support ω = E)
    {qE cE : ℕ} (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE) (hcE : IsSquare cE)
    (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau) (hne : ∏ j ∈ E, m j ≠ 1)
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (Q : ℝ) (Q' : Slot → ℝ) {Cdc σ : ℝ}
    (hrest : ∀ (v : Slot) (B : Finset ℤ),
      B ⊆ Icc 1 ((blockScale * stepEll m E 1 (blockScale * L) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child m E (Q' v) B (blockScale * stepEll m E 1 (blockScale * L))) ≤
        Yf (stepEll m E 1 (blockScale * L)) B)
    (hinvT : ∀ (j : ℤ) (F : (Slot → ResidueSpace m) → ℝ),
      (FiniteLaw.tensor μb).expect
          (fun w => F (fun v' => stepMapOff m E (stepR m E 1) 0 j (w v'))) =
        (FiniteLaw.tensor μb).expect F)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (envelopeFactors m μb D ω))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
            (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (envelopeFactors m μb D ω))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (unchangedModel m E A L Q')| ≤
      Cdc * totalVariation (selectedWeight E (envelopeFactors m μb D ω)) * (L : ℝ) ^ (-σ) *
        density (blockScale * L) A)
    (hselmix : ∀ hρ : 0 < totalVariation (selectedWeight E (envelopeFactors m μb D ω)),
      MixedLpBound (variationLaw _ hρ) (72 / θ) 1) :
    |diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight) D ω)
        (unchangedInput m Q A L)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
          |lawDensity (envelopeFactors m μb D ω b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * ((stepR m E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  abs_envelope_energy_le_unchanged_mixed m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb hμb D ω E
    hE hDE hqE hcE hcE0 hcQ hcopE hqN hne P Q Q' hrest hinvT hdc
    (fun h' => mixedLpBound_liftWeight_uniform E _
      (by rwa [totalVariation_liftWeight] at h') (one_le_72_div hθ hθ2) (hselmix _) h')

/-- **(E1), first bound, at `θ = ϑ`, for an envelope with outside law `μ` and unchanged inputs,
with the Part V input per selected atom**: `abs_envelope_energy_le_unchanged_selected` with the
unit mixed `L^{72/θ}` of the selected weight obtained from that of each selected factor
`|D_b|/‖D_b‖` (`mixedLpBound_selectedWeight`). -/
theorem abs_envelope_energy_le_unchanged_atoms (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    {T : J → Type*}
    (D : ∀ b, T b → RecordExpansion.ChangeType → ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ)
    (ω : RecordExpansion.Choice T) (E : Finset J) (hE : RecordExpansion.Choice.support ω = E)
    {qE cE : ℕ} (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE) (hcE : IsSquare cE)
    (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau) (hne : ∏ j ∈ E, m j ≠ 1)
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (Q : ℝ) (Q' : Slot → ℝ) {Cdc σ : ℝ}
    (hrest : ∀ (v : Slot) (B : Finset ℤ),
      B ⊆ Icc 1 ((blockScale * stepEll m E 1 (blockScale * L) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child m E (Q' v) B (blockScale * stepEll m E 1 (blockScale * L))) ≤
        Yf (stepEll m E 1 (blockScale * L)) B)
    (hinvT : ∀ (j : ℤ) (F : (Slot → ResidueSpace m) → ℝ),
      (FiniteLaw.tensor μb).expect
          (fun w => F (fun v' => stepMapOff m E (stepR m E 1) 0 j (w v'))) =
        (FiniteLaw.tensor μb).expect F)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (envelopeFactors m μb D ω))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
            (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (envelopeFactors m μb D ω))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (unchangedModel m E A L Q')| ≤
      Cdc * totalVariation (selectedWeight E (envelopeFactors m μb D ω)) * (L : ℝ) ^ (-σ) *
        density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ E})
      (hb : 0 < totalVariation (lawDensity (envelopeFactors m μb D ω b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight) D ω)
        (unchangedInput m Q A L)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
          |lawDensity (envelopeFactors m μb D ω b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * ((stepR m E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  abs_envelope_energy_le_unchanged_selected m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb hμb D ω E
    hE hDE hqE hcE hcE0 hcQ hcopE hqN hne P Q Q' hrest hinvT hdc
    (fun h => mixedLpBound_selectedWeight E _ (by linarith [one_le_72_div hθ hθ2]) hatom h)

end Envelope

section TwoScales

variable {J₀ J' : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J'] [DecidableEq J']
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J' → ℕ) [∀ j, NeZero (p j)]

/-- **(E1), first bound, at `θ = ϑ`, for unchanged inputs, with restoration from two scales and
the Part V input per selected atom**: `abs_envelope_energy_le_unchanged_two_scales_mixed` with
`hdmom` from `mixedLpBound_selectedWeight` and `mixedLpBound_liftWeight_uniform`. -/
theorem abs_envelope_energy_le_unchanged_two_scales_atoms
    (hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (joinModuli m₀ p b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    {T : J₀ ⊕ J' → Type*}
    (D : ∀ b, T b → RecordExpansion.ChangeType →
      ((Slot → ZMod (joinModuli m₀ p b)) → ℝ) →ₗ[ℝ] ℝ)
    (ω : RecordExpansion.Choice T) (E : Finset (J₀ ⊕ J'))
    (hE : RecordExpansion.Choice.support ω = E)
    {qE cE : ℕ} (hDE : ∏ j ∈ E, joinModuli m₀ p j = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (hne : ∏ j ∈ E, joinModuli m₀ p j ≠ 1)
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (Q Q' : ℝ) {Cdc σ : ℝ}
    (μn : FiniteLaw (Slot → ResidueSpace m₀)) (ν : FiniteLaw (Slot → ResidueSpace p))
    (hprod : ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ,
      (FiniteLaw.tensor μb).expect F =
        (μn.product ν).expect (fun w => F (fun v => (splitEquiv m₀ p).symm (w.1 v, w.2 v))))
    (hinv : ∀ s : ResidueSpace (joinModuli m₀ p), (∀ k ∉ E, s k = 0) →
      ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ,
        (FiniteLaw.tensor μb).expect (fun z => F (fun v => z v + s)) =
          (FiniteLaw.tensor μb).expect F)
    (hlarge : ∀ k (x : ZMod (p k)), x ≠ 0 → Q' < addOrderOf x)
    (hY : ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ p) E 1 (blockScale * L) : ℕ) : ℤ) →
      referenceEnergy μn (fun x => (wholeLift m₀ Q'
          (blockScale * stepEll (joinModuli m₀ p) E 1 (blockScale * L)) B x).re) ≤
        Yf (stepEll (joinModuli m₀ p) E 1 (blockScale * L)) B)
    (hinvT : ∀ (j : ℤ) (F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ),
      (FiniteLaw.tensor μb).expect (fun w => F (fun v' =>
          stepMapOff (joinModuli m₀ p) E (stepR (joinModuli m₀ p) E 1) 0 j (w v'))) =
        (FiniteLaw.tensor μb).expect F)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (envelopeFactors (joinModuli m₀ p) μb D ω))
            (uniformRest (Xa := fun b => ZMod (joinModuli m₀ p b)) E))
          (paperInputs (joinModuli m₀ p) E Q A (fun _ => 1) (fun _ => blockScale * L)
            (fun _ _ => 0) (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (envelopeFactors (joinModuli m₀ p) μb D ω))
            (uniformRest (Xa := fun b => ZMod (joinModuli m₀ p b)) E))
          (unchangedModel (joinModuli m₀ p) E A L (fun _ => Q'))| ≤
      Cdc * totalVariation (selectedWeight E (envelopeFactors (joinModuli m₀ p) μb D ω)) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ E})
      (hb : 0 < totalVariation (lawDensity (envelopeFactors (joinModuli m₀ p) μb D ω b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight) D ω)
        (unchangedInput (joinModuli m₀ p) Q A L)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (joinModuli m₀ p b),
          |lawDensity (envelopeFactors (joinModuli m₀ p) μb D ω b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
            ((stepR (joinModuli m₀ p) E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  abs_envelope_energy_le_unchanged_two_scales_mixed m₀ p hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    μb hμb D ω E hE hDE hqE hcE hcE0 hcQ hcopE hqN hne P Q Q' μn ν hprod hinv hlarge hY hinvT hdc
    (fun h' => mixedLpBound_liftWeight_uniform E _ (by rwa [totalVariation_liftWeight] at h')
      (one_le_72_div hθ hθ2)
      (mixedLpBound_selectedWeight E _ (by linarith [one_le_72_div hθ hθ2]) hatom _) h')

end TwoScales

end Sarkozy.EnvelopeInputs
