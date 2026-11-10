module

public import Sarkozy.Structured.EnvelopeE1
public import Sarkozy.EnvelopeInputs.MixedChain

/-!
# (E1), first bound, at `θ = ϑ`, for the envelopes with outside law `μ`

WP-R's `Structured/EnvelopeE1.lean` proves (E1), first bound (`lem:bracket-energy` for unchanged
inputs, i.e. `prop:record:density-structured`, `paper/sections/10_comparison_lemmas.tex`), for the
envelope law of a choice `ω` with outside law `μ`, under `θ ≤ 1`. Its last step is
`density_structured_scale`. This file re-runs the two theorems, **with WP-R's proofs unchanged
except for that step**, on `density_structured_scale_mixed` (`EnvelopeInputs.MixedChain`). So:

* `θ ≤ 1` becomes `2θ/72 ≤ 1`, which holds at `ϑ = densityExponent`;
* the new input is `hdmom`: the variation law of the whole-group weight
  `ρ_F = (⊗_{supp ω} D) ⊗ Unif(X_𝒮)` has unit mixed `L^{72/θ}` (density endpoint `θ`, Part V);
* the per-index means hold because the unchanged inputs do not depend on the index
  (`meanBound_of_const`).

The selected set `supp ω` has `D_E ≠ 1`, so every slot is changed and the two-occurrence structure
of WP-R's `_theta` layers is absent; `hdmom` is what replaces it.

Condition (b) for the selected product (`hunifS` of WP-R's theorems) is **not** an input here: the
final step uses only the density moment and the fibre means. It remains an input of WP-R's proof
of the density-dc comparison `hdc` (`density_dc_lift_moments`), which is a hypothesis here.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- **The per-index means for inputs that do not depend on the index**: `MeanBound` holds with
equality. -/
theorem meanBound_of_const {Ω : Type*} [Fintype Ω] (E : Finset J) (A : Finset ℤ)
    (P : FiniteLaw Ω) (D0 M : Slot → ℕ) (c0 : Slot → ℤ) (s0 : ∀ v, ZMod (D0 v))
    (changed : Slot → Prop) :
    MeanBound m E A P D0 M (fun _ => c0) (fun _ => s0) changed := by
  intro ω v _
  rw [uniform_fibreDensity]
  simp only [paperMeanDensity, FiniteLaw.expect_const, le_refl]

/-- **(E1), first bound, at `θ = ϑ`, for an envelope with outside law `μ` and unchanged inputs**
(WP-R's `abs_envelope_energy_le_unchanged` with `θ ≤ 1` replaced by `2θ/72 ≤ 1` and the density
moment `hdmom` of the whole-group weight `ρ_F = (⊗_{supp ω} D) ⊗ Unif(X_𝒮)`): for a
choice `ω` with `D_{supp ω} ≠ 1`,
`|Y_{(⊗_{supp ω} D) ⊗ μ_{-supp ω}}(F_A)| ≤ ∏_{supp ω} ‖D_b‖ [(1 + u_L) R_E^a Y + C_dc L^{-σ} α]`,
with `R_E = sq(D_E)`. -/
theorem abs_envelope_energy_le_unchanged_mixed (hpair : Pairwise fun i j => (m i).Coprime (m j))
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
    (hdmom : ∀ hρ : 0 < totalVariation (liftWeight (Xa := fun b => ZMod (m b)) E
        (selectedWeight E (envelopeFactors m μb D ω)) (uniformRest (Xa := fun b => ZMod (m b)) E)),
      MixedLpBound (variationLaw _ hρ) (72 / θ) 1) :
    |diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight) D ω)
        (unchangedInput m Q A L)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
          |lawDensity (envelopeFactors m μb D ω b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * ((stepR m E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hKL : ((blockScale * L : ℕ) : ℝ) ≠ 0 := by
    have : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
    exact_mod_cast this.ne'
  -- 1. the bridge
  have h1 : diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight)
      D ω) (unchangedInput m Q A L) =
      structuredEnergy (FiniteLaw.tensor fun b : {b // b ∉ E} => μb b) P
        (selectedWeight E (envelopeFactors m μb D ω))
        (fun _ _ z x => unchangedInput m Q A L (joinLabels E z x)) := by
    apply diagonalIntegral_tensorLaw_eq_structuredEnergy
    intro w
    rw [tensor_weight]
    apply prod_congr rfl
    intro b _
    have hb : ω b = none := by
      have h : (b : J) ∉ RecordExpansion.Choice.support ω := by
        rw [hE]
        exact b.2
      unfold RecordExpansion.Choice.support at h
      rw [mem_filter] at h
      simpa using h
    rw [hb]
    exact (lawDensity_signedIntegral_eq _ _).symm
  -- 2. the change of representation
  have hinputs : paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
      (fun (_ : Ω) _ => (0 : ZMod 1)) =
      fun _ _ x y => unchangedInput m Q A L (freezeLabels E x y) := by
    funext ω' v x y
    simp only [paperInputs, unchangedInput, zero_add]
    rfl
  have h2 := structuredEnergy_liftWeight E (FiniteLaw.tensor μb)
    (FiniteLaw.tensor fun b : {b // b ∉ E} => μb b)
    (expect_tensor_restrict E μb) P (selectedWeight E (envelopeFactors m μb D ω))
    (uniformRest (Xa := fun b => ZMod (m b)) E) (fun _ _ => unchangedInput m Q A L)
  have hsame : diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight)
      D ω) (unchangedInput m Q A L) =
      structuredEnergy (FiniteLaw.tensor μb) P
        (liftWeight E (selectedWeight E (envelopeFactors m μb D ω))
          (uniformRest (Xa := fun b => ZMod (m b)) E))
        (paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
          (fun _ _ => 0)) := by
    rw [h1, hinputs]
    exact h2.symm
  -- 3. `prop:record:density-structured` for the whole-group data
  have hTV : totalVariation
      (liftWeight (Xa := fun b => ZMod (m b)) E (selectedWeight E (envelopeFactors m μb D ω))
        (uniformRest (Xa := fun b => ZMod (m b)) E)) =
      totalVariation (selectedWeight E (envelopeFactors m μb D ω)) :=
    totalVariation_liftWeight (Xa := fun b => ZMod (m b)) E _ _
  have hmain := density_structured_scale_mixed m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    (FiniteLaw.tensor μb) (tensor_slot_reflection_positive μb hμb) E hDE hqE hcE hcE0 hcQ hcopE
    hqN P (liftWeight (Xa := fun b => ZMod (m b)) E (selectedWeight E (envelopeFactors m μb D ω))
      (uniformRest (Xa := fun b => ZMod (m b)) E))
    (fun _ => 1) (fun _ => le_rfl) (fun _ => one_dvd _) (fun _ _ => Nat.coprime_one_left _)
    (fun _ => blockScale * L) (fun _ => Or.inl rfl) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => True) (fun _ _ h => hne (by simpa using h.1)) Q Q' (unchangedModel m E A L Q')
    (fun _ _ _ _ => rfl) (fun _ hv => absurd trivial hv) (fun v _ => hrest v)
    (fun _ _ _ j F => hinvT j F) (by rw [hTV]; exact hdc) hdmom
    (meanBound_of_const m E A P _ _ _ _ _)
  -- 4. the prices: `ξ_v = R_E`, `ᾱ_v = α`, `Π_main = R_E^a`
  have hα := hcex.density_pos hθ.ne' hY0
  have hξ : paperPrice m E (fun _ => 1) (fun _ => blockScale * L) L =
      fun _ => ((stepR m E 1 : ℕ) : ℝ) := by
    funext v
    unfold paperPrice
    rw [div_self hKL, one_mul]
  have hᾱ : paperMeanDensity P A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
      (fun (_ : Ω) _ => (0 : ZMod 1)) = fun _ => density (blockScale * L) A := by
    funext v
    unfold paperMeanDensity
    have hfilter : ((A ∩ Icc (0 + 1) (0 + ((blockScale * L : ℕ) : ℤ))).filter
        fun x : ℤ => (x : ZMod 1) = 0) = A := by
      rw [filter_true_of_mem (fun x _ => Subsingleton.elim _ _), zero_add, zero_add]
      exact inter_eq_left.mpr hcex.admissible.1
    simp only [hfilter, FiniteLaw.expect_const]
    unfold density
    push_cast
    ring
  have hPi : mainPrice (paperPrice m E (fun _ => 1) (fun _ => blockScale * L) L)
      (paperMeanDensity P A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
        (fun (_ : Ω) _ => (0 : ZMod 1)))
      (fun _ => True) a θ (density (blockScale * L) A) = ((stepR m E 1 : ℕ) : ℝ) ^ a := by
    rw [hξ, hᾱ]
    exact mainPrice_unchanged_inputs _ a θ _ (Nat.cast_nonneg _) hα
  rw [hsame]
  rw [hTV, hPi, totalVariation_selectedWeight (Xa := fun b => ZMod (m b))] at hmain
  exact hmain

/-! ## Restoration from two scales -/

section TwoScales

variable {J₀ J' : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J'] [DecidableEq J']
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J' → ℕ) [∀ j, NeZero (p j)]

/-- **(E1), first bound, at `θ = ϑ`, for unchanged inputs, with restoration from two scales**
(WP-R's `abs_envelope_energy_le_unchanged_two_scales`, with the density moment `hdmom`). For
unchanged inputs all slots have the same child scale `ℓ = ⌈N/(K R_E)⌉`. So one splitting
`G_N = G_n × X_extra` (`joinModuli m₀ p`) serves every slot, and the restoration
hypothesis of `abs_envelope_energy_le_unchanged` follows from WP-FI's
`referenceEnergy_stepLift_le_scale` (`restoration_of_two_scales`). Its hypotheses are:
* `hprod`: `μ_N = μ_n ⊗ ν`, (R1);
* (R2) for the atom laws;
* `hinv`: (R3) for translations supported on `E`;
* `hlarge`: every nonzero extra coordinate has order `> Q'`;
* `hY`: `Λ_{μ_n}(F_B) ≤ Y(ℓ, B)`, the definition of `Y` at the scale `ℓ`. -/
theorem abs_envelope_energy_le_unchanged_two_scales_mixed
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
    (hdmom : ∀ hρ : 0 < totalVariation (liftWeight (Xa := fun b => ZMod (joinModuli m₀ p b)) E
        (selectedWeight E (envelopeFactors (joinModuli m₀ p) μb D ω))
        (uniformRest (Xa := fun b => ZMod (joinModuli m₀ p b)) E)),
      MixedLpBound (variationLaw _ hρ) (72 / θ) 1) :
    |diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight) D ω)
        (unchangedInput (joinModuli m₀ p) Q A L)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (joinModuli m₀ p b),
          |lawDensity (envelopeFactors (joinModuli m₀ p) μb D ω b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
            ((stepR (joinModuli m₀ p) E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  abs_envelope_energy_le_unchanged_mixed (joinModuli m₀ p) hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    μb hμb D ω E hE hDE hqE hcE hcE0 hcQ hcopE hqN hne P Q (fun _ => Q')
    (fun _ => restoration_of_two_scales m₀ p μn ν (FiniteLaw.tensor μb) hprod
      (tensor_slot_reflection_positive μb hμb) E hinv hlarge Yf _ _ hY)
    hinvT hdc hdmom

end TwoScales

end Sarkozy.EnvelopeInputs
