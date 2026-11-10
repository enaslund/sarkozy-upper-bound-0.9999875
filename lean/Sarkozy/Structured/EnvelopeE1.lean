module

public import Sarkozy.Structured.Representation
public import Sarkozy.Structured.ScaleInputs










@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- `ν(δ_x) = w(x)` for `ν = ∫ · w`. -/
theorem lawDensity_signedIntegral_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w : Ω → ℝ)
    (x : Ω) : lawDensity (signedIntegral w) x = w x := by
  unfold lawDensity signedIntegral
  simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_ite_eq']

/-- The unchanged input `F_A = Re 𝓛_{[N]} 1_A`, `N = K L`. -/
noncomputable def unchangedInput (Q : ℝ) (A : Finset ℤ) (L : ℕ) (y : ResidueSpace m) : ℝ :=
  (input m Q (Icc 1 ((blockScale * L : ℕ) : ℤ)) 1 0 A y).re

/-- The atom factors of the envelope of a choice with outside laws `μ_b`. -/
noncomputable def envelopeFactors {T : J → Type*} (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (D : ∀ b, T b → RecordExpansion.ChangeType → ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ)
    (ω : RecordExpansion.Choice T) : ∀ b, ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ :=
  fun b => RecordExpansion.entryFactor (signedIntegral (μb b).weight) (D b) (ω b)

/-- The square-step models of the unchanged input at the changed slots. -/
noncomputable def unchangedModel {Ω : Type*} (E : Finset J) (A : Finset ℤ) (L : ℕ)
    (Q' : Slot → ℝ) : Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ :=
  fun _ v x y =>
    (squareStepModel m E x (0 : ZMod 1) A (Icc (0 + 1) (0 + ((blockScale * L : ℕ) : ℤ))) 0
      (blockScale * L) (stepR m E 1) (blockScale * stepEll m E 1 (blockScale * L)) (Q' v) y).re

/-- **(E1), first bound, for an envelope with outside law `μ` and unchanged inputs**: for a
choice `ω` with `D_{supp ω} ≠ 1`,
`|Y_{(⊗_{supp ω} D) ⊗ μ_{-supp ω}}(F_A)| ≤ ∏_{supp ω} ‖D_b‖ [(1 + u_L) R_E^a Y + C_dc L^{-σ} α]`,
with `R_E = sq(D_E)`. -/
theorem abs_envelope_energy_le_unchanged (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
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
    (hunifS : selectedMarginalsUniform (selectedWeight E (envelopeFactors m μb D ω)))
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
        density (blockScale * L) A) :
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
        (liftWeight E (selectedWeight E (envelopeFactors m μb D ω)) (uniformRest (Xa := fun b => ZMod (m b)) E))
        (paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
          (fun _ _ => 0)) := by
    rw [h1, hinputs]
    exact h2.symm
  -- 3. `prop:record:density-structured` for the whole-group data
  have hunifF : selectedMarginalsUniform
      (liftWeight (Xa := fun b => ZMod (m b)) E (selectedWeight E (envelopeFactors m μb D ω))
        (uniformRest (Xa := fun b => ZMod (m b)) E)) :=
    selectedMarginalsUniform_liftWeight_uniform (Xa := fun b => ZMod (m b)) E _ hunifS
  have hTV : totalVariation
      (liftWeight (Xa := fun b => ZMod (m b)) E (selectedWeight E (envelopeFactors m μb D ω))
        (uniformRest (Xa := fun b => ZMod (m b)) E)) =
      totalVariation (selectedWeight E (envelopeFactors m μb D ω)) :=
    totalVariation_liftWeight (Xa := fun b => ZMod (m b)) E _ _
  have hmain := density_structured_scale m hpair hcex hθ hθ1 ha hC0 hL hY0 hsc hM0
    (FiniteLaw.tensor μb) (tensor_slot_reflection_positive μb hμb) E hDE hqE hcE hcE0 hcQ hcopE
    hqN P _ hunifF
    (fun _ => 1) (fun _ => le_rfl) (fun _ => one_dvd _) (fun _ _ => Nat.coprime_one_left _)
    (fun _ => blockScale * L) (fun _ => Or.inl rfl) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ => True) (fun _ _ h => hne (by simpa using h.1)) Q Q' (unchangedModel m E A L Q')
    (fun _ _ _ _ => rfl) (fun _ hv => absurd trivial hv) (fun v _ => hrest v)
    (fun _ _ _ j F => hinvT j F) (by rw [hTV]; exact hdc)
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

/-- **(E1), first bound, for unchanged inputs, with restoration from two scales.** For
unchanged inputs all slots have the same child scale `ℓ = ⌈N/(K R_E)⌉`. So one splitting
`G_N = G_n × X_extra` (`joinModuli m₀ p`) serves every slot, and the restoration
hypothesis of `abs_envelope_energy_le_unchanged` follows from WP-FI's
`referenceEnergy_stepLift_le_scale` (`restoration_of_two_scales`). Its hypotheses are:
* `hprod`: `μ_N = μ_n ⊗ ν`, (R1);
* (R2) for the atom laws;
* `hinv`: (R3) for translations supported on `E`;
* `hlarge`: every nonzero extra coordinate has order `> Q'`;
* `hY`: `Λ_{μ_n}(F_B) ≤ Y(ℓ, B)`, the definition of `Y` at the scale `ℓ`. -/
theorem abs_envelope_energy_le_unchanged_two_scales
    (hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
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
    (hunifS : selectedMarginalsUniform
      (selectedWeight E (envelopeFactors (joinModuli m₀ p) μb D ω)))
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
        (L : ℝ) ^ (-σ) * density (blockScale * L) A) :
    |diagonalIntegral (RecordExpansion.envelopeLaw (fun b => signedIntegral (μb b).weight) D ω)
        (unchangedInput (joinModuli m₀ p) Q A L)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (joinModuli m₀ p b),
          |lawDensity (envelopeFactors (joinModuli m₀ p) μb D ω b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
            ((stepR (joinModuli m₀ p) E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  abs_envelope_energy_le_unchanged (joinModuli m₀ p) hpair hcex hθ hθ1 ha hC0 hL hY0 hsc hM0
    μb hμb D ω E hE hDE hqE hcE hcE0 hcQ hcopE hqN hne hunifS P Q (fun _ => Q')
    (fun _ => restoration_of_two_scales m₀ p μn ν (FiniteLaw.tensor μb) hprod
      (tensor_slot_reflection_positive μb hμb) E hinv hlarge Yf _ _ hY)
    hinvT hdc

end TwoScales

end Sarkozy.Structured
