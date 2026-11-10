module

public import Sarkozy.EnvelopeInputs.PriceBridge
public import Sarkozy.EnvelopeInputs.FoldedExpansion

/-!
# (F) per term, in coordinates: the folded energies at `θ = ϑ`

Input (F) of `sharpFirstTerms_of_foldedPieces_uniform` and `envelopeBound_of_foldedPieces_uniform`
bounds the folded energies `𝔈_±(f) = ∫ (a ∘ φ_±) d(⊗_b R_{b,f_b})` with the unchanged input
`a = F_A` at every slot. This file proves that bound at `θ = ϑ` in the coordinate setting of
WP-R's envelope theorems (atoms = coordinates of the group):

* `foldedPlus_const`, `foldedMinus_const`: with a constant input the fold does nothing, and
  `𝔈_±(f)` is the diagonal integral of `⊗_b R_{b,f_b}`;
* `markChoice`, `tensorLaw_eq_envelopeLaw`: a tensor law equal to `μ_b` off `E` is the envelope
  law of the choice marking `E`;
* `abs_tensor_energy_le_unchanged_atoms`: (E1), first bound, at `ϑ`, for any tensor law equal to
  `μ` off a selected set: the per-term form of both (S) and (F);
* `abs_folded_energy_le_unchanged_atoms`, `abs_folded_energy_minus_le_unchanged_atoms`: (F) per
  term, from `abs_envelope_energy_le_unchanged_atoms`.

Not done here: the transport from WP-FI's atoms `Option (J L)` to these coordinates
(`tensorLaw_atoms_transport`), the identification of `atomLift` at the cut with `unchangedInput`,
and the per-term inputs (`hdc`, restoration, `hinvT`, `hatom`).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic

/-- **A folded energy with a constant input is a diagonal integral** of the folded laws. -/
theorem foldedPlus_const {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (c : ReflectionCut V) {I : J → Type*} (Lp : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (g : (∀ j, X j) → ℝ) (f : ∀ j, I j) :
    foldedPlus c Lp (fun _ => g) f = diagonalIntegral (tensorLaw fun j => Lp j (f j)) g :=
  rfl

/-- The same for `𝔈₋`. -/
theorem foldedMinus_const {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (c : ReflectionCut V) {I : J → Type*} (Lm : ∀ j, I j → ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (g : (∀ j, X j) → ℝ) (f : ∀ j, I j) :
    foldedMinus c Lm (fun _ => g) f = diagonalIntegral (tensorLaw fun j => Lm j (f j)) g :=
  rfl

/-- The choice marking a set `S` of atoms (one piece per atom, symmetric type). -/
def markChoice {J : Type*} [DecidableEq J] (S : Finset J) :
    RecordExpansion.Choice (fun _ : J => Unit) :=
  fun b => if b ∈ S then some ((), RecordExpansion.ChangeType.sym) else none

theorem support_markChoice {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) :
    RecordExpansion.Choice.support (markChoice S) = S := by
  ext b
  unfold RecordExpansion.Choice.support markChoice
  by_cases hb : b ∈ S <;> simp [hb]

/-- The factors `Λ_b` of the marking choice. -/
def markFactors {J V : Type*} {X : J → Type*} (Λ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ b, Unit → RecordExpansion.ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ :=
  fun b _ _ => Λ b

/-- **A tensor law equal to `N_b` off `S` is the envelope law of the marking choice of `S`.** -/
theorem tensorLaw_eq_envelopeLaw {V : Type*} [Fintype V] [DecidableEq V] {J : Type*} [Fintype J]
    [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (N Λ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (S : Finset J) (hS : ∀ b ∉ S, Λ b = N b) :
    tensorLaw Λ =
      RecordExpansion.envelopeLaw N (markFactors Λ) (markChoice S) := by
  unfold RecordExpansion.envelopeLaw
  congr 1
  funext b
  unfold markChoice
  by_cases hb : b ∈ S
  · simp [hb, RecordExpansion.entryFactor, markFactors]
  · simp [hb, RecordExpansion.entryFactor, hS b hb]

/-- Unit mixed bounds transfer along an equality of weights. -/
theorem mixedLpBound_variationLaw_congr {XE : Type*} [Fintype XE] [Nonempty XE]
    {ρ ρ' : (Slot → XE) → ℝ} (h : ρ = ρ') {p C : ℝ}
    (h' : ∀ hb : 0 < totalVariation ρ', MixedLpBound (variationLaw ρ' hb) p C)
    (hb : 0 < totalVariation ρ) : MixedLpBound (variationLaw ρ hb) p C := by
  subst h
  exact h' hb

/-- The selected weight depends only on the selected factors. -/
theorem selectedWeight_congr {J : Type*} [Fintype J] [DecidableEq J] {Xa : J → Type*}
    [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] (E : Finset J)
    (ν ν' : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ) (h : ∀ b ∈ E, ν b = ν' b) :
    selectedWeight E ν = selectedWeight E ν' := by
  funext z
  unfold selectedWeight
  exact prod_congr rfl fun b _ => by rw [h b b.2]

section Folded

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

omit [Fintype J] in
/-- The envelope factors of the marking choice are the marked factors on `E`. -/
theorem envelopeFactors_markChoice (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (Λ : ∀ b, ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ) (E : Finset J) (b : J) (hb : b ∈ E) :
    envelopeFactors m μb (markFactors Λ) (markChoice E) b = Λ b := by
  simp [envelopeFactors, markChoice, hb, RecordExpansion.entryFactor, markFactors]

/-- **(E1), first bound, at `θ = ϑ`, for a tensor law equal to `μ` off a selected set** (the
per-term form of (S) and (F)): if `Λ_b = μ_b` for `b ∉ E`, `D_E ≠ 1`, `q_E ≤ N^τ`, and every
`|Λ_b|/‖Λ_b‖`, `b ∈ E`, has unit mixed `L^{72/θ}`, then
`|Y_{⊗_b Λ_b}(F_A)| ≤ ∏_{b ∈ E} ‖Λ_b‖ [(1 + u_L) R_E^a Y + C_dc L^{-σ} α]`.
It is `abs_envelope_energy_le_unchanged_atoms` for the marking choice of `E`. -/
theorem abs_tensor_energy_le_unchanged_atoms (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (Λ : ∀ b, ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ) (E : Finset J)
    (hE : ∀ b ∉ E, Λ b = signedIntegral (μb b).weight)
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
          (liftWeight E (selectedWeight E Λ)
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
            (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E Λ)
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (unchangedModel m E A L Q')| ≤
      Cdc * totalVariation (selectedWeight E Λ) * (L : ℝ) ^ (-σ) *
        density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ E})
      (hb : 0 < totalVariation (lawDensity (Λ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |diagonalIntegral (tensorLaw Λ) (unchangedInput m Q A L)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
          |lawDensity (Λ b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * ((stepR m E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hfac : ∀ b ∈ E, envelopeFactors m μb (markFactors Λ) (markChoice E) b = Λ b :=
    fun b hb => envelopeFactors_markChoice m μb _ E b hb
  have hsel : selectedWeight E (envelopeFactors m μb (markFactors Λ) (markChoice E)) =
      selectedWeight E Λ := selectedWeight_congr E _ _ hfac
  have hlaw := tensorLaw_eq_envelopeLaw (fun b => signedIntegral (μb b).weight) Λ E hE
  have h := abs_envelope_energy_le_unchanged_atoms m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb
    hμb (markFactors Λ) (markChoice E) E (support_markChoice E) hDE hqE hcE hcE0
    hcQ hcopE hqN hne P Q Q' hrest hinvT (by rw [hsel]; exact hdc)
    (fun b hb => mixedLpBound_variationLaw_congr (congrArg lawDensity (hfac b b.2)) (hatom b) hb)
  have hprod : (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
      |lawDensity (envelopeFactors m μb (markFactors Λ) (markChoice E) b) y|) =
      ∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b), |lawDensity (Λ b) y| :=
    prod_congr rfl fun b _ => by rw [hfac b b.2]
  rw [hlaw]
  rw [hprod] at h
  exact h

/-- **(F) per term, in coordinates: the folded energy at `θ = ϑ`** (`lem:record:folded-energy`
with `prop:record:density-structured` for the folded laws). Let the folded laws `R_{b,f_b}` be
`μ_b` off a selected set `E` with `D_E ≠ 1` and `q_E ≤ N^τ`, and let each `|R_{b,f_b}|/‖R_{b,f_b}‖`,
`b ∈ E`, have unit mixed `L^{72/θ}`. Then for the unchanged input `F_A` at every slot,
`|𝔈_+(f)| ≤ ∏_{b ∈ E} ‖R_{b,f_b}‖ [(1 + u_L) R_E^a Y + C_dc L^{-σ} α]`.
It is `abs_envelope_energy_le_unchanged_atoms` for the marking choice of `E`. -/
theorem abs_folded_energy_le_unchanged_atoms (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (c : ReflectionCut Slot) {I : J → Type*}
    (Lp : ∀ b, I b → ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ) (f : ∀ b, I b) (E : Finset J)
    (hE : ∀ b ∉ E, Lp b (f b) = signedIntegral (μb b).weight)
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
          (liftWeight E (selectedWeight E (fun b => Lp b (f b)))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
            (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (fun b => Lp b (f b)))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (unchangedModel m E A L Q')| ≤
      Cdc * totalVariation (selectedWeight E (fun b => Lp b (f b))) * (L : ℝ) ^ (-σ) *
        density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ E})
      (hb : 0 < totalVariation (lawDensity (Lp b (f b)))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |foldedPlus c Lp (fun _ => unchangedInput m Q A L) f| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
          |lawDensity (Lp b (f b)) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * ((stepR m E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hfac : ∀ b ∈ E, envelopeFactors m μb (markFactors fun b => Lp b (f b)) (markChoice E) b =
      Lp b (f b) := fun b hb => envelopeFactors_markChoice m μb _ E b hb
  have hsel : selectedWeight E (envelopeFactors m μb (markFactors fun b => Lp b (f b))
      (markChoice E)) = selectedWeight E (fun b => Lp b (f b)) := selectedWeight_congr E _ _ hfac
  have hlaw := tensorLaw_eq_envelopeLaw (fun b => signedIntegral (μb b).weight)
    (fun b => Lp b (f b)) E hE
  have h := abs_envelope_energy_le_unchanged_atoms m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb
    hμb (markFactors fun b => Lp b (f b)) (markChoice E) E (support_markChoice E) hDE hqE hcE hcE0
    hcQ hcopE hqN hne P Q Q' hrest hinvT (by rw [hsel]; exact hdc)
    (fun b hb => mixedLpBound_variationLaw_congr (congrArg lawDensity (hfac b b.2)) (hatom b) hb)
  have hprod : (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
      |lawDensity (envelopeFactors m μb (markFactors fun b => Lp b (f b)) (markChoice E) b) y|) =
      ∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b), |lawDensity (Lp b (f b)) y| :=
    prod_congr rfl fun b _ => by rw [hfac b b.2]
  rw [foldedPlus_const, hlaw]
  rw [hprod] at h
  exact h

/-- The same for `𝔈₋`. -/
theorem abs_folded_energy_minus_le_unchanged_atoms (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (c : ReflectionCut Slot) {I : J → Type*}
    (Lp : ∀ b, I b → ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ) (f : ∀ b, I b) (E : Finset J)
    (hE : ∀ b ∉ E, Lp b (f b) = signedIntegral (μb b).weight)
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
          (liftWeight E (selectedWeight E (fun b => Lp b (f b)))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (paperInputs m E Q A (fun _ => 1) (fun _ => blockScale * L) (fun _ _ => 0)
            (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor μb) P
          (liftWeight E (selectedWeight E (fun b => Lp b (f b)))
            (uniformRest (Xa := fun b => ZMod (m b)) E))
          (unchangedModel m E A L Q')| ≤
      Cdc * totalVariation (selectedWeight E (fun b => Lp b (f b))) * (L : ℝ) ^ (-σ) *
        density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ E})
      (hb : 0 < totalVariation (lawDensity (Lp b (f b)))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |foldedMinus c Lp (fun _ => unchangedInput m Q A L) f| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
          |lawDensity (Lp b (f b)) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * ((stepR m E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hfac : ∀ b ∈ E, envelopeFactors m μb (markFactors fun b => Lp b (f b)) (markChoice E) b =
      Lp b (f b) := fun b hb => envelopeFactors_markChoice m μb _ E b hb
  have hsel : selectedWeight E (envelopeFactors m μb (markFactors fun b => Lp b (f b))
      (markChoice E)) = selectedWeight E (fun b => Lp b (f b)) := selectedWeight_congr E _ _ hfac
  have hlaw := tensorLaw_eq_envelopeLaw (fun b => signedIntegral (μb b).weight)
    (fun b => Lp b (f b)) E hE
  have h := abs_envelope_energy_le_unchanged_atoms m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb
    hμb (markFactors fun b => Lp b (f b)) (markChoice E) E (support_markChoice E) hDE hqE hcE hcE0
    hcQ hcopE hqN hne P Q Q' hrest hinvT (by rw [hsel]; exact hdc)
    (fun b hb => mixedLpBound_variationLaw_congr (congrArg lawDensity (hfac b b.2)) (hatom b) hb)
  have hprod : (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b),
      |lawDensity (envelopeFactors m μb (markFactors fun b => Lp b (f b)) (markChoice E) b) y|) =
      ∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b), |lawDensity (Lp b (f b)) y| :=
    prod_congr rfl fun b _ => by rw [hfac b b.2]
  rw [foldedMinus_const, hlaw]
  rw [hprod] at h
  exact h

end Folded

end Sarkozy.EnvelopeInputs
