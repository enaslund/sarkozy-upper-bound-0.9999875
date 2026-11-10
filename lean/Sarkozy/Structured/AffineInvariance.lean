module

public import Sarkozy.Structured.EnvelopeE1

/-!
# (R3) and the invariance hypotheses

(R3) of `hyp:record:reference` (`paper/sections/06_lifts_sectors.tex`) states that every
atom law `μ_b` is square-affine invariant: it is invariant under the simultaneous maps
`z_v ↦ r z_v + t`, with `r` a square unit (independently for the primes of a block).
This file derives from (R3) the two invariance hypotheses that the structured-energy
estimate uses for `μ_N = ⊗_b μ_b`. It takes the coordinates of the group as atoms, so it
covers the one-prime atoms (clique and tail atoms) but not the multi-prime blocks of `𝒫₃`;
the generic step `tensor_expect_comp` applies to any atom labels:

* `hinvT` of `changed_slot_bound_paper` and `density_structured_scale`: invariance under
  the maps `T_j = stepMapOff` (`tensor_expect_stepMapOff`). Off `E`, `T_j` is
  `y ↦ R^{-1}(y - t)` with `R = sq(D₀ D_E)` a square coprime to the modulus.
  Its inverse `x ↦ R x + t` is square-affine.
* `hinv` of WP-FI's `referenceEnergy_stepLift_le_scale`: invariance under the
  translations supported on `E` (`tensor_expect_translate`), the case `r = 1`.

The generic step is `tensor_expect_comp`: a product law is invariant under a
coordinatewise map applied at all slots when every atom law is invariant under its
coordinate map.

`density_structured_reference` is `density_structured_scale` for `μ_N = ⊗_b μ_b`, with
(R2) and (R3) in place of the reflection positivity of `μ_N` and of `hinvT`.

`abs_envelope_energy_le_unchanged_reference` is (E1), first bound, for the envelopes with
outside law `μ` and unchanged inputs. Its hypotheses are:
* (R1) in the two-scale form `μ_N = μ_n ⊗ ν`;
* (R2) and (R3) for the atom laws;
* the large orders of the extra coordinates;
* the definition of `Y` at the child scale;
* (O1) for the selected product;
* `lem:record:density-dc`;
* the scale conditions.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

/-! ## Invariance of product laws -/

/-- Invariance of a law under a slotwise injective map gives invariance of its weight. -/
theorem weight_comp_of_expect_comp {X : Type*} [Fintype X] [DecidableEq X]
    (μ : FiniteLaw (Slot → X)) (φ : X → X) (hφ : Function.Injective φ)
    (h : ∀ F : (Slot → X) → ℝ, μ.expect (fun w => F (fun v => φ (w v))) = μ.expect F)
    (w : Slot → X) : μ.weight (fun v => φ (w v)) = μ.weight w := by
  have h1 := h (fun w' => if w' = (fun v => φ (w v)) then 1 else 0)
  unfold FiniteLaw.expect at h1
  have hinj : ∀ w' : Slot → X, ((fun v => φ (w' v)) = (fun v => φ (w v))) ↔ w' = w := by
    intro w'
    constructor
    · intro h'
      funext v
      exact hφ (congrFun h' v)
    · intro h'
      rw [h']
  simp only [hinj, mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] at h1
  exact h1.symm

section Generic

variable {J : Type*} [Fintype J] [DecidableEq J] {Xa : J → Type*} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- **A product law is invariant under coordinatewise maps** applied at all slots, if
every atom law is invariant under its coordinate map. -/
theorem tensor_expect_comp (μ : ∀ b, FiniteLaw (Slot → Xa b)) (φ : ∀ b, Xa b → Xa b)
    (hφ : ∀ b, Function.Injective (φ b))
    (h : ∀ b (F : (Slot → Xa b) → ℝ),
      (μ b).expect (fun w => F (fun v => φ b (w v))) = (μ b).expect F)
    (F : (Slot → ∀ b, Xa b) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun y => F (fun v b => φ b (y v b))) =
      (FiniteLaw.tensor μ).expect F := by
  have hinj : Function.Injective (fun (y : Slot → ∀ b, Xa b) v b => φ b (y v b)) := by
    intro y y' hyy
    funext v b
    exact hφ b (congrFun (congrFun hyy v) b)
  have hbij := Finite.injective_iff_bijective.mp hinj
  unfold FiniteLaw.expect
  apply Fintype.sum_bijective _ hbij
  intro y
  simp only [tensor_weight]
  congr 1
  apply prod_congr rfl
  intro b _
  exact (weight_comp_of_expect_comp (μ b) (φ b) (hφ b) (h b) (fun v => y v b)).symm

end Generic

/-! ## (R3) -/

section Paper

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- **(R3)** of `hyp:record:reference`, with the coordinates as atoms: every `μ_b` is
invariant under the simultaneous maps `z_v ↦ r z_v + t`, with `r` a square unit. -/
def SquareAffineInvariant (μb : ∀ b, FiniteLaw (Slot → ZMod (m b))) : Prop :=
  ∀ b (r t : ZMod (m b)), IsUnit r → IsSquare r → ∀ F : (Slot → ZMod (m b)) → ℝ,
    (μb b).expect (fun w => F (fun v => r * w v + t)) = (μb b).expect F

omit [Fintype J] [DecidableEq J] in
/-- `R⁻¹ R = 1` modulo a modulus coprime to `R`. -/
theorem inv_mul_natCast_eq_one {n R : ℕ} (h : R.Coprime n) :
    ((R : ZMod n))⁻¹ * (R : ZMod n) = 1 := by
  rw [mul_comm]
  exact ZMod.coe_mul_inv_eq_one R h

/-- **(R3) gives the invariance under the maps `T_j`** (`hinvT`): if `R` is a square
coprime to the moduli off `E`, the product of square-affine invariant atom laws is
invariant under `stepMapOff m E R c j` at all slots. -/
theorem tensor_expect_stepMapOff (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hR3 : SquareAffineInvariant m μb) (E : Finset J) {R : ℕ} (hRsq : IsSquare R)
    (hcop : ∀ k ∉ E, R.Coprime (m k)) (c j : ℤ) (F : (Slot → ResidueSpace m) → ℝ) :
    (FiniteLaw.tensor μb).expect (fun w => F (fun v => stepMapOff m E R c j (w v))) =
      (FiniteLaw.tensor μb).expect F := by
  set φ : ∀ k, ZMod (m k) → ZMod (m k) := fun k x =>
    if k ∈ E then x else ((R : ZMod (m k)))⁻¹ * (x - ((c + (j - R) : ℤ) : ZMod (m k)))
    with hφdef
  have hmap : ∀ y : ResidueSpace m, stepMapOff m E R c j y = fun k => φ k (y k) := by
    intro y
    funext k
    rfl
  have hinj : ∀ k, Function.Injective (φ k) := by
    intro k x y hxy
    by_cases hk : k ∈ E
    · simpa [hφdef, hk] using hxy
    · simp only [hφdef, hk, ↓reduceIte] at hxy
      have h1 := congrArg (fun z => (R : ZMod (m k)) * z) hxy
      simp only [← mul_assoc, ZMod.coe_mul_inv_eq_one R (hcop k hk), one_mul] at h1
      exact sub_left_injective h1
  have hinv : ∀ k (G : (Slot → ZMod (m k)) → ℝ),
      (μb k).expect (fun w => G (fun v => φ k (w v))) = (μb k).expect G := by
    intro k G
    by_cases hk : k ∈ E
    · simp only [hφdef, hk, ↓reduceIte]
    · have hunit : IsUnit (R : ZMod (m k)) := by
        rw [← ZMod.coe_unitOfCoprime R (hcop k hk)]
        exact Units.isUnit _
      have hsq : IsSquare (R : ZMod (m k)) := by
        obtain ⟨s, hs⟩ := hRsq
        exact ⟨(s : ZMod (m k)), by rw [hs]; push_cast; ring⟩
      have h := hR3 k (R : ZMod (m k)) ((c + (j - R) : ℤ) : ZMod (m k)) hunit hsq
        (fun w => G (fun v => φ k (w v)))
      have hback : ∀ x : ZMod (m k),
          φ k ((R : ZMod (m k)) * x + ((c + (j - R) : ℤ) : ZMod (m k))) = x := by
        intro x
        simp only [hφdef, hk, ↓reduceIte, add_sub_cancel_right, ← mul_assoc,
          inv_mul_natCast_eq_one (hcop k hk), one_mul]
      simp only [hback] at h
      exact h.symm
  simp_rw [hmap]
  exact tensor_expect_comp μb φ hinj hinv F

/-- **(R3) gives the invariance under the translations supported on `E`** (`hinv` of
WP-FI's `referenceEnergy_stepLift_le_scale`), the case `r = 1`. -/
theorem tensor_expect_translate (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hR3 : SquareAffineInvariant m μb) (s : ResidueSpace m) (F : (Slot → ResidueSpace m) → ℝ) :
    (FiniteLaw.tensor μb).expect (fun z => F (fun v => z v + s)) =
      (FiniteLaw.tensor μb).expect F := by
  have hinv : ∀ k (G : (Slot → ZMod (m k)) → ℝ),
      (μb k).expect (fun w => G (fun v => w v + s k)) = (μb k).expect G := by
    intro k G
    have h := hR3 k 1 (s k) isUnit_one ⟨1, (mul_one 1).symm⟩ G
    simpa only [one_mul] using h
  exact tensor_expect_comp μb (fun k x => x + s k) (fun k => add_left_injective (s k)) hinv F

end Paper

/-! ## `prop:record:density-structured` with (R2) and (R3) -/

section DensityReference

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- **`prop:record:density-structured` for `μ_N = ⊗_b μ_b`**: `density_structured_scale`
with (R2) and (R3) for the atom laws in place of the reflection positivity of `μ_𝒮` and
of `hinvT`. -/
theorem density_structured_reference (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (hR3 : SquareAffineInvariant m μb) (E : Finset J) {qE cE : ℕ}
    (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0)
    (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ) (hunif : selectedMarginalsUniform ρ)
    (D0 : Slot → ℕ) (hD0 : ∀ v, 1 ≤ D0 v) (hD0M : ∀ v, D0 v ∣ M0)
    (hcop0 : ∀ v k, (D0 v).Coprime (m k))
    (M : Slot → ℕ) (hM : ∀ v, M v = blockScale * L ∨ M v = L)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, m j = 1 ∧ M v = blockScale * L))
    (Q : ℝ) (Q' : Slot → ℝ) (gt : Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ)
    (hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel m E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR m E (D0 v)) (blockScale * stepEll m E (D0 v) (M v)) (Q' v) y).re)
    (hun : ∀ v, ¬changed v → ∀ ω x, referenceEnergy (FiniteLaw.tensor μb) (gt ω v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy (FiniteLaw.tensor μb) P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :
    |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  density_structured_scale m hpair hcex hθ hθ1 ha hC0 hL hY0 hsc hM0 (FiniteLaw.tensor μb)
    (tensor_slot_reflection_positive μb hμb) E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0
    hD0M hcop0 M hM c s changed hchg Q Q' gt hgt hun hrest
    (fun v _ ω j F => tensor_expect_stepMapOff m μb hR3 E (isSquare_leastSquare _)
      (leastSquare_step_conditions m (E := E) (hD0 v) (hcop0 v) hpair).2.2.2 (c ω v) j F)
    hdc

end DensityReference

/-! ## (E1) for unchanged inputs from the reference hypotheses -/

section Reference

variable {J₀ J' : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J'] [DecidableEq J']
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J' → ℕ) [∀ j, NeZero (p j)]

/-- **(E1), first bound, for an envelope with outside law `μ` and unchanged inputs, from
the reference hypotheses.** This is `abs_envelope_energy_le_unchanged_two_scales` with
both invariance hypotheses derived from (R3). The remaining hypotheses are:
* (R1) in two-scale form (`hprod`);
* (R2) (`hμb`) and (R3) (`hR3`) for the atom laws;
* large orders of the extra coordinates (`hlarge`);
* the definition of `Y` at the child scale (`hY`);
* (O1) for the selected product (`hunifS`);
* `lem:record:density-dc` (`hdc`);
* the scale conditions and the factorization of `D_E`. -/
theorem abs_envelope_energy_le_unchanged_reference
    (hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (joinModuli m₀ p b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (hR3 : SquareAffineInvariant (joinModuli m₀ p) μb)
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
    (hlarge : ∀ k (x : ZMod (p k)), x ≠ 0 → Q' < addOrderOf x)
    (hY : ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ p) E 1 (blockScale * L) : ℕ) : ℤ) →
      referenceEnergy μn (fun x => (wholeLift m₀ Q'
          (blockScale * stepEll (joinModuli m₀ p) E 1 (blockScale * L)) B x).re) ≤
        Yf (stepEll (joinModuli m₀ p) E 1 (blockScale * L)) B)
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
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hcond := leastSquare_step_conditions (joinModuli m₀ p) (E := E) (D0 := 1) le_rfl
    (fun _ => Nat.coprime_one_left _) hpair
  exact abs_envelope_energy_le_unchanged_two_scales m₀ p hpair hcex hθ hθ1 ha hC0 hL hY0 hsc
    hM0 μb hμb D ω E hE hDE hqE hcE hcE0 hcQ hcopE hqN hne hunifS P Q Q' μn ν hprod
    (fun s _ F => tensor_expect_translate (joinModuli m₀ p) μb hR3 s F) hlarge hY
    (fun j F => tensor_expect_stepMapOff (joinModuli m₀ p) μb hR3 E (isSquare_leastSquare _)
      hcond.2.2.2 0 j F)
    hdc

end Reference

end Sarkozy.Structured
