module

public import Sarkozy.EnvelopeInputs.LiftMixed
public import Sarkozy.EnvelopeInputs.MixedChain
public import Sarkozy.EnvelopeInputs.UnchangedMixed

@[expose] public section

/-!
# The density chain at `θ = ϑ` with changed slot inputs (structured slot data)

`lem:bracket-energy`'s first bound is `prop:record:density-structured` for a positive selected
measure with *structured slot data*: at the query endpoints the inputs are
`g^{I_v, D_{0,v}, s_v}` (the revealed inputs of `lem:envelope-energy`, `TwoInterval`), and `F_A`
elsewhere. I1's chain at `ϑ` (`abs_tensor_energy_le_unchanged_atoms`) covers only the unchanged
inputs `F_A`. This file runs I1's general layer `density_structured_reference_mixed` (WP-R's
`density_structured_reference` with the density moment) on a tensor law with **arbitrary slot
inputs of the paper's form**, at a fixed index (the index law is a point; the per-index mean is
then automatic, `meanBound_of_subsingleton`):

* `multilinearIntegral_tensorLaw_eq_structuredEnergy`: the multilinear form of WP-R's bridge
  (`diagonalIntegral_tensorLaw_eq_structuredEnergy`), with a slot-dependent input;
* `revealedModel`: the square-step model of `lem:record:fibre-scale` for the slot data;
* **`abs_tensor_energy_le_structured`** (`prop:record:density-structured` with structured slot
  data, at `θ = ϑ`, with `lem:record:density-dc`): for `⊗_b Λ_b` equal to `μ_b` off a selected
  set `E` and the inputs `g^{I_v, D_{0,v}, s_v}` with `I_v = [c_v + 1, c_v + M_v]`,
  `|∫ ∏_v g_v d(⊗ Λ)| ≤ ∏_{E} ‖Λ_b‖ [(1 + u_L) Π_main Y + C_dc L^{-σ} α]`, where
  `Π_main = ∏_v ξ_v^{a/72} ∏_{v changed} (ᾱ_v/α)^{θ/72}` with `ξ_v = (N/M_v) sq(D_{0,v} D_E)` and
  `ᾱ_v` the density of `A` on `I_v ∩ {x ≡ s_v (D_{0,v})}` (`def:record:structured-energy`).

The inputs are those of I1's chain: the modulus conditions on `D_E`, the restoration `hrest`, the
density-dc comparison `hdc` (per term), the unit mixed `L^{72/θ}` of the selected factors
`hatom`, and the unchanged slots `hun`; (R2), (R3) of the reference. Nothing about the inputs is
assumed beyond their form.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic
  Sarkozy.PaperFrame

section Bridge

variable {J : Type*} [Fintype J] [DecidableEq J] {Xa : J → Type*} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- **Tensor-law energies with slot-dependent inputs are structured energies** (the multilinear
form of `diagonalIntegral_tensorLaw_eq_structuredEnergy`). -/
theorem multilinearIntegral_tensorLaw_eq_structuredEnergy (E : Finset J)
    (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (G : Slot → (∀ b, Xa b) → ℝ) :
    multilinearIntegral (tensorLaw ν) G =
      structuredEnergy μS P (selectedWeight E ν) (fun _ v z x => G v (joinLabels E z x)) := by
  unfold structuredEnergy
  rw [FiniteLaw.expect_const]
  change (∑ y : ∀ j, Slot → Xa j, (∏ j, lawDensity (ν j) (y j)) * ∏ v, G v (fun j => y j v)) = _
  rw [← (splitLabels E).symm.sum_comp, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro z _
  unfold multilinearIntegral signedIntegral
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [mul_sum]
  apply sum_congr rfl
  intro w _
  have hsplit : (∏ j, lawDensity (ν j) ((splitLabels E).symm (z, w) j)) =
      selectedWeight E ν z * μS.weight w := by
    rw [hμS, ← Fintype.prod_subtype_mul_prod_subtype (fun b => b ∈ E)]
    unfold selectedWeight
    congr 1
    · refine Finset.prod_congr (by congr 1; exact Subsingleton.elim _ _) (fun b _ => ?_)
      congr 1
      funext v
      exact joinLabels_mem E (z v) (w v) b
    · refine Finset.prod_congr rfl (fun b _ => ?_)
      congr 1
      funext v
      exact joinLabels_not_mem E (z v) (w v) b
  rw [hsplit]
  change (selectedWeight E ν z * μS.weight w) * ∏ v, G v (joinLabels E (z v) (w v)) =
    selectedWeight E ν z * (μS.weight w * ∏ v, G v (joinLabels E (z v) (w v)))
  ring

end Bridge

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The square-step model `g̃_v` of the slot data (`lem:record:fibre-scale`). -/
noncomputable def revealedModel (E : Finset J) (A : Finset ℤ) (D0 M : Slot → ℕ) (c : Slot → ℤ)
    (s : ∀ v : Slot, ZMod (D0 v)) (Q' : Slot → ℝ) (v : Slot) (x : ResidueSpace m) :
    ResidueSpace m → ℝ := fun y =>
  (squareStepModel m E x (s v) A (Icc (c v + 1) (c v + M v)) (c v) (M v) (stepR m E (D0 v))
    (blockScale * stepEll m E (D0 v) (M v)) (Q' v) y).re

/-- **`prop:record:density-structured` with structured slot data, at `θ = ϑ`** (with
`lem:record:density-dc`; the first bound of `lem:bracket-energy` for the revealed inputs of
`lem:envelope-energy` at a fixed index). For a tensor law `⊗_b Λ_b` equal to `μ_b` off `E`, and
the inputs `g^{I_v, D_{0,v}, s_v}` (`I_v = [c_v + 1, c_v + M_v]`, `M_v ∈ {N, L}`) at the slots,
`|∫ ∏_v g_v d(⊗ Λ)| ≤ ∏_{E} ‖Λ_b‖ [(1 + u_L) Π_main Y + C_dc L^{-σ} α]` with the main price of
`def:record:structured-energy` at the point index. -/
theorem abs_tensor_energy_le_structured (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (hR3 : SquareAffineInvariant m μb)
    (Λ : ∀ b, ((Slot → ZMod (m b)) → ℝ) →ₗ[ℝ] ℝ) (E : Finset J)
    (hE : ∀ b ∉ E, Λ b = signedIntegral (μb b).weight)
    {qE cE : ℕ} (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE) (hcE : IsSquare cE)
    (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (D0 : Slot → ℕ) (hD0 : ∀ v, 1 ≤ D0 v) (hD0M : ∀ v, D0 v ∣ M0)
    (hcop0 : ∀ v k, (D0 v).Coprime (m k))
    (M : Slot → ℕ) (hM : ∀ v, M v = blockScale * L ∨ M v = L)
    (c : Slot → ℤ) (s : ∀ v : Slot, ZMod (D0 v))
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, m j = 1 ∧ M v = blockScale * L))
    (Q : ℝ) (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy (FiniteLaw.tensor μb)
      (revealedModel m E A D0 M c s Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) (FiniteLaw.uniform Unit)
          (liftWeight E (selectedWeight E Λ) (uniformRest (Xa := fun b => ZMod (m b)) E))
          (paperInputs m E Q A D0 M (fun _ => c) (fun _ => s)) -
        structuredEnergy (FiniteLaw.tensor μb) (FiniteLaw.uniform Unit)
          (liftWeight E (selectedWeight E Λ) (uniformRest (Xa := fun b => ZMod (m b)) E))
          (fun _ => revealedModel m E A D0 M c s Q')| ≤
      Cdc * totalVariation (selectedWeight E Λ) * (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ (b : {b // b ∈ E}) (hb : 0 < totalVariation (lawDensity (Λ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw Λ)
        (fun v y => (input m Q (Icc (c v + 1) (c v + M v)) (D0 v) (s v) A y).re)| ≤
      (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (m b), |lawDensity (Λ b) y|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice m E D0 M L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A D0 M (fun _ => c) (fun _ => s))
            changed a θ (density (blockScale * L) A) * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  set G : Slot → ResidueSpace m → ℝ :=
    fun v y => (input m Q (Icc (c v + 1) (c v + M v)) (D0 v) (s v) A y).re
  -- 1. the bridge to a structured energy with the outside law `μ` off `E`
  have h1 : multilinearIntegral (tensorLaw Λ) G =
      structuredEnergy (FiniteLaw.tensor fun b : {b // b ∉ E} => μb b) (FiniteLaw.uniform Unit)
        (selectedWeight E Λ) (fun _ v z x => G v (joinLabels E z x)) := by
    apply multilinearIntegral_tensorLaw_eq_structuredEnergy
    intro w
    rw [tensor_weight]
    apply prod_congr rfl
    intro b _
    rw [hE b b.2]
    exact (lawDensity_signedIntegral_eq _ _).symm
  -- 2. the lift to the whole group
  have h2 := structuredEnergy_liftWeight E (FiniteLaw.tensor μb)
    (FiniteLaw.tensor fun b : {b // b ∉ E} => μb b)
    (expect_tensor_restrict E μb) (FiniteLaw.uniform Unit) (selectedWeight E Λ)
    (uniformRest (Xa := fun b => ZMod (m b)) E) (fun _ => G)
  have hinputs : paperInputs m E Q A D0 M (fun (_ : Unit) => c) (fun _ => s) =
      fun _ v x y => G v (freezeLabels E x y) := by
    funext ω' v x y
    rfl
  have hsame : multilinearIntegral (tensorLaw Λ) G =
      structuredEnergy (FiniteLaw.tensor μb) (FiniteLaw.uniform Unit)
        (liftWeight E (selectedWeight E Λ) (uniformRest (Xa := fun b => ZMod (m b)) E))
        (paperInputs m E Q A D0 M (fun _ => c) (fun _ => s)) := by
    rw [h1, hinputs]
    exact h2.symm
  -- 3. the chain (`density_structured_reference_mixed`) at the point index
  have hTV : totalVariation
      (liftWeight (Xa := fun b => ZMod (m b)) E (selectedWeight E Λ)
        (uniformRest (Xa := fun b => ZMod (m b)) E)) = totalVariation (selectedWeight E Λ) :=
    totalVariation_liftWeight (Xa := fun b => ZMod (m b)) E _ _
  have hmix : ∀ hρ : 0 < totalVariation (liftWeight (Xa := fun b => ZMod (m b)) E
      (selectedWeight E Λ) (uniformRest (Xa := fun b => ZMod (m b)) E)),
      MixedLpBound (variationLaw _ hρ) (72 / θ) 1 := fun h' =>
    mixedLpBound_liftWeight_uniform E _ (by rwa [totalVariation_liftWeight] at h')
      (one_le_72_div hθ hθ2)
      (mixedLpBound_selectedWeight E _ (by linarith [one_le_72_div hθ hθ2]) hatom _) h'
  have hmain := density_structured_reference_mixed m hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb
    hμb hR3 E hDE hqE hcE hcE0 hcQ hcopE hqN (FiniteLaw.uniform Unit)
    (liftWeight E (selectedWeight E Λ) (uniformRest (Xa := fun b => ZMod (m b)) E))
    D0 hD0 hD0M hcop0 M hM (fun _ => c) (fun _ => s) changed hchg Q Q'
    (fun _ => revealedModel m E A D0 M c s Q') (fun _ _ _ _ => rfl)
    (fun v hv _ x => hun v hv x) hrest (by rw [hTV]; exact hdc) hmix
    (meanBound_of_subsingleton m E A _ D0 M _ _ changed)
  rw [hsame]
  rw [hTV, totalVariation_selectedWeight (Xa := fun b => ZMod (m b))] at hmain
  exact hmain

end Sarkozy.BracketEnergy
