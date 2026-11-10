module

public import Sarkozy.Structured.HandOff
public import Sarkozy.RecordExpansion.Bound

/-!
# Tensor-law energies as structured energies

`Sarkozy.RecordExpansion` writes energies as `diagonalIntegral (tensorLaw ν) F`, with one
functional `ν_b` on `(V → X_b) → ℝ` for every atom `b` and labels `∀ b, X_b`. The
structured energies of `Sarkozy/Structured/MainTerm.lean` have a reference law `μ_𝒮` on
`Slot → X_𝒮` and a selected measure `ρ` on `Slot → X_E`. This file identifies the two
for the paper's slots `V = Slot`, which is the paper's remark after `lem:sharp-first`
(`paper/sections/10_comparison_lemmas.tex`): "for admissible positive `κ` with
`q_X ≤ N^τ`, `𝔈[κ]` is a structured energy".

* `splitLabels`: `(∀ b, Slot → X_b) ≃ (Slot → X_E) × (Slot → X_𝒮)`, with
  `X_E = ∀ b : E, X_b` and `X_𝒮 = ∀ b ∉ E, X_b`.
* `diagonalIntegral_tensorLaw_eq_structuredEnergy`: if the atoms outside `E` carry
  the laws whose product is `μ_𝒮`, then
  `Y_{⊗_b ν_b}(F) = 𝔈` for the selected weight `ρ = ⊗_{b ∈ E} ν_b`
  (`selectedWeight`) and the inputs `g_v(z, x) = F(z ⊔ x)` (`F` at every slot).
* `totalVariation_selectedWeight`: `‖ρ‖ = ∏_{b ∈ E} ‖ν_b‖`, the multiplicativity of the
  norms in (E1).
* `envelopeLaw_eq_structuredEnergy`, `abs_envelope_energy_le`: for the envelope law of a
  choice `ω` with outside law `μ`, the selected set is the support of `ω`. Then
  `density_structured` bounds the envelope energy by
  `‖ρ‖ [(1 + u) Π_main Y + C_dc L^{-σ} α]`. With the per-slot bounds of the paper's
  unchanged inputs, `Π_main = R_E^a` (`mainPrice_unchanged_inputs`), so this is (E1),
  first bound, for the envelopes, with outside law `μ`.

The outside law `Ñ` of `hE1` in `abs_energy_sub_le_of_envelopes` is not covered here;
it needs the bracket expansion
(`Sarkozy.RecordExpansion.envelope_energy_le_of_bracket`).
`Sarkozy/Structured/Representation.lean` identifies the split labels here with WP-FI's
whole-group `coordinateFreeze` representation of `Sarkozy/Structured/PaperSlot.lean`.
`Sarkozy/Structured/EnvelopeE1.lean` uses it for the paper's `F_A`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

variable {J : Type*} [Fintype J] [DecidableEq J] {Xa : J → Type*} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-- The label with the selected coordinates from `z` and the others from `x`. -/
def joinLabels (E : Finset J) (z : ∀ b : {b // b ∈ E}, Xa b) (x : ∀ b : {b // b ∉ E}, Xa b) :
    ∀ b, Xa b :=
  fun b => if h : b ∈ E then z ⟨b, h⟩ else x ⟨b, h⟩

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
theorem joinLabels_mem (E : Finset J) (z : ∀ b : {b // b ∈ E}, Xa b)
    (x : ∀ b : {b // b ∉ E}, Xa b) (b : {b // b ∈ E}) : joinLabels E z x b = z b := by
  unfold joinLabels
  simp [b.2]

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
theorem joinLabels_not_mem (E : Finset J) (z : ∀ b : {b // b ∈ E}, Xa b)
    (x : ∀ b : {b // b ∉ E}, Xa b) (b : {b // b ∉ E}) : joinLabels E z x b = x b := by
  unfold joinLabels
  simp [b.2]

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
/-- The splitting of the atom labels into selected and remaining labels. -/
def splitLabels (E : Finset J) :
    (∀ b, Slot → Xa b) ≃
      (Slot → ∀ b : {b // b ∈ E}, Xa b) × (Slot → ∀ b : {b // b ∉ E}, Xa b) where
  toFun y := (fun v b => y b v, fun v b => y b v)
  invFun p := fun b v => joinLabels E (p.1 v) (p.2 v) b
  left_inv y := by
    funext b v
    dsimp only
    unfold joinLabels
    split_ifs <;> rfl
  right_inv p := by
    ext v b
    · exact joinLabels_mem E (p.1 v) (p.2 v) b
    · exact joinLabels_not_mem E (p.1 v) (p.2 v) b

/-- The weight of the selected measure `⊗_{b ∈ E} ν_b` on `Slot → X_E`. -/
noncomputable def selectedWeight (E : Finset J) (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (z : Slot → ∀ b : {b // b ∈ E}, Xa b) : ℝ :=
  ∏ b : {b // b ∈ E}, lawDensity (ν b) (fun v => z v b)

/-- **Tensor-law energies are structured energies.** If the atoms outside `E` carry the
functionals whose product is the law `μ_𝒮`, then
`Y_{⊗_b ν_b}(F) = E_P ∫ Λ_{μ_𝒮}((F(z_v ⊔ ·))_v) dρ(z)` with `ρ = ⊗_{b ∈ E} ν_b`. -/
theorem diagonalIntegral_tensorLaw_eq_structuredEnergy (E : Finset J)
    (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ E}, lawDensity (ν b) (fun v => w v b))
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (F : (∀ b, Xa b) → ℝ) :
    diagonalIntegral (tensorLaw ν) F =
      structuredEnergy μS P (selectedWeight E ν) (fun _ _ z x => F (joinLabels E z x)) := by
  unfold structuredEnergy
  rw [FiniteLaw.expect_const]
  change (∑ y : ∀ j, Slot → Xa j, (∏ j, lawDensity (ν j) (y j)) * ∏ v, F (fun j => y j v)) = _
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
  change (selectedWeight E ν z * μS.weight w) * ∏ v, F (joinLabels E (z v) (w v)) =
    selectedWeight E ν z * (μS.weight w * ∏ v, F (joinLabels E (z v) (w v)))
  ring

/-- The transposition `Slot → X_E ≃ ∀ b ∈ E, Slot → X_b`. -/
def transposeLabels (E : Finset J) :
    (Slot → ∀ b : {b // b ∈ E}, Xa b) ≃ (∀ b : {b // b ∈ E}, Slot → Xa b) :=
  Equiv.piComm _

omit [Fintype J] in
/-- **`‖⊗_{b ∈ E} ν_b‖ = ∏_{b ∈ E} ‖ν_b‖`**, with `‖ν_b‖ = ∑_y |ν_b(δ_y)|`. -/
theorem totalVariation_selectedWeight (E : Finset J) (ν : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ) :
    totalVariation (selectedWeight E ν) =
      ∏ b : {b // b ∈ E}, ∑ y : Slot → Xa b, |lawDensity (ν b) y| := by
  unfold totalVariation selectedWeight
  rw [← (transposeLabels E).symm.sum_comp]
  rw [Fintype.prod_sum (fun (b : {b // b ∈ E}) (y : Slot → Xa b) => |lawDensity (ν b) y|)]
  apply sum_congr rfl
  intro y _
  rw [Finset.abs_prod]
  rfl

/-- **The envelope law of a choice with outside law `μ` is a structured energy**, with
selected set the support of the choice and selected weight `⊗_{b ∈ supp ω} D_{b,t_b}^{ε_b}`. -/
theorem envelopeLaw_eq_structuredEnergy {T : J → Type*}
    (N : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (D : ∀ b, T b → Sarkozy.RecordExpansion.ChangeType → ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (ω : Sarkozy.RecordExpansion.Choice T)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ Sarkozy.RecordExpansion.Choice.support ω}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ Sarkozy.RecordExpansion.Choice.support ω},
      lawDensity (N b) (fun v => w v b))
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (F : (∀ b, Xa b) → ℝ) :
    diagonalIntegral (Sarkozy.RecordExpansion.envelopeLaw N D ω) F =
      structuredEnergy μS P
        (selectedWeight (Sarkozy.RecordExpansion.Choice.support ω)
          (fun b => Sarkozy.RecordExpansion.entryFactor (N b) (D b) (ω b)))
        (fun _ _ z x => F (joinLabels _ z x)) := by
  apply diagonalIntegral_tensorLaw_eq_structuredEnergy
  intro w
  rw [hμS]
  apply prod_congr rfl
  intro b _
  have hb : ω b = none := by
    have h := b.2
    unfold Sarkozy.RecordExpansion.Choice.support at h
    rw [mem_filter] at h
    simpa using h
  rw [hb]
  rfl

/-- **(E1), first bound, for an envelope with outside law `μ`**:
`prop:record:density-structured` (abstract form, `density_structured`) for the structured
energy of `envelopeLaw_eq_structuredEnergy`, whose inputs are `F` at every slot. The
per-slot bounds of the paper's inputs are hypotheses, as in `density_structured`. -/
theorem abs_envelope_energy_le {T : J → Type*}
    (N : ∀ b, ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (D : ∀ b, T b → Sarkozy.RecordExpansion.ChangeType → ((Slot → Xa b) → ℝ) →ₗ[ℝ] ℝ)
    (ω : Sarkozy.RecordExpansion.Choice T)
    (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ Sarkozy.RecordExpansion.Choice.support ω}, Xa b))
    (hμS : ∀ w, μS.weight w = ∏ b : {b // b ∉ Sarkozy.RecordExpansion.Choice.support ω},
      lawDensity (N b) (fun v => w v b))
    (hμSp : SlotReflectionPositive (signedIntegral μS.weight))
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (F : (∀ b, Xa b) → ℝ)
    (gt : Ω → Slot → (∀ b : {b // b ∈ Sarkozy.RecordExpansion.Choice.support ω}, Xa b) →
      (∀ b : {b // b ∉ Sarkozy.RecordExpansion.Choice.support ω}, Xa b) → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y) (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω' z, referenceEnergy μS (gt ω' v z) ≤ Y)
    (αf : Ω → Slot → (∀ b : {b // b ∈ Sarkozy.RecordExpansion.Choice.support ω}, Xa b) → ℝ)
    (hαf : ∀ ω' v z, 0 ≤ αf ω' v z)
    (hch : ∀ v, changed v → ∀ ω' z,
      referenceEnergy μS (gt ω' v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω' v z ^ θ)
    (hmean : ∀ hρ : 0 < totalVariation (selectedWeight (Sarkozy.RecordExpansion.Choice.support ω)
        (fun b => Sarkozy.RecordExpansion.entryFactor (N b) (D b) (ω b))), ∀ v, changed v →
      (P.product (variationLaw _ hρ)).expect (fun p => αf p.1 v (p.2 v)) = αbar v)
    (hdc : |structuredEnergy μS P
        (selectedWeight (Sarkozy.RecordExpansion.Choice.support ω)
          (fun b => Sarkozy.RecordExpansion.entryFactor (N b) (D b) (ω b)))
        (fun _ _ z x => F (joinLabels _ z x)) -
      structuredEnergy μS P
        (selectedWeight (Sarkozy.RecordExpansion.Choice.support ω)
          (fun b => Sarkozy.RecordExpansion.entryFactor (N b) (D b) (ω b))) gt| ≤
      Cdc * totalVariation (selectedWeight (Sarkozy.RecordExpansion.Choice.support ω)
          (fun b => Sarkozy.RecordExpansion.entryFactor (N b) (D b) (ω b))) * L ^ (-σ) * α) :
    |diagonalIntegral (Sarkozy.RecordExpansion.envelopeLaw N D ω) F| ≤
      (∏ b : {b // b ∈ Sarkozy.RecordExpansion.Choice.support ω}, ∑ y : Slot → Xa b,
          |lawDensity (Sarkozy.RecordExpansion.entryFactor (N b) (D b) (ω b)) y|) *
        ((1 + u) * mainPrice ξ αbar changed a θ α * Y + Cdc * L ^ (-σ) * α) := by
  rw [envelopeLaw_eq_structuredEnergy N D ω μS hμS P F]
  have h := density_structured μS hμSp P _ _ gt changed hC0 ha hθ0 hθ1 hL hα hu hY hlow ξ αbar
    hξ hαbar hun αf hαf hch hmean hdc
  rw [totalVariation_selectedWeight] at h
  exact h

end Sarkozy.Structured
