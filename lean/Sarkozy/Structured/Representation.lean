module

public import Sarkozy.Structured.Bridge
public import Sarkozy.TensorMarginals

/-!
# Whole-group and split representations of structured energies

`Sarkozy/Structured/Bridge.lean` writes the tensor-law energies of
`Sarkozy.RecordExpansion` as structured energies on *split* labels:
- selected labels `X_E = ∀ b ∈ E, X_b`;
- a reference law `μ_𝒮` on `Slot → X_𝒮`, `X_𝒮 = ∀ b ∉ E, X_b`;
- inputs `G(z ⊔ ·)`.

WP-FI's layer and `Sarkozy/Structured/PaperSlot.lean` use the *whole-group*
representation instead:
- selected labels in `∀ b, X_b`;
- a law `μ_N` on the whole group;
- inputs `G(freeze(x, ·))`, which take the coordinates of `E` from the label `x`.

This file proves that the two representations give the same energy, and transfers
condition (b) of `def:record:structured-energy` between them.

* `freezeLabels E x y`: the coordinates of `E` from `x`, the others from `y`; for
  `X_b = ZMod (m b)` it is WP-FI's `coordinateFreeze` (`freezeLabels_eq_coordinateFreeze`).
* `liftWeight ρ κ`: the weight `x ↦ ρ(x|_E) κ(x|_𝒮)` on `Slot → ∀ b, X_b`, i.e. `ρ ⊗ κ`.
* `structuredEnergy_liftWeight`: if `μ_𝒮` is the `𝒮`-marginal of `μ_N`
  (`hmarg`), the whole-group energy with `ρ ⊗ κ` equals the split energy with `ρ`.
* `totalVariation_liftWeight`: `‖ρ ⊗ κ‖ = ‖ρ‖` for a probability law `κ`.
* `selectedMarginalsUniform_liftWeight`: if `|ρ|` has uniform one-slot marginals on `X_E`
  and `κ` has uniform one-slot marginals on `X_𝒮`, then `|ρ ⊗ κ|` has uniform one-slot
  marginals on the whole group; `uniformRest` is `κ = Unif(X_𝒮)^Slot`.
* `expect_tensor_restrict`: for a product `μ_N = ⊗_b μ_b` of atom laws, the
  `𝒮`-marginal is `⊗_{b ∉ E} μ_b`, the law of the outside atoms in the bridge
  (`tensor_weight`).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

variable {J : Type*} [Fintype J] [DecidableEq J] {Xa : J → Type*} [∀ b, Fintype (Xa b)]
  [∀ b, DecidableEq (Xa b)]

/-! ## Splitting a label -/

/-- The selected coordinates of a label. -/
def selLabel (E : Finset J) (x : ∀ b, Xa b) : ∀ b : {b // b ∈ E}, Xa b := fun b => x b

/-- The remaining coordinates of a label. -/
def restLabel (E : Finset J) (x : ∀ b, Xa b) : ∀ b : {b // b ∉ E}, Xa b := fun b => x b

/-- The coordinates of `E` from `x`, the others from `y`. -/
def freezeLabels (E : Finset J) (x y : ∀ b, Xa b) : ∀ b, Xa b :=
  fun b => if b ∈ E then x b else y b

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
theorem freezeLabels_eq_join (E : Finset J) (x y : ∀ b, Xa b) :
    freezeLabels E x y = joinLabels E (selLabel E x) (restLabel E y) := by
  funext b
  unfold freezeLabels joinLabels selLabel restLabel
  split_ifs <;> rfl

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
theorem join_sel_rest (E : Finset J) (x : ∀ b, Xa b) :
    joinLabels E (selLabel E x) (restLabel E x) = x := by
  funext b
  unfold joinLabels selLabel restLabel
  split_ifs <;> rfl

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
theorem sel_join (E : Finset J) (z : ∀ b : {b // b ∈ E}, Xa b) (w : ∀ b : {b // b ∉ E}, Xa b) :
    selLabel E (joinLabels E z w) = z := by
  funext b
  exact joinLabels_mem E z w b

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
theorem rest_join (E : Finset J) (z : ∀ b : {b // b ∈ E}, Xa b) (w : ∀ b : {b // b ∉ E}, Xa b) :
    restLabel E (joinLabels E z w) = w := by
  funext b
  exact joinLabels_not_mem E z w b

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
/-- The splitting of a label into selected and remaining coordinates. -/
def splitPoint (E : Finset J) :
    (∀ b, Xa b) ≃ (∀ b : {b // b ∈ E}, Xa b) × (∀ b : {b // b ∉ E}, Xa b) where
  toFun x := (selLabel E x, restLabel E x)
  invFun p := joinLabels E p.1 p.2
  left_inv x := join_sel_rest E x
  right_inv p := by
    ext1
    · exact sel_join E p.1 p.2
    · exact rest_join E p.1 p.2

omit [Fintype J] [∀ b, Fintype (Xa b)] [∀ b, DecidableEq (Xa b)] in
/-- The slotwise splitting `(Slot → ∀ b, X_b) ≃ (Slot → X_E) × (Slot → X_𝒮)`. -/
def splitSlots (E : Finset J) :
    (Slot → ∀ b, Xa b) ≃
      (Slot → ∀ b : {b // b ∈ E}, Xa b) × (Slot → ∀ b : {b // b ∉ E}, Xa b) where
  toFun x := (fun v => selLabel E (x v), fun v => restLabel E (x v))
  invFun p := fun v => joinLabels E (p.1 v) (p.2 v)
  left_inv x := by
    funext v
    exact join_sel_rest E (x v)
  right_inv p := by
    ext1
    · funext v
      exact sel_join E (p.1 v) (p.2 v)
    · funext v
      exact rest_join E (p.1 v) (p.2 v)

/-! ## The lifted weight and the energy identity -/

/-- The weight `ρ ⊗ κ` on whole-group labels: `x ↦ ρ(x|_E) κ(x|_𝒮)`. -/
noncomputable def liftWeight (E : Finset J) (ρ : (Slot → ∀ b : {b // b ∈ E}, Xa b) → ℝ)
    (κ : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b)) (x : Slot → ∀ b, Xa b) : ℝ :=
  ρ (fun v => selLabel E (x v)) * κ.weight (fun v => restLabel E (x v))

omit [∀ b, DecidableEq (Xa b)] in
/-- Sums over whole-group labels split into selected and remaining labels. -/
theorem sum_splitSlots (E : Finset J) (f : (Slot → ∀ b, Xa b) → ℝ) :
    ∑ x, f x = ∑ z : Slot → ∀ b : {b // b ∈ E}, Xa b, ∑ w : Slot → ∀ b : {b // b ∉ E}, Xa b,
      f (fun v => joinLabels E (z v) (w v)) := by
  rw [← (splitSlots E).symm.sum_comp, Fintype.sum_prod_type]
  rfl

omit [∀ b, DecidableEq (Xa b)] in
/-- **The two representations give the same energy**: if `μ_𝒮` is the `𝒮`-marginal of
`μ_N` and `κ` is a probability law, the whole-group energy with the weight `ρ ⊗ κ` and the
inputs `G(freeze(x, ·))` equals the split energy with `ρ` and the inputs `G(z ⊔ ·)`. -/
theorem structuredEnergy_liftWeight (E : Finset J)
    (μN : FiniteLaw (Slot → ∀ b, Xa b)) (μS : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    (hmarg : ∀ f : (Slot → ∀ b : {b // b ∉ E}, Xa b) → ℝ,
      μN.expect (fun y => f (fun v => restLabel E (y v))) = μS.expect f)
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (ρ : (Slot → ∀ b : {b // b ∈ E}, Xa b) → ℝ)
    (κ : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b)) (G : Ω → Slot → (∀ b, Xa b) → ℝ) :
    structuredEnergy μN P (liftWeight E ρ κ) (fun ω v x y => G ω v (freezeLabels E x y)) =
      structuredEnergy μS P ρ (fun ω v z w => G ω v (joinLabels E z w)) := by
  unfold structuredEnergy
  apply P.expect_congr
  intro ω
  -- the inner integral depends on the label only through its selected part
  have hinner : ∀ x : Slot → ∀ b, Xa b,
      multilinearIntegral (signedIntegral μN.weight)
          (fun v => fun y => G ω v (freezeLabels E (x v) y)) =
        multilinearIntegral (signedIntegral μS.weight)
          (fun v => fun w => G ω v (joinLabels E (selLabel E (x v)) w)) := by
    intro x
    unfold multilinearIntegral
    rw [← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral, ← hmarg]
    apply μN.expect_congr
    intro y
    apply prod_congr rfl
    intro v _
    change G ω v (freezeLabels E (x v) (y v)) =
      G ω v (joinLabels E (selLabel E (x v)) (restLabel E (y v)))
    rw [freezeLabels_eq_join]
  simp_rw [hinner]
  rw [sum_splitSlots E]
  apply sum_congr rfl
  intro z _
  unfold liftWeight
  simp only [sel_join, rest_join]
  rw [← sum_mul, ← mul_sum, κ.total, mul_one]

omit [∀ b, DecidableEq (Xa b)] in
/-- `‖ρ ⊗ κ‖ = ‖ρ‖`. -/
theorem totalVariation_liftWeight (E : Finset J) (ρ : (Slot → ∀ b : {b // b ∈ E}, Xa b) → ℝ)
    (κ : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b)) :
    totalVariation (liftWeight E ρ κ) = totalVariation ρ := by
  unfold totalVariation liftWeight
  rw [sum_splitSlots E]
  apply sum_congr rfl
  intro z _
  simp only [sel_join, rest_join, abs_mul, abs_of_nonneg (κ.nonneg _)]
  rw [← mul_sum, κ.total, mul_one]

/-- **Condition (b) for the lifted weight**: if `|ρ|` has uniform one-slot marginals on
`X_E` and `κ` has uniform one-slot marginals on `X_𝒮`, then `|ρ ⊗ κ|` has uniform one-slot
marginals on the whole group. -/
theorem selectedMarginalsUniform_liftWeight (E : Finset J)
    (ρ : (Slot → ∀ b : {b // b ∈ E}, Xa b) → ℝ) (hρ : selectedMarginalsUniform ρ)
    (κ : FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b))
    [Nonempty (∀ b : {b // b ∉ E}, Xa b)] (hκ : HasUniformMarginals κ) :
    selectedMarginalsUniform (liftWeight E ρ κ) := by
  intro v x0
  rw [totalVariation_liftWeight, sum_filter, sum_splitSlots E]
  -- `join(z v, w v) = x0` iff `z v = x0|_E` and `w v = x0|_𝒮`
  have hiff : ∀ (z : Slot → ∀ b : {b // b ∈ E}, Xa b) (w : Slot → ∀ b : {b // b ∉ E}, Xa b),
      ((fun v' => joinLabels E (z v') (w v')) v = x0) ↔
        (z v = selLabel E x0 ∧ w v = restLabel E x0) := by
    intro z w
    constructor
    · intro h
      exact ⟨by rw [← h, sel_join], by rw [← h, rest_join]⟩
    · rintro ⟨h1, h2⟩
      change joinLabels E (z v) (w v) = x0
      rw [h1, h2, join_sel_rest]
  have hterm : ∀ (z : Slot → ∀ b : {b // b ∈ E}, Xa b) (w : Slot → ∀ b : {b // b ∉ E}, Xa b),
      (if (fun v' => joinLabels E (z v') (w v')) v = x0 then
        |liftWeight E ρ κ (fun v' => joinLabels E (z v') (w v'))| else 0) =
      ((if z v = selLabel E x0 then |ρ z| else 0) *
        (κ.weight w * if w v = restLabel E x0 then 1 else 0)) := by
    intro z w
    unfold liftWeight
    simp only [sel_join, rest_join, abs_mul, abs_of_nonneg (κ.nonneg _)]
    by_cases h1 : z v = selLabel E x0
    · by_cases h2 : w v = restLabel E x0
      · rw [ite_eq_left ((hiff z w).mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, mul_one]
      · rw [ite_eq_right (fun h => h2 ((hiff z w).mp h).2), ite_eq_right h2, mul_zero,
          mul_zero]
    · rw [ite_eq_right (fun h => h1 ((hiff z w).mp h).1), ite_eq_right h1, zero_mul]
  simp_rw [hterm]
  simp_rw [← mul_sum]
  rw [← sum_mul]
  -- the two marginals
  have hz : ∑ z : Slot → ∀ b : {b // b ∈ E}, Xa b, (if z v = selLabel E x0 then |ρ z| else 0) =
      totalVariation ρ / (Fintype.card (∀ b : {b // b ∈ E}, Xa b) : ℝ) := by
    rw [← sum_filter]
    exact hρ v (selLabel E x0)
  have hw : ∑ w : Slot → ∀ b : {b // b ∉ E}, Xa b,
      κ.weight w * (if w v = restLabel E x0 then (1 : ℝ) else 0) =
      (Fintype.card (∀ b : {b // b ∉ E}, Xa b) : ℝ)⁻¹ := by
    have h := hκ v (fun y => if y = restLabel E x0 then (1 : ℝ) else 0)
    rw [FiniteLaw.expect_uniform] at h
    unfold FiniteLaw.expect at h
    rw [h, Fintype.sum_ite_eq']
    ring
  rw [hz, hw]
  have hcard : (Fintype.card (∀ b, Xa b) : ℝ) =
      (Fintype.card (∀ b : {b // b ∈ E}, Xa b) : ℝ) *
        (Fintype.card (∀ b : {b // b ∉ E}, Xa b) : ℝ) := by
    rw [Fintype.card_congr (splitPoint E), Fintype.card_prod]
    push_cast
    ring
  rw [hcard]
  ring

/-- The uniform law on `Slot → X_𝒮`, a product of uniform one-slot laws. -/
noncomputable def uniformRest (E : Finset J) [∀ b, Nonempty (Xa b)] :
    FiniteLaw (Slot → ∀ b : {b // b ∉ E}, Xa b) :=
  FiniteLaw.pi fun _ => FiniteLaw.uniform _

omit [∀ b, DecidableEq (Xa b)] in
theorem uniformRest_marginals (E : Finset J) [∀ b, Nonempty (Xa b)] :
    HasUniformMarginals (uniformRest (Xa := Xa) E) := by
  intro v f
  exact FiniteLaw.expect_pi_coordinate _ v f

/-- Condition (b) for `ρ ⊗ Unif(X_𝒮)`. -/
theorem selectedMarginalsUniform_liftWeight_uniform (E : Finset J) [∀ b, Nonempty (Xa b)]
    (ρ : (Slot → ∀ b : {b // b ∈ E}, Xa b) → ℝ) (hρ : selectedMarginalsUniform ρ) :
    selectedMarginalsUniform (liftWeight E ρ (uniformRest E)) :=
  selectedMarginalsUniform_liftWeight E ρ hρ _ (uniformRest_marginals E)

/-! ## Products of atom laws -/

omit [Fintype J] in
/-- The weight of a product of atom laws. -/
theorem tensor_weight {K : Type*} [Fintype K] [DecidableEq K] {Y : K → Type*}
    [∀ b, Fintype (Y b)] [∀ b, DecidableEq (Y b)] (μ : ∀ b, FiniteLaw (Slot → Y b))
    (w : Slot → ∀ b, Y b) :
    (FiniteLaw.tensor μ).weight w = ∏ b, (μ b).weight (fun v => w v b) := by
  change lawDensity (tensorLaw fun b => signedIntegral (μ b).weight) w = _
  unfold lawDensity
  rw [Sarkozy.RecordExpansion.tensorLaw_apply]
  rw [Finset.sum_eq_single (fun b v => w v b)]
  · rw [ite_eq_left rfl, mul_one]
    apply prod_congr rfl
    intro b _
    unfold lawDensity signedIntegral
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq']
  · intro z _ hz
    have hne : (fun v b => z b v) ≠ w := by
      intro h
      apply hz
      funext b v
      exact congrFun (congrFun h v) b
    rw [ite_eq_right hne, mul_zero]
  · intro h
    exact absurd (mem_univ _) h

/-- **The `𝒮`-marginal of a product of atom laws** is the product of the laws of the
atoms outside `E`. -/
theorem expect_tensor_restrict (E : Finset J) (μ : ∀ b, FiniteLaw (Slot → Xa b))
    (f : (Slot → ∀ b : {b // b ∉ E}, Xa b) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun y => f (fun v => restLabel E (y v))) =
      (FiniteLaw.tensor fun b : {b // b ∉ E} => μ b).expect f := by
  unfold FiniteLaw.expect
  rw [sum_splitSlots E]
  simp only [rest_join]
  simp_rw [tensor_weight]
  have hsplit : ∀ (z : Slot → ∀ b : {b // b ∈ E}, Xa b) (w : Slot → ∀ b : {b // b ∉ E}, Xa b),
      (∏ b, (μ b).weight (fun v => joinLabels E (z v) (w v) b)) =
        (∏ b : {b // b ∈ E}, (μ b).weight (fun v => z v b)) *
          ∏ b : {b // b ∉ E}, (μ b).weight (fun v => w v b) := by
    intro z w
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun b => b ∈ E)]
    congr 1
    · refine Finset.prod_congr (by congr 1; exact Subsingleton.elim _ _) (fun b _ => ?_)
      congr 1
      funext v
      exact joinLabels_mem E (z v) (w v) b
    · refine Finset.prod_congr rfl (fun b _ => ?_)
      congr 1
      funext v
      exact joinLabels_not_mem E (z v) (w v) b
  simp_rw [hsplit]
  -- the selected atoms integrate to one
  have hone : ∑ z : Slot → ∀ b : {b // b ∈ E}, Xa b,
      ∏ b : {b // b ∈ E}, (μ b).weight (fun v => z v b) = 1 := by
    rw [← (transposeLabels E).symm.sum_comp]
    change ∑ i : (∀ b : {b // b ∈ E}, Slot → Xa b), ∏ b : {b // b ∈ E}, (μ b).weight (i b) = 1
    rw [← Fintype.prod_sum (fun (b : {b // b ∈ E}) (y : Slot → Xa b) => (μ b).weight y)]
    simp only [(μ _).total, prod_const_one]
  simp_rw [mul_assoc, ← mul_sum]
  rw [← sum_mul, hone, one_mul]

end Sarkozy.Structured
