module

public import Sarkozy.PaperFrame.TailMarginal
public import Sarkozy.Functional.FibreCount

@[expose] public section

/-!
# The square-step maps preserve the reference energy (`lem:record:fibre-scale`(b), (R3))

The fibre-energy argument (`Sarkozy.SignedHolder.fibre_energy_le`,
`Comparison/FibreEnergy.lean`) needs `Z(h_j ∘ T_j) = Z(h_j)` for the maps
`T_j(y) = R⁻¹(y − c_I − c_j)` of the square-step model (`lem:record:fibre-scale`(b): "each
`T_j` is a map of the form in (R3)"). This module proves it for the comparison worker's
reference law `paperLaw = μ₀ ⊗ ⊗_p μ_p`, from the square-affine invariance (R3) of the atom
laws: `μ₀` under the coordinatewise maps `x ↦ a x + b` with square units `a`, and every
`μ_q` under `z ↦ a z + b` with `a` a square unit modulo `q`.

* `weight_map_equiv`, `tensor_map_invariant`, `paperLaw_map_invariant`: invariance of a
  tensor law and of `paperLaw` under slotwise coordinatewise bijections preserving each
  factor.
* `energy_stepMap_invariant`: `Z_{paperLaw}(h_j ∘ T_j) = Z_{paperLaw}(h_j)` for the piece
  `h_j = stepLift …` and `T_j = stepMap …` read on `X₀ × X_tail`. Since `h_j` does not depend
  on the coordinates of `E`, `T_j` may be replaced by `stepMapOff` (identity on `E`), whose
  multipliers are `1` on `E` and the square unit `R⁻¹` off `E`.
-/

open Finset Function
open scoped BigOperators ComplexConjugate

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Comparison

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Invariance under a slotwise bijection, in terms of the weights. -/
theorem weight_map_equiv {G : Type*} [Fintype G] [DecidableEq G] (ν : FiniteLaw (V → G))
    (φ : G ≃ G) (hinv : ∀ F : (V → G) → ℝ, ν.expect (fun z => F (fun v => φ (z v))) = ν.expect F)
    (y : V → G) : ν.weight (fun v => φ.symm (y v)) = ν.weight y := by
  have h := hinv (fun z => if z = y then 1 else 0)
  simp only [FiniteLaw.expect, mul_ite, mul_one, mul_zero] at h
  rw [sum_ite_eq' univ y, ite_eq_left (mem_univ y)] at h
  rw [Finset.sum_eq_single (fun v => φ.symm (y v))] at h
  · simpa using h
  · intro z _ hz
    have : (fun v => φ (z v)) ≠ y := by
      intro h'
      apply hz
      funext v
      rw [← congrFun h' v]
      simp
    simp [this]
  · intro h'
    exact absurd (mem_univ _) h'

/-- A tensor of laws, each invariant under a slotwise bijection of its alphabet, is invariant
under the product of these bijections at every slot. -/
theorem tensor_map_invariant {I : Type*} [Fintype I] [DecidableEq I] {G : I → Type*}
    [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] (μ : ∀ i, FiniteLaw (V → G i))
    (φ : ∀ i, G i ≃ G i)
    (hinv : ∀ i (F : (V → G i) → ℝ), (μ i).expect (fun z => F (fun v => φ i (z v))) = (μ i).expect F)
    (F : (V → ∀ i, G i) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun w => F (fun v i => φ i (w v i))) =
      (FiniteLaw.tensor μ).expect F := by
  rw [tensor_expect_sum, tensor_expect_sum]
  let σ : (∀ i, V → G i) ≃ (∀ i, V → G i) :=
    { toFun := fun z i v => φ i (z i v)
      invFun := fun z i v => (φ i).symm (z i v)
      left_inv := fun z => by funext i v; simp
      right_inv := fun z => by funext i v; simp }
  refine Fintype.sum_equiv σ _ _ (fun z => ?_)
  have hw : ∀ i, (μ i).weight (z i) = (μ i).weight (σ z i) := by
    intro i
    have := weight_map_equiv (μ i) (φ i) (hinv i) (σ z i)
    rw [← this]
    congr 1
    funext v
    simp [σ]
  rw [prod_congr rfl (fun i _ => hw i)]
  rfl

end General

section PaperLaw

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- `paperLaw = μ₀ ⊗ ⊗_q μ_q` is invariant under slotwise maps acting by a bijection on the
prefix and by bijections on the tail coordinates, if each atom law is invariant under its
bijection. -/
theorem paperLaw_map_invariant (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ)
    (φ₀ : ResidueSpace m₀ ≃ ResidueSpace m₀) (φt : ∀ j : J L, ZMod (p L j) ≃ ZMod (p L j))
    (h₀ : ∀ F : (Slot → ResidueSpace m₀) → ℝ, μ₀.expect (fun z => F (fun v => φ₀ (z v))) = μ₀.expect F)
    (hq : ∀ (j : J L) (F : (Slot → ZMod (p L j)) → ℝ),
      (μp (p L j)).expect (fun z => F (fun v => φt j (z v))) = (μp (p L j)).expect F)
    (F : (Slot → ResidueSpace m₀ × ResidueSpace (p L)) → ℝ) :
    (paperLaw m₀ p μ₀ μp L).expect (fun w => F (fun v => (φ₀ (w v).1, fun j => φt j ((w v).2 j)))) =
      (paperLaw m₀ p μ₀ μp L).expect F := by
  unfold paperLaw
  rw [FiniteLaw.expect_slotProduct, FiniteLaw.expect_slotProduct]
  have htail : ∀ z : Slot → ResidueSpace m₀,
      (primeTailLaw p μp L).expect (fun t => F (fun v => (φ₀ (z v), fun j => φt j (t v j)))) =
        (primeTailLaw p μp L).expect (fun t => F (fun v => (φ₀ (z v), t v))) := by
    intro z
    unfold primeTailLaw
    exact tensor_map_invariant (fun j : J L => μp (p L j)) φt (fun j F => hq j F)
      (fun t => F (fun v => (φ₀ (z v), t v)))
  simp only [htail]
  exact h₀ (fun z => (primeTailLaw p μp L).expect (fun t => F (fun v => (z v, t v))))

/-- The affine bijection `x ↦ a x + b` of `ℤ/qℤ` for a unit `a`. -/
def affineEquiv {q : ℕ} (a : (ZMod q)ˣ) (b : ZMod q) : ZMod q ≃ ZMod q where
  toFun x := (a : ZMod q) * x + b
  invFun x := ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * (x - b)
  left_inv x := by
    simp only [add_sub_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    simp only [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]

/-- The coordinatewise affine bijection `x ↦ a x + b` of `∏_i ℤ/m_iℤ`. -/
def piAffineEquiv {I : Type*} (m : I → ℕ) (a : ∀ i, (ZMod (m i))ˣ) (b : ResidueSpace m) :
    ResidueSpace m ≃ ResidueSpace m where
  toFun x i := (a i : ZMod (m i)) * x i + b i
  invFun x i := ((a i)⁻¹ : (ZMod (m i))ˣ) * (x i - b i)
  left_inv x := by
    funext i
    simp only [add_sub_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    funext i
    simp only [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]

/-- `paperLaw` is invariant under the slotwise coordinatewise square-affine maps of
`X₀ × X_tail`, if `μ₀` and every `μ_q` are square-affine invariant ((R3)). -/
theorem paperLaw_affine_invariant (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hμ₀ : ∀ (a : ∀ i, (ZMod (m₀ i))ˣ) (b : ResidueSpace m₀),
      (∀ i, IsSquare ((a i : ZMod (m₀ i)))) → ∀ F : (Slot → ResidueSpace m₀) → ℝ,
        μ₀.expect (fun z => F (fun v => piAffineEquiv m₀ a b (z v))) = μ₀.expect F)
    (hμp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
      ∀ F : (Slot → ZMod q) → ℝ,
        (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F)
    (L : ℕ) (a₀ : ∀ i, (ZMod (m₀ i))ˣ) (b₀ : ResidueSpace m₀)
    (ha₀ : ∀ i, IsSquare ((a₀ i : ZMod (m₀ i))))
    (at' : ∀ j : J L, (ZMod (p L j))ˣ) (bt : ResidueSpace (p L))
    (hat : ∀ j, IsSquare ((at' j : ZMod (p L j))))
    (F : (Slot → ResidueSpace m₀ × ResidueSpace (p L)) → ℝ) :
    (paperLaw m₀ p μ₀ μp L).expect (fun w => F (fun v =>
        (piAffineEquiv m₀ a₀ b₀ (w v).1, fun j => affineEquiv (at' j) (bt j) ((w v).2 j)))) =
      (paperLaw m₀ p μ₀ μp L).expect F :=
  paperLaw_map_invariant m₀ p μ₀ μp L (piAffineEquiv m₀ a₀ b₀) (fun j => affineEquiv (at' j) (bt j))
    (hμ₀ a₀ b₀ ha₀) (fun j F => hμp (p L j) (at' j) (bt j) (hat j) F) F

end PaperLaw

/-! ### The square-step maps -/

section StepMaps

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The multiplier of `stepMapOff` at a coordinate: `1` on `E`, the unit `R⁻¹` off `E`. -/
noncomputable def stepUnit (L : ℕ) (E : Finset (J₀ ⊕ J L)) (R : ℕ)
    (hcop : ∀ k ∉ E, R.Coprime (joinModuli m₀ (p L) k)) (k : J₀ ⊕ J L) :
    (ZMod (joinModuli m₀ (p L) k))ˣ :=
  if hk : k ∈ E then 1 else (ZMod.unitOfCoprime R (hcop k hk))⁻¹

/-- The translation of `stepMapOff` at a coordinate. -/
noncomputable def stepShift (L : ℕ) (E : Finset (J₀ ⊕ J L)) (R : ℕ) (c jj : ℤ)
    (k : J₀ ⊕ J L) : ZMod (joinModuli m₀ (p L) k) :=
  if k ∈ E then 0 else -((R : ZMod (joinModuli m₀ (p L) k))⁻¹ *
    ((c + (jj - R) : ℤ) : ZMod (joinModuli m₀ (p L) k)))

omit [Fintype J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)] [∀ L j, NeZero (p L j)] in
theorem stepUnit_val (L : ℕ) (E : Finset (J₀ ⊕ J L)) (R : ℕ)
    (hcop : ∀ k ∉ E, R.Coprime (joinModuli m₀ (p L) k)) (k : J₀ ⊕ J L) (hk : k ∉ E) :
    ((stepUnit m₀ p L E R hcop k : (ZMod (joinModuli m₀ (p L) k))ˣ) : ZMod (joinModuli m₀ (p L) k)) =
      (R : ZMod (joinModuli m₀ (p L) k))⁻¹ := by
  unfold stepUnit
  rw [dite_eq_right hk, ← ZMod.inv_coe_unit, ZMod.coe_unitOfCoprime]

omit [Fintype J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)] [∀ L j, NeZero (p L j)] in
theorem stepUnit_isSquare (L : ℕ) (E : Finset (J₀ ⊕ J L)) {R r : ℕ} (hR : R = r ^ 2)
    (hcop : ∀ k ∉ E, R.Coprime (joinModuli m₀ (p L) k)) (k : J₀ ⊕ J L) :
    IsSquare ((stepUnit m₀ p L E R hcop k : (ZMod (joinModuli m₀ (p L) k))ˣ) :
      ZMod (joinModuli m₀ (p L) k)) := by
  by_cases hk : k ∈ E
  · unfold stepUnit
    rw [dite_eq_left hk, Units.val_one]
    exact ⟨1, (mul_one 1).symm⟩
  · rw [stepUnit_val m₀ p L E R hcop k hk]
    exact (stepMap_squareUnit (joinModuli m₀ (p L)) hR k (hcop k hk)).2

omit [Fintype J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)] [∀ L j, NeZero (p L j)] in
/-- `stepMapOff` is the coordinatewise affine map with the multipliers `stepUnit` and the
translations `stepShift`. -/
theorem stepMapOff_eq_affine (L : ℕ) (E : Finset (J₀ ⊕ J L)) (R : ℕ)
    (hcop : ∀ k ∉ E, R.Coprime (joinModuli m₀ (p L) k)) (c jj : ℤ)
    (y : ResidueSpace (joinModuli m₀ (p L))) :
    stepMapOff (joinModuli m₀ (p L)) E R c jj y =
      piAffineEquiv (joinModuli m₀ (p L)) (stepUnit m₀ p L E R hcop) (stepShift m₀ p L E R c jj) y := by
  funext k
  change (if k ∈ E then y k else stepMap (joinModuli m₀ (p L)) R c jj y k) =
    (stepUnit m₀ p L E R hcop k : ZMod (joinModuli m₀ (p L) k)) * y k + stepShift m₀ p L E R c jj k
  by_cases hk : k ∈ E
  · rw [ite_eq_left hk]
    unfold stepUnit stepShift
    rw [dite_eq_left hk, ite_eq_left hk, Units.val_one, one_mul, add_zero]
  · rw [ite_eq_right hk, stepUnit_val m₀ p L E R hcop k hk, stepMap_apply]
    unfold stepShift
    rw [ite_eq_right hk]
    ring

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)]
  [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
/-- The affine map on the joined group, read on `X₀ × X_tail`. -/
theorem splitEquiv_piAffine (L : ℕ) (a : ∀ k, (ZMod (joinModuli m₀ (p L) k))ˣ)
    (b : ResidueSpace (joinModuli m₀ (p L))) (x : ResidueSpace m₀ × ResidueSpace (p L)) :
    splitEquiv m₀ (p L) (piAffineEquiv (joinModuli m₀ (p L)) a b ((splitEquiv m₀ (p L)).symm x)) =
      (piAffineEquiv m₀ (fun i => a (Sum.inl i)) (fun i => b (Sum.inl i)) x.1,
        fun j => affineEquiv (a (Sum.inr j)) (b (Sum.inr j)) (x.2 j)) := rfl

/-- On `X₀ × X_tail`, `h_j ∘ T_j = h_j ∘ Φ` with `Φ` the slotwise square-affine map of
`stepMapOff` (`h_j` does not depend on the coordinates of `E`). -/
theorem stepLift_stepMap_split (L : ℕ) (E : Finset (J₀ ⊕ J L)) (R : ℕ)
    (hcop : ∀ k ∉ E, R.Coprime (joinModuli m₀ (p L) k)) (c jj : ℤ) (Q' : ℝ) (B : Finset ℤ)
    (n : ℕ) (x : ResidueSpace m₀ × ResidueSpace (p L)) :
    (stepLift (joinModuli m₀ (p L)) E Q' B n ((splitEquiv m₀ (p L)).symm
        (splitEquiv m₀ (p L) (stepMap (joinModuli m₀ (p L)) R c jj
          ((splitEquiv m₀ (p L)).symm x))))).re =
      (stepLift (joinModuli m₀ (p L)) E Q' B n ((splitEquiv m₀ (p L)).symm
        (piAffineEquiv m₀ (fun i => stepUnit m₀ p L E R hcop (Sum.inl i))
            (fun i => stepShift m₀ p L E R c jj (Sum.inl i)) x.1,
          fun j => affineEquiv (stepUnit m₀ p L E R hcop (Sum.inr j))
            (stepShift m₀ p L E R c jj (Sum.inr j)) (x.2 j)))).re := by
  rw [AddEquiv.symm_apply_apply]
  rw [stepLift_congr (joinModuli m₀ (p L)) (E := E) (Q' := Q') B n
    (y := stepMap (joinModuli m₀ (p L)) R c jj ((splitEquiv m₀ (p L)).symm x))
    (y' := stepMapOff (joinModuli m₀ (p L)) E R c jj ((splitEquiv m₀ (p L)).symm x))
    (fun k hk => by simp [stepMapOff, hk])]
  rw [stepMapOff_eq_affine m₀ p L E R hcop c jj]
  have hxy : piAffineEquiv (joinModuli m₀ (p L)) (stepUnit m₀ p L E R hcop)
      (stepShift m₀ p L E R c jj) ((splitEquiv m₀ (p L)).symm x) =
      (splitEquiv m₀ (p L)).symm
        (piAffineEquiv m₀ (fun i => stepUnit m₀ p L E R hcop (Sum.inl i))
            (fun i => stepShift m₀ p L E R c jj (Sum.inl i)) x.1,
          fun j => affineEquiv (stepUnit m₀ p L E R hcop (Sum.inr j))
            (stepShift m₀ p L E R c jj (Sum.inr j)) (x.2 j)) := by
    funext k
    match k with
    | Sum.inl i => rfl
    | Sum.inr j => rfl
  exact congrArg (fun y => (stepLift (joinModuli m₀ (p L)) E Q' B n y).re) hxy

/-- **`T_j` preserves the reference energy** (`lem:record:fibre-scale`(b), (R3)): with the
square-affine invariance of the atom laws, `Z_{paperLaw}(h_j ∘ T_j) = Z_{paperLaw}(h_j)` for
the square-step piece `h_j = stepLift …` and the map `T_j = stepMap …`, both read on
`X₀ × X_tail`. This is the hypothesis `hinv` of `Sarkozy.SignedHolder.fibre_energy_le`. -/
theorem energy_stepMap_invariant (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hμ₀ : ∀ (a : ∀ i, (ZMod (m₀ i))ˣ) (b : ResidueSpace m₀),
      (∀ i, IsSquare ((a i : ZMod (m₀ i)))) → ∀ F : (Slot → ResidueSpace m₀) → ℝ,
        μ₀.expect (fun z => F (fun v => piAffineEquiv m₀ a b (z v))) = μ₀.expect F)
    (hμp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
      ∀ F : (Slot → ZMod q) → ℝ,
        (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F)
    (L : ℕ) (E : Finset (J₀ ⊕ J L)) {R r : ℕ} (hR : R = r ^ 2)
    (hcop : ∀ k ∉ E, R.Coprime (joinModuli m₀ (p L) k)) (c jj : ℤ) (Q' : ℝ) (B : Finset ℤ)
    (n : ℕ) :
    diagonalIntegral (signedIntegral (paperLaw m₀ p μ₀ μp L).weight)
        ((fun x => (stepLift (joinModuli m₀ (p L)) E Q' B n ((splitEquiv m₀ (p L)).symm x)).re) ∘
          (fun x => splitEquiv m₀ (p L)
            (stepMap (joinModuli m₀ (p L)) R c jj ((splitEquiv m₀ (p L)).symm x)))) =
      diagonalIntegral (signedIntegral (paperLaw m₀ p μ₀ μp L).weight)
        (fun x => (stepLift (joinModuli m₀ (p L)) E Q' B n ((splitEquiv m₀ (p L)).symm x)).re) := by
  unfold diagonalIntegral multilinearIntegral
  rw [← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral]
  simp only [Function.comp_apply]
  simp_rw [stepLift_stepMap_split m₀ p L E R hcop c jj Q' B n]
  exact paperLaw_affine_invariant m₀ p μ₀ μp hμ₀ hμp L _ _
    (fun i => stepUnit_isSquare m₀ p L E hR hcop (Sum.inl i)) _ _
    (fun j => stepUnit_isSquare m₀ p L E hR hcop (Sum.inr j))
    (fun z => ∏ v, (stepLift (joinModuli m₀ (p L)) E Q' B n ((splitEquiv m₀ (p L)).symm (z v))).re)

end StepMaps

end Sarkozy.PaperFrame
