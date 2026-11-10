module

public import Sarkozy.Construction.CliqueLaw

/-!
# Square-affine invariance of the square-clique law (`lem:frontier:iidlocal`(ii))

`paper/sections/19_prefix.tex`. For a unit square `σ` and any `τ` of `ℤ/p^{2ℓ}ℤ`, the square-clique
law is invariant under the simultaneous map `z ↦ (σ z_v + τ)_v` (`cliqueLaw_invariant`): this is
(R3) at a clique atom. The proof substitutes the labels and reindexes the affine data
`(d, s, c) ↦ (d, σ s, σ c + τ)`, a bijection of the data set.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy

variable {p : ℕ} [Fact p.Prime] (ℓ : ℕ)

local notation "Rℓ" => ZMod (p ^ (2 * ℓ))

theorem unitSquares_mul {σ s : Rℓ} (hσ : σ ∈ unitSquares p ℓ) (hs : s ∈ unitSquares p ℓ) :
    σ * s ∈ unitSquares p ℓ := by
  obtain ⟨u, _, rfl⟩ := mem_image.mp hσ
  obtain ⟨t, _, rfl⟩ := mem_image.mp hs
  exact mem_image.mpr ⟨u * t, mem_univ _, by push_cast; ring⟩

/-- The unit square `σ` as a unit, and the inverse of a unit square is a unit square. -/
theorem unitSquares_inv {σ : Rℓ} (hσ : σ ∈ unitSquares p ℓ) :
    ∃ σ' ∈ unitSquares p ℓ, σ' * σ = 1 := by
  obtain ⟨u, _, rfl⟩ := mem_image.mp hσ
  refine ⟨((u⁻¹ ^ 2 : Rℓˣ) : Rℓ), mem_image.mpr ⟨u⁻¹, mem_univ _, rfl⟩, ?_⟩
  rw [← Units.val_mul]
  simp

/-- The reindexing `(d, s, c) ↦ (d, σ s, σ c + τ)` of the affine data. -/
noncomputable def affineShift {σ : Rℓ} (hσ : σ ∈ unitSquares p ℓ) (τ : Rℓ) :
    AffineData (R := Rℓ) (CliqueData p ℓ) (unitSquares p ℓ) ≃
      AffineData (R := Rℓ) (CliqueData p ℓ) (unitSquares p ℓ) where
  toFun q := (q.1, ⟨σ * q.2.1, unitSquares_mul ℓ hσ q.2.1.2⟩, σ * q.2.2 + τ)
  invFun q := (q.1, ⟨(unitSquares_inv ℓ hσ).choose * q.2.1,
      unitSquares_mul ℓ (unitSquares_inv ℓ hσ).choose_spec.1 q.2.1.2⟩,
      (unitSquares_inv ℓ hσ).choose * (q.2.2 - τ))
  left_inv q := by
    obtain ⟨_, h⟩ := (unitSquares_inv ℓ hσ).choose_spec
    rcases q with ⟨d, s, c⟩
    simp only [Prod.mk.injEq, true_and]
    refine ⟨Subtype.ext ?_, ?_⟩
    · change (unitSquares_inv ℓ hσ).choose * (σ * s) = s
      rw [← mul_assoc, h, one_mul]
    · rw [add_sub_cancel_right, ← mul_assoc, h, one_mul]
  right_inv q := by
    obtain ⟨_, h⟩ := (unitSquares_inv ℓ hσ).choose_spec
    have h' : σ * (unitSquares_inv ℓ hσ).choose = 1 := (mul_comm _ _).trans h
    rcases q with ⟨d, s, c⟩
    simp only [Prod.mk.injEq, true_and]
    refine ⟨Subtype.ext ?_, ?_⟩
    · change σ * ((unitSquares_inv ℓ hσ).choose * s) = s
      rw [← mul_assoc, h', one_mul]
    · rw [← mul_assoc, h', one_mul, sub_add_cancel]

/-- **(R3) at a clique atom**: the square-clique law is invariant under `z ↦ (σ z_v + τ)_v` for
every unit square `σ` and every `τ`. -/
theorem cliqueLaw_invariant {σ : Rℓ} (hσ : σ ∈ unitSquares p ℓ) (τ : Rℓ)
    (f : (Slot → Rℓ) → ℝ) :
    (cliqueLaw p ℓ).expect (fun z => f (fun v => σ * z v + τ)) = (cliqueLaw p ℓ).expect f := by
  obtain ⟨σ', hσ'S, hσ'⟩ := unitSquares_inv ℓ hσ
  have hσσ' : σ * σ' = 1 := (mul_comm _ _).trans hσ'
  -- the affine map `h` and its inverse on labels
  let h : Rℓ ≃ Rℓ :=
    { toFun := fun x => σ * x + τ
      invFun := fun x => σ' * (x - τ)
      left_inv := fun x => by
        change σ' * (σ * x + τ - τ) = x
        rw [add_sub_cancel_right, ← mul_assoc, hσ', one_mul]
      right_inv := fun x => by
        change σ * (σ' * (x - τ)) + τ = x
        rw [← mul_assoc, hσσ', one_mul, sub_add_cancel] }
  have hS : Nonempty (unitSquares p ℓ) :=
    ⟨⟨(unitSquares_nonempty p ℓ).choose, (unitSquares_nonempty p ℓ).choose_spec⟩⟩
  unfold cliqueLaw affineChamberLaw
  rw [expect_chamberIidLaw, expect_chamberIidLaw]
  -- substitute the labels: `y ↦ h ∘ y`
  have hinj : ∀ (s : Rℓ), s ∈ unitSquares p ℓ → ∀ c : Rℓ,
      Function.Injective fun x : Rℓ => s * x + c := by
    intro s hs c x x' hxx
    have hu := unitSquares_isUnit p ℓ s hs
    have : s * x = s * x' := by simpa using hxx
    exact hu.mul_left_cancel this
  have hfactor : ∀ q (x : Rℓ),
      (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q).weight x =
      (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ)
        (affineShift ℓ hσ τ q)).weight (h x) := by
    intro q x
    set q' := affineShift ℓ hσ τ q
    have hq1 : q'.1 = q.1 := rfl
    have hq2 : (q'.2.1 : Rℓ) = σ * q.2.1 := rfl
    have hq3 : q'.2.2 = σ * q.2.2 + τ := rfl
    have hmem : (x ∈ (clique p ℓ q.1).image fun y => (q.2.1 : Rℓ) * y + q.2.2) ↔
        (h x ∈ (clique p ℓ q'.1).image fun y => (q'.2.1 : Rℓ) * y + q'.2.2) := by
      rw [hq1, hq2, hq3]
      simp only [mem_image]
      constructor
      · rintro ⟨y, hy, hxe⟩
        exact ⟨y, hy, by rw [← hxe]; simp only [h, Equiv.coe_fn_mk]; ring⟩
      · rintro ⟨y, hy, hxe⟩
        refine ⟨y, hy, ?_⟩
        have : h ((q.2.1 : Rℓ) * y + q.2.2) = h x := by
          simp only [h, Equiv.coe_fn_mk] at hxe ⊢; rw [← hxe]; ring
        exact h.injective this
    have hcard : ((clique p ℓ q.1).image fun y => (q.2.1 : Rℓ) * y + q.2.2).card =
        ((clique p ℓ q'.1).image fun y => (q'.2.1 : Rℓ) * y + q'.2.2).card := by
      rw [card_image_of_injective _ (hinj _ q.2.1.2 _),
        card_image_of_injective _ (hinj _ q'.2.1.2 _), hq1]
    unfold affineLabelLaw uniformOn
    by_cases hx : x ∈ (clique p ℓ q.1).image fun y => (q.2.1 : Rℓ) * y + q.2.2
    · have hx' := hmem.mp hx
      simp only [hx, hx', ↓reduceIte, hcard]
    · have hx' : h x ∉ (clique p ℓ q'.1).image fun y => (q'.2.1 : Rℓ) * y + q'.2.2 :=
        fun h' => hx (hmem.mpr h')
      simp only [hx, hx', ↓reduceIte]
  have hsub : ∀ q, ∑ y : Chamber → Rℓ,
      (∏ i, (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q).weight (y i)) *
        f (fun v => σ * (y ∘ firstChamber) v + τ) =
      ∑ y : Chamber → Rℓ,
      (∏ i, (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ)
        (affineShift ℓ hσ τ q)).weight (y i)) * f (y ∘ firstChamber) := by
    intro q
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl Chamber) h) _ _ (fun y => ?_)
    simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply,
      CompTriple.comp_eq]
    congr 1
    exact prod_congr rfl fun i _ => hfactor q (y i)
  simp_rw [hsub]
  -- reindex the affine data
  exact Fintype.sum_equiv (affineShift ℓ hσ τ) _ _ (fun _ => rfl)

end Sarkozy
