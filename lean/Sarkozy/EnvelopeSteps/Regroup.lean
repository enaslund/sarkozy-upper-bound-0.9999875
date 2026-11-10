module

public import Sarkozy.EnvelopeSteps.JointEnergy

@[expose] public section

/-!
# Regrouping the blocks: the joint energy of a tensor is the energy of the product law

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 1 (the selected measure
`ζ_ω = ⊗_{𝔅 ∈ X} ζ_{ω(𝔅),𝔅}` on the labels of `X`, against `λ_{-X}` outside); B10's
`ClassInputsPaper.term_eq_support`.

The joint energies of `JointEnergy.lean` pair a law on the labels `∀ j : S, X j` of a block set
`S` with a law on the labels `∀ j : Sᶜ, X j` outside. If the inside law is itself a tensor of
per-block laws, the joint energy is the ordinary energy of the product law over all blocks:

* `lawDensity_tensorLaw`: the point masses of a tensor law are the products of the point masses;
* `merge`: the joint label of the two groups as a label of all blocks;
* **`jointEnergy_tensor`**:
  `Y_{(⊗_{j ∈ S} L_j) ⊗ (⊗_{j ∉ S} L_j)}[F ∘ merge] = Y_{⊗_j L_j}[F]`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The point masses of a tensor law** are the products of the point masses of its factors. -/
theorem lawDensity_tensorLaw {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*}
    [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (y : V → ∀ j, X j) :
    lawDensity (tensorLaw L) y = ∏ j, lawDensity (L j) (fun v => y v j) := by
  change (∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) *
    (if (fun v j => z j v) = y then (1 : ℝ) else 0)) = _
  rw [Fintype.sum_eq_single (fun j v => y v j)]
  · simp
  · intro z hz
    have hne : (fun v j => z j v) ≠ y := by
      intro h
      apply hz
      funext j v
      rw [← h]
    simp only [hne, ↓reduceIte, mul_zero]

variable {J : Type u} [Fintype J] [DecidableEq J] {X : J → Type u} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)] (S : Finset J)

/-- The labels of the blocks of `S`. -/
abbrev InLabel : Type u := ∀ j : {j // j ∈ S}, X j.1

/-- The labels of the blocks outside `S`. -/
abbrev OutLabel : Type u := ∀ j : {j // j ∉ S}, X j.1

/-- The label of all blocks from the labels of the two groups. -/
def merge (z : ∀ t, pairFam (InLabel (X := X) S) (OutLabel (X := X) S) t) : ∀ j, X j :=
  fun j => if h : j ∈ S then (z true : InLabel S) ⟨j, h⟩ else (z false : OutLabel S) ⟨j, h⟩

/-- Splitting a configuration of all blocks into the two groups. -/
def splitCfg (y : ∀ j, V → X j) :
    ∀ t, V → pairFam (InLabel (X := X) S) (OutLabel (X := X) S) t
  | true => fun v j => y j.1 v
  | false => fun v j => y j.1 v

omit [Fintype V] [DecidableEq V] [Fintype J] [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] in
theorem merge_splitCfg (y : ∀ j, V → X j) (v : V) :
    merge S (fun t => splitCfg S y t v) = fun j => y j v := by
  funext j
  unfold merge
  by_cases h : j ∈ S
  · simp only [h, ↓reduceDIte]
    rfl
  · simp only [h, ↓reduceDIte]
    rfl

/-- The splitting is a bijection. -/
def splitEquiv : (∀ j, V → X j) ≃ (∀ t, V → pairFam (InLabel (X := X) S) (OutLabel (X := X) S) t)
    where
  toFun := splitCfg S
  invFun z := fun j v => merge S (fun t => z t v) j
  left_inv y := by
    funext j v
    change merge S (fun t => splitCfg S y t v) j = y j v
    rw [merge_splitCfg]
  right_inv z := by
    funext t
    cases t
    · funext v j
      change merge S (fun t => z t v) j.1 = z false v j
      unfold merge
      simp only [j.2, ↓reduceDIte]
    · funext v j
      change merge S (fun t => z t v) j.1 = z true v j
      unfold merge
      simp only [j.2, ↓reduceDIte]

/-- **The joint energy of a tensor is the energy of the product law**:
`Y_{(⊗_{j ∈ S} L_j) ⊗ (⊗_{j ∉ S} L_j)}[F ∘ merge] = Y_{⊗_j L_j}[F]`. -/
theorem jointEnergy_tensor (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ j, X j) → ℝ) :
    jointEnergy (tensorLaw fun j : {j // j ∈ S} => L j.1)
      (tensorLaw fun j : {j // j ∉ S} => L j.1) (fun z => F (merge S z)) =
    diagonalIntegral (tensorLaw L) F := by
  unfold jointEnergy diagonalIntegral multilinearIntegral
  rw [tensorLaw_pairLaws_apply]
  change _ = ∑ y : ∀ j, V → X j, (∏ j, lawDensity (L j) (y j)) * ∏ v, F (fun j => y j v)
  symm
  refine Fintype.sum_equiv (splitEquiv (V := V) S) _ _ fun y => ?_
  change (∏ j, lawDensity (L j) (y j)) * ∏ v, F (fun j => y j v) =
    (lawDensity (tensorLaw fun j : {j // j ∈ S} => L j.1) (splitCfg S y true) *
      lawDensity (tensorLaw fun j : {j // j ∉ S} => L j.1) (splitCfg S y false)) *
      ∏ v, F (merge S (fun t => splitCfg S y t v))
  rw [lawDensity_tensorLaw, lawDensity_tensorLaw]
  simp only [merge_splitCfg]
  congr 1
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ S)
    (fun j => lawDensity (L j) (y j))]
  congr 1
  exact Finset.prod_congr (by ext x; simp) (fun _ _ => rfl)

end Sarkozy.EnvelopeSteps
