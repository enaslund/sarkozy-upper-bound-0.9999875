module

public import Sarkozy.FiveType.PolarizationTensor
public import Sarkozy.Variance.MatchingBlocks

/-!
# The polarization order with outside factors (`lem:record:paired-e-joint`(a), blocks as factors)

`paper/sections/22_variance.tex`, `lem:record:paired-e-joint`(a), for the blocks of a selected set
`X` (factors `j ∈ Xs`, each carrying the two-layer five-type datum `D j` of C1's `FiveType`)
together with outside factors `O j` (`j ∉ Xs`, the reference `μ` outside `X`):
`⊗_X Π_{F₁} ⊗ O + ⊗_X Π_{F₂} ⊗ O ⪯_{ϑ₀} ⊗_X(Π_{E₀} + ε G_e) ⊗ O + ⊗_X(Π_{E₁} + ε G_o) ⊗ O`
(`polarization_c_blocks`). This is C1's `polarization_c_first` with the outside factors added.

**Hypotheses on the outside factors:** `O j` is positive at `ϑ₀` ((R2)) and invariant under its
reflection. The invariance is the chamber-reflection invariance of the reference, (R1); V1 proves
it for the middle law (`middleReference_g6_inv`).

`polarization_energy_blocks` is the energy form. It discharges the hypothesis `hord` of
`paired_e_joint_b_blocks` for five-type data: `Y[⊗Π_{F₁}] + Y[⊗Π_{F₂}] ≤ ∑_s Y[⊗(Π_{E_s} + ε G_s)]`.
`paired_e_joint_b_fivetype_blocks` is `lem:record:paired-e-joint`(b) for five-type data, with this
order proved.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.FiveType Sarkozy.ReflectionCut

namespace Sarkozy.Variance

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)]

/-- **`lem:record:paired-e-joint`(a) with outside factors**, both signs. -/
theorem polarization_c_blocks (D : ∀ j, Datum (X j)) (O : ∀ j, ((ZMod 6 → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hOpos : ∀ j, j ∉ Xs → (chamberCut 0).Positive (O j))
    (hOinv : ∀ j, j ∉ Xs → ∀ f : (ZMod 6 → X j) → ℝ,
      O j (fun z => f (z ∘ (chamberCut 0).flip)) = O j f)
    (eF eE ε : J → ℝ)
    (hF : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j ∈ Xs, eF j + eE j ≤ ε j) :
    (chamberCut 0).Positive
      (tensorLaw (fun j => if j ∈ Xs then (D j).QE0 (ε j) else O j) +
        tensorLaw (fun j => if j ∈ Xs then (D j).QE1 (ε j) else O j) -
        (tensorLaw (fun j => if j ∈ Xs then (D j).compF 1 else O j) +
          tensorLaw (fun j => if j ∈ Xs then (D j).compF 2 else O j))) ∧
    (chamberCut 0).Positive
      (tensorLaw (fun j => if j ∈ Xs then (D j).QE0 (ε j) else O j) +
        tensorLaw (fun j => if j ∈ Xs then (D j).QE1 (ε j) else O j) +
        (tensorLaw (fun j => if j ∈ Xs then (D j).compF 1 else O j) +
          tensorLaw (fun j => if j ∈ Xs then (D j).compF 2 else O j))) := by
  set A := tensorLaw (fun j => if j ∈ Xs then (D j).QE0 (ε j) else O j)
  set Dm := tensorLaw (fun j => if j ∈ Xs then (D j).QE1 (ε j) else O j)
  set K := tensorLaw (fun j => if j ∈ Xs then (D j).compF 1 else O j)
  set K2 := tensorLaw (fun j => if j ∈ Xs then (D j).compF 2 else O j)
  have hBr : (chamberCut 0).Bracket A K Dm := by
    apply Bracket.tensor
    intro j
    by_cases hj : j ∈ Xs
    · simp only [hj, ↓reduceIte]
      exact (D j).bracket_F1 (hF j hj) (hE j hj) (hε j hj)
    · simp only [hj, ↓reduceIte]
      exact (hOpos j hj).bracket_self
  have hK2 : ∀ f, K2 f = K (fun z => f (z ∘ (chamberCut 0).flip)) := fun f =>
    tensorLaw_comp (chamberCut 0).flip _ _ (fun j g => by
      by_cases hj : j ∈ Xs
      · simp only [hj, ↓reduceIte]
        exact ((D j).compF12_flip g).1.symm
      · simp only [hj, ↓reduceIte]
        exact (hOinv j hj g).symm) f
  have hA : ∀ f, A (fun z => f (z ∘ (chamberCut 0).flip)) = A f := fun f =>
    tensorLaw_inv (chamberCut 0).flip _ (fun j g => by
      by_cases hj : j ∈ Xs
      · simp only [hj, ↓reduceIte]
        exact (D j).QE0_flip_inv (ε j) g
      · simp only [hj, ↓reduceIte]
        exact hOinv j hj g) f
  have hD : ∀ f, Dm (fun z => f (z ∘ (chamberCut 0).flip)) = Dm f := fun f =>
    tensorLaw_inv (chamberCut 0).flip _ (fun j g => by
      by_cases hj : j ∈ Xs
      · simp only [hj, ↓reduceIte]
        exact (D j).QE1_flip_inv (ε j) g
      · simp only [hj, ↓reduceIte]
        exact hOinv j hj g) f
  have hKK : ∀ f, (K + K2) (fun z => f (z ∘ (chamberCut 0).flip)) = (K + K2) f := by
    intro f
    simp only [LinearMap.add_apply]
    rw [hK2 f, hK2 (fun z => f (z ∘ (chamberCut 0).flip))]
    have : (fun z : ZMod 6 → ∀ j, X j =>
        (fun z => f (z ∘ (chamberCut 0).flip)) (z ∘ (chamberCut 0).flip)) = f := by
      funext z
      simp only [Function.comp_def, (chamberCut 0).flip_flip]
    rw [this, add_comm]
  have hdiag : ∀ F, (chamberCut 0).form K2 F F = (chamberCut 0).form K F F := fun F =>
    form_of_flip_image (chamberCut 0) hK2 F F
  constructor
  · constructor
    · intro F G
      refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
      simp only [LinearMap.sub_apply, LinearMap.add_apply]
      rw [hA, hD]
      have := hKK f
      simp only [LinearMap.add_apply] at this
      rw [this]
    · intro F
      have h := (Bracket.neg hBr).nonneg F F
      rw [show (chamberCut 0).form (-K) F F = -(chamberCut 0).form K F F from rfl] at h
      rw [form_sub, form_add, form_add, hdiag]
      linarith
  · constructor
    · intro F G
      refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
      simp only [LinearMap.add_apply]
      rw [hA, hD]
      have := hKK f
      simp only [LinearMap.add_apply] at this
      rw [this]
    · intro F
      have h := hBr.nonneg F F
      rw [form_add, form_add, form_add, hdiag]
      linarith

/-- **The polarization order in energy form**: under the hypotheses of `polarization_c_blocks`,
`Y[⊗_X Π_{F₁} ⊗ O] + Y[⊗_X Π_{F₂} ⊗ O] ≤ Y[⊗_X(Π_{E₀} + εG_e) ⊗ O] + Y[⊗_X(Π_{E₁} + εG_o) ⊗ O]`
for every input `F`. This is the hypothesis `hord` of `paired_e_joint_b_blocks`. -/
theorem polarization_energy_blocks (D : ∀ j, Datum (X j))
    (O : ∀ j, ((ZMod 6 → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J)
    (hOpos : ∀ j, j ∉ Xs → (chamberCut 0).Positive (O j))
    (hOinv : ∀ j, j ∉ Xs → ∀ f : (ZMod 6 → X j) → ℝ,
      O j (fun z => f (z ∘ (chamberCut 0).flip)) = O j f)
    (eF eE ε : J → ℝ)
    (hF : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j ∈ Xs, eF j + eE j ≤ ε j) (F : (∀ j, X j) → ℝ) :
    diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compF 1 else O j)) F +
        diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compF 2 else O j)) F ≤
      diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).QE0 (ε j) else O j)) F +
        diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).QE1 (ε j) else O j)) F := by
  have h := ((polarization_c_blocks D O Xs hOpos hOinv eF eE ε hF hE hε).1).diagonal_nonneg F
  simp only [diagonalIntegral, multilinearIntegral, LinearMap.sub_apply, LinearMap.add_apply] at h ⊢
  linarith

/-- **`lem:record:paired-e-joint`(b), the aligned bound, for five-type data with outside
factors**: the polarization order is proved (`polarization_energy_blocks`); the restoration bounds
for the two fold products and (E1) for the merge parts `⊗(Π_{E_s} + εG_s) - ⊗Π_{E_s}` are
hypotheses. Conclusion: `½(Y[⊗_X Π_{E₀} ⊗ O] + Y[⊗_X Π_{E₁} ⊗ O]) ≥ (l₀ - C ε_X - z₁ - z ε_X C) Y`.
-/
theorem paired_e_joint_b_fivetype_blocks (D : ∀ j, Datum (X j))
    (O : ∀ j, ((ZMod 6 → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J)
    (hOpos : ∀ j, j ∉ Xs → (chamberCut 0).Positive (O j))
    (hOinv : ∀ j, j ∉ Xs → ∀ f : (ZMod 6 → X j) → ℝ,
      O j (fun z => f (z ∘ (chamberCut 0).flip)) = O j f)
    (eF eE ε : J → ℝ)
    (hF : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j ∈ Xs, eF j + eE j ≤ ε j) (F : (∀ j, X j) → ℝ)
    {Yμ CX C εX l₀ z₁ z : ℝ} (hY : 0 ≤ Yμ) (hCX : CX ≤ C) (hεX : 0 ≤ εX) (hz : 0 ≤ z)
    (hF1 : (l₀ - z₁) * Yμ ≤
      diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compF 1 else O j)) F)
    (hF2 : (l₀ - z₁) * Yμ ≤
      diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compF 2 else O j)) F)
    (hMg0 : diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).QE0 (ε j) else O j)) F -
        diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compE 0 else O j)) F ≤
      (1 + z) * εX * CX * Yμ)
    (hMg1 : diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).QE1 (ε j) else O j)) F -
        diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compE 1 else O j)) F ≤
      (1 + z) * εX * CX * Yμ) :
    (l₀ - C * εX - z₁ - z * εX * C) * Yμ ≤
      (diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compE 0 else O j)) F +
        diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compE 1 else O j)) F) / 2 :=
  paired_e_joint_b_blocks hY hCX hεX hz
    (polarization_energy_blocks D O Xs hOpos hOinv eF eE ε hF hE hε F) hF1 hF2 hMg0 hMg1

/-- **The polarization order in energy form, with the five-type reference outside**: when the
outside factors are the blocks' five-type measures `𝒬_{a_j}` (the reference laws of
`lem:front12:reference`, before they are read on the slots), the reflection invariance is C1's
`Q_inv6` (`lem:five-type`(a)). Only their positivity at `ϑ₀` remains a hypothesis
(`lem:five-type`(b), V1's `ChamberCut`). -/
theorem polarization_energy_blocks_Q (D : ∀ j, Datum (X j)) (a : J → Ty → ℝ) (Xs : Finset J)
    (hOpos : ∀ j, j ∉ Xs → (chamberCut 0).Positive ((D j).Q (a j)))
    (eF eE ε : J → ℝ)
    (hF : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j ∈ Xs, ∀ b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j ∈ Xs, eF j + eE j ≤ ε j) (F : (∀ j, X j) → ℝ) :
    diagonalIntegral (tensorLaw (fun j => if j ∈ Xs then (D j).compF 1 else (D j).Q (a j))) F +
        diagonalIntegral
          (tensorLaw (fun j => if j ∈ Xs then (D j).compF 2 else (D j).Q (a j))) F ≤
      diagonalIntegral
          (tensorLaw (fun j => if j ∈ Xs then (D j).QE0 (ε j) else (D j).Q (a j))) F +
        diagonalIntegral
          (tensorLaw (fun j => if j ∈ Xs then (D j).QE1 (ε j) else (D j).Q (a j))) F :=
  polarization_energy_blocks D (fun j => (D j).Q (a j)) Xs hOpos
    (fun j _ f => flip_inv_of_inv6 ((D j).Q_inv6 (a j)) f) eF eE ε hF hE hε F

end Sarkozy.Variance
