module

public import Sarkozy.RecordExpansion.Selections
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Expansion of a product of two-term laws over subsets

The expansion behind the energy bounds under the bracket, `lem:bracket-energy`
of the paper (Section 10): on the first-stage atoms
`Ñ_{0,b} = μ_b + (Ñ_{0,b} - μ_b)`, and expanding the product gives a sum, over
the sets `X'` of atoms carrying the second summand, of energies with selected
measures `⊗_{b ∈ X'} (Ñ_{0,b} - μ_b)`. If each of these is bounded by
`K ∏_{b ∈ X'} u_b`, the total is at most `K ∏_b (1 + u_b) ≤ K e^{U_0}`,
`U_0 = ∑_b u_b`.

Here a set of atoms is given by its indicator `f : J → Bool`; `A b` is the
law kept off the set and `R b` the law selected on it. The index type `J` is
arbitrary, so a fixed selected block (the measure `κ` on `X_X^V` of
`lem:bracket-energy`) can be one of the factors, with `R = 0` there. The
per-term bounds, which in the paper come from the structured-energy estimate
(`prop:record:density-structured`), are hypotheses.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- `⊗_b (A_b + R_b) = ∑_{X'} ⊗_b (R_b on X', A_b off X')`. -/
theorem tensorLaw_add_eq_sum (A R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun b => A b + R b) =
      ∑ f : J → Bool, tensorLaw (fun b => if f b then R b else A b) := by
  have h : (fun b => A b + R b) = fun b => ∑ i : Bool, (if i then R b else A b) := by
    funext b
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    exact add_comm _ _
  rw [h, tensorLaw_sum]

/-- The energy form of `tensorLaw_add_eq_sum`. -/
theorem energy_add_eq_sum (A R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw fun b => A b + R b) F =
      ∑ f : J → Bool, diagonalIntegral (tensorLaw fun b => if f b then R b else A b) F := by
  rw [tensorLaw_add_eq_sum, diagonalIntegral_sum]

omit [DecidableEq J] in
theorem prod_one_add_le_exp (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) :
    ∏ b, (1 + u b) ≤ Real.exp (∑ b, u b) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro b _
    linarith [hu b]
  · intro b _
    linarith [Real.add_one_le_exp (u b)]

/-- **Summed bound** (`lem:bracket-energy`): if every term with selected set `X'`
satisfies `|Y_{X'}| ≤ K ∏_{b ∈ X'} u_b`, then
`|Y_{⊗(A + R)}| ≤ K ∏_b (1 + u_b)`. -/
theorem abs_energy_add_le (A R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ)
    (u : J → ℝ) {K : ℝ}
    (hterm : ∀ f : J → Bool, |diagonalIntegral (tensorLaw fun b => if f b then R b else A b) F| ≤
      K * ∏ b, (if f b then u b else 1)) :
    |diagonalIntegral (tensorLaw fun b => A b + R b) F| ≤ K * ∏ b, (1 + u b) := by
  rw [energy_add_eq_sum]
  have hprod : ∏ b, (1 + u b) = ∑ f : J → Bool, ∏ b, (if f b then u b else 1) := by
    rw [← Fintype.prod_sum (fun b (i : Bool) => if i then u b else 1)]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    exact add_comm _ _
  rw [hprod, Finset.mul_sum]
  calc |∑ f : J → Bool, diagonalIntegral (tensorLaw fun b => if f b then R b else A b) F|
      ≤ ∑ f : J → Bool, |diagonalIntegral (tensorLaw fun b => if f b then R b else A b) F| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun f _ => hterm f

/-- **The exponential form** (`lem:bracket-energy`): with `K ≥ 0` and `u ≥ 0`,
`|Y_{⊗(A + R)}| ≤ K e^{U}`, `U = ∑_b u_b`. -/
theorem abs_energy_add_le_exp (A R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ)
    (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) {K : ℝ} (hK : 0 ≤ K)
    (hterm : ∀ f : J → Bool, |diagonalIntegral (tensorLaw fun b => if f b then R b else A b) F| ≤
      K * ∏ b, (if f b then u b else 1)) :
    |diagonalIntegral (tensorLaw fun b => A b + R b) F| ≤ K * Real.exp (∑ b, u b) :=
  (abs_energy_add_le A R F u hterm).trans
    (mul_le_mul_of_nonneg_left (prod_one_add_le_exp u hu) hK)

end Sarkozy.RecordExpansion
