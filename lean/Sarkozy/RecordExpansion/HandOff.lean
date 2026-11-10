module

public import Sarkozy.RecordExpansion.SharpFirst





@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

open Choice

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} {I : J → Type*} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]

omit [∀ b, DecidableEq (I b)] in
/-- The envelope law of a choice in the form of the bracket expansion. -/
theorem envelopeLaw_eq_bracketForm (N μ R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (δ : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (hN : ∀ b, N b = (μ b + R b) + ∑ i, δ b i)
    (D : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (ω : Choice T) :
    envelopeLaw N D ω = tensorLaw (fun b =>
      (entryFactor (μ b) (D b) (ω b) + (if (ω b).isSome then 0 else R b)) +
        ∑ i, (if (ω b).isSome then 0 else δ b i)) := by
  unfold envelopeLaw
  congr 1
  funext b
  rcases ω b with _ | ⟨t, e⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact hN b
  · simp only [Option.isSome_some, ↓reduceIte, add_zero, sum_const_zero]
    rfl

/-- **(E1) for the envelopes, from the bracket expansion** (`lem:bracket-energy` applied to
`κ = ⊗_{b∈X} D^{ε_b}_{b,t_b}`). -/
theorem envelope_energy_le_of_bracket {Tag : Type*} [Fintype Tag] [DecidableEq Tag]
    (N μ R : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (δ : ∀ b, I b → ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (hN : ∀ b, N b = (μ b + R b) + ∑ i, δ b i)
    (D : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (ω : Choice T)
    (F : (∀ b, X b) → ℝ) (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) {K K' : ℝ} (hK : 0 ≤ K)
    (hK' : 0 ≤ K')
    (hterm0 : ∀ f : J → Bool,
      |diagonalIntegral (tensorLaw fun b => if f b then (if (ω b).isSome then 0 else R b)
        else entryFactor (μ b) (D b) (ω b)) F| ≤
        K * ∏ b, (if f b then (if (ω b).isSome then 0 else u b) else 1))
    (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (r : (∀ b, Option (I b)) → ℝ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec tag σ j →
      |diagonalIntegral (tensorLaw (fun b => (σ b).elim
        (entryFactor (μ b) (D b) (ω b) + (if (ω b).isSome then 0 else R b))
        (fun i => if (ω b).isSome then 0 else δ b i))) F| ≤
        K' * tagWeight tag d v (fun b => if (ω b).isSome then 0 else u b) j σ + r σ) :
    diagonalIntegral (envelopeLaw N D ω) F ≤
      K * Real.exp (∑ b, if (ω b).isSome then 0 else u b) +
        K' * Real.exp (∑ b, if (ω b).isSome then 0 else u b) *
          tagSeries (tagTotal tag d) (tagTotal tag v) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), r σ := by
  rw [envelopeLaw_eq_bracketForm N μ R δ hN D ω]
  have hu' : ∀ b, 0 ≤ (if (ω b).isSome then 0 else u b) := by
    intro b
    split_ifs
    · exact le_rfl
    · exact hu b
  have h := abs_energy_le_bracket (fun b => entryFactor (μ b) (D b) (ω b))
    (fun b => if (ω b).isSome then 0 else R b) (fun b i => if (ω b).isSome then 0 else δ b i) F
    (fun b => if (ω b).isSome then 0 else u b) hu' hK hK' hterm0 tag hd hv r hterm
  exact (le_abs_self _).trans h

end Sarkozy.RecordExpansion
