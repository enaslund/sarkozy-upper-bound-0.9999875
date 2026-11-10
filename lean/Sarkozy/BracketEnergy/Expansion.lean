module

public import Sarkozy.RecordExpansion.SubsetExpansion

@[expose] public section

/-!
# The expansion of the bracket `Ñ = μ + (Ñ₀ − μ) + δ_E` in a multilinear energy

`lem:bracket-energy` bounds an energy whose outside law is the bracket `Ñ = ⊗_𝔟 Ñ_𝔟` of (CP3),
`Ñ_𝔟 = Ñ_{0,𝔟} + δ_{E,𝔟}` and `Ñ_{0,𝔟} = μ_𝔟 + (Ñ_{0,𝔟} − μ_𝔟)`. The paper's proof:
* `E_{Ñ₀}[κ]` is the sum over the sets `X'` of atoms outside `X` of the energies with selected
  measure `κ ⊗ ⊗_{X'} (Ñ₀ − μ)` and outside law `μ`; each is at most
  `(1 + o(1)) ‖κ‖ Π_X ∏_{X'} u_𝔟 Y` (the first bound), and the sum is at most
  `(1 + o(1)) ∏_𝔟 (1 + u_𝔟) ‖κ‖ Π_X Y ≤ (1 + o(1)) e^{U₀} ‖κ‖ Π_X Y`;
* `E_Ñ[κ] − E_{Ñ₀}[κ]` is `lem:sharp-first` (at most `(R_err + o(1)) ‖κ‖ Π_X Y`);
* hence `|E_Ñ[κ]| ≤ (B + o(1)) ‖κ‖ Π_X Y` with `B = e^{U₀} + R_err`.

This file is the algebra of that proof, for any multilinear energy
`∫ ∏_v G_v(z_v) d(⊗_𝔟 Λ_𝔟)` (inputs `G` arbitrary, so revealed inputs are allowed), any atoms and
any alphabets:
* `tensorLaw_eq_zero_of_factor`: a product law with a zero factor is zero;
* `tensorLaw_ite_add_eq_sum`: `⊗_𝔟 (f ? Q : A + R) = ∑_g ⊗_𝔟 (g ? (f ? 0 : R) : (f ? Q : A))`;
* `bracketTerm`, `bracketTerm_eq_zero`, `bracketTerm_eq_valid`: the terms; a term that selects a
  record at an atom of `f` vanishes, the others are `⊗_𝔟 (f ? Q : g ? R : A)`;
* **`abs_multilinear_bracket0_le`**: `|E_{f ? Q : A + R}| ≤ K e^U + ∑_{g ⊥ f} r_g` from the
  per-term bounds `|E_{f ? Q : g ? R : A}| ≤ K ∏_{g} u + r_g` (`∑ u ≤ U`, `u ≥ 0`, `K ≥ 0`);
* **`abs_multilinear_bracket_le`**: the same with the bracket `A + R + δ` and the difference
  bound `|E_{A+R+δ} − E_{A+R}| ≤ K₂ + r₂` (`lem:sharp-first`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.RecordExpansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

/-- A product law with a zero factor is zero. -/
theorem tensorLaw_eq_zero_of_factor (Λ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (h : Λ j₀ = 0) : tensorLaw Λ = 0 := by
  apply LinearMap.ext
  intro F
  rw [tensorLaw_apply, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro z _
  rw [Finset.prod_eq_zero (mem_univ j₀) (by rw [h]; rfl), zero_mul]

omit [Fintype J] [DecidableEq J] [DecidableEq V] [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)] in
/-- The multilinear energy is linear in the law. -/
theorem multilinearIntegral_sum {ι : Type*} (s : Finset ι)
    (Λ : ι → ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ) (G : V → (∀ j, X j) → ℝ) :
    multilinearIntegral (∑ i ∈ s, Λ i) G = ∑ i ∈ s, multilinearIntegral (Λ i) G := by
  unfold multilinearIntegral
  exact LinearMap.sum_apply s Λ _

/-- The term of the expansion of `⊗_𝔟 (f ? Q : A + R)` at the choice `g`. -/
noncomputable def bracketTerm (f g : J → Bool) (Q A R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ :=
  fun b => if g b then (if f b then 0 else R b) else (if f b then Q b else A b)

/-- **The expansion of the selected bracket** (`lem:bracket-energy`, proof):
`⊗_𝔟 (f ? Q : A + R) = ∑_g bracketTerm f g`. -/
theorem tensorLaw_ite_add_eq_sum (f : J → Bool) (Q A R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (fun b => if f b then Q b else A b + R b) =
      ∑ g : J → Bool, tensorLaw (bracketTerm f g Q A R) := by
  have h : (fun b => if f b then Q b else A b + R b) =
      fun b => (if f b then Q b else A b) + (if f b then 0 else R b) := by
    funext b
    cases f b <;> simp
  rw [h, tensorLaw_add_eq_sum]
  rfl

/-- The choices `g` that select no record at an atom of `f`. -/
noncomputable def validChoices (f : J → Bool) : Finset (J → Bool) :=
  univ.filter fun g => ∀ b, g b = true → f b = false

/-- A term that selects a record at an atom of `f` vanishes. -/
theorem bracketTerm_eq_zero (f g : J → Bool) (Q A R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hg : g ∉ validChoices f) : tensorLaw (bracketTerm f g Q A R) = 0 := by
  unfold validChoices at hg
  simp only [mem_filter, mem_univ, true_and] at hg
  push Not at hg
  obtain ⟨b, hgb, hfb⟩ := hg
  apply tensorLaw_eq_zero_of_factor _ b
  unfold bracketTerm
  simp only [ne_eq, Bool.not_eq_false] at hfb
  simp [hgb, hfb]

omit [Fintype V] [DecidableEq V] [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] in
/-- The other terms are `⊗_𝔟 (f ? Q : g ? R : A)`. -/
theorem bracketTerm_eq_valid (f g : J → Bool) (Q A R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hg : g ∈ validChoices f) :
    bracketTerm f g Q A R = fun b => if f b then Q b else if g b then R b else A b := by
  unfold validChoices at hg
  rw [mem_filter] at hg
  funext b
  unfold bracketTerm
  cases hgb : g b <;> cases hfb : f b <;> simp
  exact absurd (hg.2 b hgb) (by simp [hfb])

omit [Fintype V] [DecidableEq V] [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] in
/-- `∑_{g ⊥ f} ∏_{g} u ≤ ∏_𝔟 (1 + u_𝔟) ≤ e^U`. -/
theorem sum_valid_prod_le_exp (f : J → Bool) (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) {U : ℝ}
    (hU : ∑ b, u b ≤ U) :
    ∑ g ∈ validChoices f, ∏ b, (if g b then u b else 1) ≤ Real.exp U := by
  have hprod : ∏ b, (1 + u b) = ∑ g : J → Bool, ∏ b, (if g b then u b else 1) := by
    rw [← Fintype.prod_sum (fun b (i : Bool) => if i then u b else 1)]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    exact add_comm _ _
  have hnn : ∀ g : J → Bool, 0 ≤ ∏ b, (if g b then u b else 1) := fun g =>
    prod_nonneg fun b _ => by split_ifs; exacts [hu b, zero_le_one]
  calc ∑ g ∈ validChoices f, ∏ b, (if g b then u b else 1)
      ≤ ∑ g : J → Bool, ∏ b, (if g b then u b else 1) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun g _ _ => hnn g
    _ = ∏ b, (1 + u b) := hprod.symm
    _ ≤ Real.exp (∑ b, u b) := prod_one_add_le_exp u hu
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hU

/-- **The first two bounds of `lem:bracket-energy`, summed** (proof, `Ñ₀` part): if every term
`⊗_𝔟 (f ? Q : g ? R : A)` with `g ⊥ f` satisfies `|E| ≤ K ∏_{𝔟 ∈ g} u_𝔟 + r_g`, then
`|E_{⊗(f ? Q : A + R)}| ≤ K e^U + ∑_{g ⊥ f} r_g`, for `u ≥ 0`, `∑ u ≤ U`, `K ≥ 0`. -/
theorem abs_multilinear_bracket0_le (f : J → Bool) (Q A R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (G : V → (∀ j, X j) → ℝ) (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) {U K : ℝ} (hU : ∑ b, u b ≤ U)
    (hK : 0 ≤ K) (r : (J → Bool) → ℝ)
    (hterm : ∀ g ∈ validChoices f,
      |multilinearIntegral (tensorLaw fun b => if f b then Q b else if g b then R b else A b) G| ≤
        K * ∏ b, (if g b then u b else 1) + r g) :
    |multilinearIntegral (tensorLaw fun b => if f b then Q b else A b + R b) G| ≤
      K * Real.exp U + ∑ g ∈ validChoices f, r g := by
  rw [tensorLaw_ite_add_eq_sum, ← Finset.sum_subset (subset_univ (validChoices f))
    (fun g _ hg => bracketTerm_eq_zero f g Q A R hg), multilinearIntegral_sum]
  have hsum := sum_valid_prod_le_exp f u hu hU
  calc |∑ g ∈ validChoices f, multilinearIntegral (tensorLaw (bracketTerm f g Q A R)) G|
      ≤ ∑ g ∈ validChoices f, |multilinearIntegral (tensorLaw (bracketTerm f g Q A R)) G| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ g ∈ validChoices f, (K * ∏ b, (if g b then u b else 1) + r g) := by
        apply sum_le_sum
        intro g hg
        rw [bracketTerm_eq_valid f g Q A R hg]
        exact hterm g hg
    _ = K * ∑ g ∈ validChoices f, ∏ b, (if g b then u b else 1) +
          ∑ g ∈ validChoices f, r g := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ K * Real.exp U + ∑ g ∈ validChoices f, r g := by
        have := mul_le_mul_of_nonneg_left hsum hK
        linarith

/-- **`lem:bracket-energy`, the summed form** (proof): with the bracket `A + R + δ`, the
per-term bounds of `abs_multilinear_bracket0_le` and the difference bound
`|E_{f ? Q : A + R + δ} − E_{f ? Q : A + R}| ≤ K₂ + r₂` (`lem:sharp-first`),
`|E_{f ? Q : A + R + δ}| ≤ K e^U + K₂ + ∑_{g ⊥ f} r_g + r₂`. -/
theorem abs_multilinear_bracket_le (f : J → Bool) (Q A R δ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (G : V → (∀ j, X j) → ℝ) (u : J → ℝ) (hu : ∀ b, 0 ≤ u b) {U K K₂ r₂ : ℝ}
    (hU : ∑ b, u b ≤ U) (hK : 0 ≤ K) (r : (J → Bool) → ℝ)
    (hterm : ∀ g ∈ validChoices f,
      |multilinearIntegral (tensorLaw fun b => if f b then Q b else if g b then R b else A b) G| ≤
        K * ∏ b, (if g b then u b else 1) + r g)
    (hdiff : |multilinearIntegral (tensorLaw fun b => if f b then Q b else A b + R b + δ b) G -
        multilinearIntegral (tensorLaw fun b => if f b then Q b else A b + R b) G| ≤ K₂ + r₂) :
    |multilinearIntegral (tensorLaw fun b => if f b then Q b else A b + R b + δ b) G| ≤
      K * Real.exp U + K₂ + (∑ g ∈ validChoices f, r g + r₂) := by
  have h0 := abs_multilinear_bracket0_le f Q A R G u hu hU hK r hterm
  have htri := abs_sub_abs_le_abs_sub
    (multilinearIntegral (tensorLaw fun b => if f b then Q b else A b + R b + δ b) G)
    (multilinearIntegral (tensorLaw fun b => if f b then Q b else A b + R b) G)
  linarith

end Sarkozy.BracketEnergy
