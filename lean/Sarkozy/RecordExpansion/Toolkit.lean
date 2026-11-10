module

public import Sarkozy.RecordExpansion.FirstStage
public import Sarkozy.RecordExpansion.Charging

/-!
# Order and `±` tensorization in the energy toolkit

The parts (E2) and (P5) of `lem:energy-toolkit` (Section 10 of the paper) that use
only positivity at one cut, for product laws `⊗_b L_b` over an arbitrary finite
index type. A selected set `X` of atoms with a law `κ` on `X_X^V` is one factor of
such a product (index the factors by the selected block and the outside atoms),
so these statements cover the paper's `κ ⊗ O'` and `ζ ⊗ λ_{-X}`.

* `energy_le_of_below_factor` ((E2)): if `κ ⪰_ϑ κ'` at the factor `j₀` and every
  other factor is `⪰_ϑ 0`, then `Y_{κ ⊗ O'} ≥ Y_{κ' ⊗ O'}`; no positivity of `κ'`
  is needed.
* `abs_energy_le_of_add_sub` ((P5), first claim): if `κ_b ± ζ_b ⪰_ι 0` for every
  factor (at the outside atoms these are `Ñ_b ± λ_b` of (CP3)), then
  `|Y_{⊗ζ}| ≤ Y_{⊗κ}`.
* `abs_energy_le_of_brackets` ((P5), second claim): brackets
  `(κ_b  ζ_b; ζ_b*  κ'_b) ⪰_ι 0` for every factor give
  `|Y_{⊗ζ}| ≤ Y_{⊗κ}^{1/2} Y_{⊗κ'}^{1/2}`.
* `energy_eq_zero_of_skew_factor` ((P5), third claim): if one factor is skew at
  `ι` and all others are symmetric, the energy of the product vanishes.
* `abs_energy_le_diagonal_marginals` ((P1)): for a nonnegative `π` at the factor
  `j₀` and positive outside factors,
  `|Y^O[π]| ≤ Y^O[Diag(m_+)]^{1/2} Y^O[Diag(m_-)]^{1/2}`.
* `energy_diagonal_le_of_le` ((P2)): `m ≤ M m'` pointwise gives
  `Y^O[Diag(m)] ≤ M Y^O[Diag(m')]`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- A product law is linear in each single factor: subtraction. -/
theorem tensorLaw_update_sub (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (M N : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (Function.update L j₀ (M - N)) =
      tensorLaw (Function.update L j₀ M) - tensorLaw (Function.update L j₀ N) := by
  have h := tensorLaw_update_add L j₀ (M - N) N
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- **(E2) of `lem:energy-toolkit`**: if `κ ⪰_ϑ κ'` at the factor `j₀` and all other
factors are positive at `ϑ`, then `Y_{κ ⊗ O'} ≥ Y_{κ' ⊗ O'}`. -/
theorem energy_le_of_below_factor (ϑ : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hO : ∀ j, j ≠ j₀ → ϑ.Positive (O j)) {κ κ' : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ}
    (h : ϑ.Below κ' κ) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw (Function.update O j₀ κ')) F ≤
      diagonalIntegral (tensorLaw (Function.update O j₀ κ)) F := by
  have hpos : ϑ.Positive (tensorLaw (Function.update O j₀ (κ - κ'))) := by
    apply ReflectionCut.Positive.tensor
    intro j
    by_cases hj : j = j₀
    · subst hj
      rw [Function.update_self]
      exact h
    · rw [Function.update_of_ne hj]
      exact hO j hj
  rw [tensorLaw_update_sub] at hpos
  have h1 := hpos.diagonal_nonneg F
  change 0 ≤ diagonalIntegral (tensorLaw (Function.update O j₀ κ)) F -
    diagonalIntegral (tensorLaw (Function.update O j₀ κ')) F at h1
  linarith

/-- **(P5), first claim**: `κ_b ± ζ_b ⪰_c 0` at every factor gives `|Y_{⊗ζ}| ≤ Y_{⊗κ}`. -/
theorem abs_energy_le_of_add_sub {c : ReflectionCut V} {κ ζ : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hp : ∀ b, c.Positive (κ b + ζ b)) (hm : ∀ b, c.Positive (κ b - ζ b))
    (F : (∀ b, X b) → ℝ) :
    |diagonalIntegral (tensorLaw ζ) F| ≤ diagonalIntegral (tensorLaw κ) F :=
  abs_diagonal_le_self_of_bracket (bracket_tensorLaw_of_add_sub hp hm) F

/-- **(P5), second claim**: brackets `(κ_b  ζ_b; ζ_b*  κ'_b) ⪰_c 0` at every factor give
`|Y_{⊗ζ}| ≤ Y_{⊗κ}^{1/2} Y_{⊗κ'}^{1/2}`. -/
theorem abs_energy_le_of_brackets {c : ReflectionCut V}
    {κ ζ κ' : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ} (h : ∀ b, c.Bracket (κ b) (ζ b) (κ' b))
    (F : (∀ b, X b) → ℝ) :
    |diagonalIntegral (tensorLaw ζ) F| ≤
      Real.sqrt (diagonalIntegral (tensorLaw κ) F) *
        Real.sqrt (diagonalIntegral (tensorLaw κ') F) :=
  abs_diagonal_le_of_bracket (ReflectionCut.Bracket.tensor h) F

/-- **(P5), third claim**: if the factor `j₀` is skew at `c` and every other factor is
symmetric at `c`, the product is skew and its energy vanishes. -/
theorem energy_eq_zero_of_skew_factor (c : ReflectionCut V) (L : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hskew : IsSkewAt c (L j₀)) (hsym : ∀ j, j ≠ j₀ → IsSymmetricAt c (L j))
    (F : (∀ b, X b) → ℝ) : diagonalIntegral (tensorLaw L) F = 0 := by
  apply diagonalIntegral_tensorLaw_eq_zero c L (fun j => if j = j₀ then -1 else 1)
  · intro j
    by_cases hj : j = j₀
    · subst hj
      rw [ite_eq_left rfl, neg_one_smul_functional]
      exact hskew
    · rw [ite_eq_right hj, one_smul_functional]
      exact hsym j hj
  · rw [Fintype.prod_ite_eq']

/-- Scaling one factor scales the product law. -/
theorem tensorLaw_update_smul (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (a : ℝ)
    (K : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) :
    tensorLaw (Function.update L j₀ (a • K)) = a • tensorLaw (Function.update L j₀ K) := by
  have h := tensorLaw_smul (fun j => if j = j₀ then a else 1) (Function.update L j₀ K)
  rw [Fintype.prod_ite_eq'] at h
  rw [← h]
  congr 1
  funext j
  by_cases hj : j = j₀
  · subst hj
    rw [ite_eq_left rfl, Function.update_self, Function.update_self]
  · rw [ite_eq_right hj, Function.update_of_ne hj, Function.update_of_ne hj,
      one_smul_functional]

/-- **(P1) of `lem:energy-toolkit`**: for a nonnegative weight `π` at the factor `j₀`,
with half marginals `m_±`, and positive outside factors,
`|Y^O[π]| ≤ Y^O[Diag(m_+)]^{1/2} Y^O[Diag(m_-)]^{1/2}`. -/
theorem abs_energy_le_diagonal_marginals (c : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (hO : ∀ j, j ≠ j₀ → c.Positive (O j))
    {π : (V → X j₀) → ℝ} (hπ : ∀ z, 0 ≤ π z) (F : (∀ b, X b) → ℝ) :
    |diagonalIntegral (tensorLaw (Function.update O j₀ (signedIntegral π))) F| ≤
      Real.sqrt (diagonalIntegral
          (tensorLaw (Function.update O j₀ (c.diagonalLaw (plusMarginal c π)))) F) *
        Real.sqrt (diagonalIntegral
          (tensorLaw (Function.update O j₀ (c.diagonalLaw (minusMarginal c π)))) F) := by
  apply abs_energy_le_of_brackets
  intro j
  by_cases hj : j = j₀
  · subst hj
    simp only [Function.update_self]
    exact bracket_diagonal_marginals c hπ
  · simp only [Function.update_of_ne hj]
    exact (hO j hj).bracket_self

/-- **(P2) of `lem:energy-toolkit`** (density domination): if `0 ≤ m ≤ M m'` pointwise
on the plus-half labels, then `Y^O[Diag(m)] ≤ M Y^O[Diag(m')]` for positive outside
factors. -/
theorem energy_diagonal_le_of_le (c : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J) (hO : ∀ j, j ≠ j₀ → c.Positive (O j))
    {m m' : (c.Half → X j₀) → ℝ} {M : ℝ} (hle : ∀ x, m x ≤ M * m' x)
    (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw (Function.update O j₀ (c.diagonalLaw m))) F ≤
      M * diagonalIntegral (tensorLaw (Function.update O j₀ (c.diagonalLaw m'))) F := by
  have hbelow : c.Below (c.diagonalLaw m) (M • c.diagonalLaw m') := by
    unfold ReflectionCut.Below
    have he : M • c.diagonalLaw m' - c.diagonalLaw m =
        c.diagonalLaw (fun x => M * m' x - m x) := by
      apply LinearMap.ext
      intro f
      change M * (∑ x, m' x * f (c.join x x)) - ∑ x, m x * f (c.join x x) =
        ∑ x, (M * m' x - m x) * f (c.join x x)
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [he]
    exact c.diagonalLaw_positive fun x => by linarith [hle x]
  have h := energy_le_of_below_factor c O j₀ hO hbelow F
  rw [tensorLaw_update_smul] at h
  exact h

end Sarkozy.RecordExpansion
