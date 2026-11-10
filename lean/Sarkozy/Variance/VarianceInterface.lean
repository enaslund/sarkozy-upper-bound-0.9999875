module

public import Sarkozy.Variance.Exterior

/-!
# The variance form for a product of record differences (`lem:record:variance-interface`(i))

`paper/sections/10_comparison_lemmas.tex`, `lem:record:variance-interface`(i), for a selected set
`X` of atoms, **each its own factor**: on `𝔅 ∈ X` the record difference `ζ_𝔅` has a bilinear
bound `γ_𝔅` relative to the centred norm of `m_𝔅` (`‖Δ_𝔅‖ ≤ γ_𝔅`, `Δ_𝔅 1 = Δ_𝔅^* 1 = 0`), and the
outside atoms carry the brackets `(Ñ_b λ_b; λ_b Ñ_b) ⪰ 0` of (CP3). Then
`|Y_{ζ_X ⊗ λ_{-X}}| ≤ ∏_𝔅 γ_𝔅 (Y^Ñ[Diag_X] - Y^Ñ[J_X])` (`abs_energy_le_variance_blocks`), with
`Diag_X = ⊗_X Diag(m_𝔅)` and `J_X = ⊗_X J(m_𝔅)`.

WP-R's `RecordExpansion.abs_energy_le_variance` is the case of one factor; its report lists the
deduction of the bound from `Δ_X = ⊗ Δ_𝔅` as open. **Proof:** the brackets
`(γ_𝔅(Diag - J)  ζ_𝔅; ζ_𝔅^*  γ_𝔅(Diag - J)) ⪰ 0` (WP-R's `bracket_of_form_bound`) tensorize with
those of (CP3), giving `|Y[⊗ζ]| ≤ ∏γ_𝔅 · Y[⊗_X (Diag - J) ⊗ Ñ]`, and
`⊗_X(Diag - J) ⪯ ⊗_X Diag - ⊗_X J` (expand `⊗_X Diag = ⊗_X (J + (Diag - J))`; every term is
positive). The parities of the paper (an even number of skew factors) enter only through the
bilinear bounds.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`lem:record:variance-interface`(i) for a product of record differences** over a nonempty
set `X` of factors. -/
theorem abs_energy_le_variance_blocks (c : ReflectionCut V) (N lam : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (Xs : Finset J) (hXs : Xs.Nonempty) (hN : ∀ j, j ∉ Xs → c.Bracket (N j) (lam j) (N j))
    (m : ∀ j, (c.Half → X j) → ℝ) (hm : ∀ j ∈ Xs, ∀ x, 0 ≤ m j x) (γ : J → ℝ)
    (hγ : ∀ j ∈ Xs, 0 ≤ γ j) (ζ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hζ : ∀ j ∈ Xs, ∀ G H : (c.Half → X j) → ℝ, |c.form (ζ j) G H| ≤
      γ j * Real.sqrt (c.form (c.diagonalLaw (m j) - indepLaw c (m j)) G G) *
        Real.sqrt (c.form (c.diagonalLaw (m j) - indepLaw c (m j)) H H))
    (F : (∀ b, X b) → ℝ) :
    |diagonalIntegral (tensorLaw fun j => if j ∈ Xs then ζ j else lam j) F| ≤
      (∏ j ∈ Xs, γ j) *
        (diagonalIntegral (tensorLaw fun j => if j ∈ Xs then c.diagonalLaw (m j) else N j) F -
          diagonalIntegral (tensorLaw fun j => if j ∈ Xs then indepLaw c (m j) else N j) F) := by
  obtain ⟨K, hK⟩ : ∃ K : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ,
      K = fun j => if j ∈ Xs then c.diagonalLaw (m j) - indepLaw c (m j) else N j := ⟨_, rfl⟩
  have hNpos : ∀ j, j ∉ Xs → c.Positive (N j) := fun j hj => (hN j hj).left_positive
  have hKpos : ∀ j, c.Positive (K j) := by
    intro j
    by_cases hj : j ∈ Xs
    · simp only [hK, hj, ↓reduceIte]
      exact positive_diagonal_sub_indep c (hm j hj)
    · simp only [hK, hj, ↓reduceIte]
      exact hNpos j hj
  -- the tensorized brackets
  have hbr := abs_energy_le_of_brackets (c := c)
    (κ := fun j => (if j ∈ Xs then γ j else 1) • K j)
    (ζ := fun j => if j ∈ Xs then ζ j else lam j)
    (κ' := fun j => (if j ∈ Xs then γ j else 1) • K j) (fun j => by
      by_cases hj : j ∈ Xs
      · simp only [hK, hj, ↓reduceIte]
        exact bracket_of_form_bound (positive_diagonal_sub_indep c (hm j hj)) (hγ j hj) (hζ j hj)
      · simp only [hK, hj, ↓reduceIte, one_smul]
        exact hN j hj) F
  rw [tensorLaw_smul] at hbr
  have hprod : ∏ j, (if j ∈ Xs then γ j else 1) = ∏ j ∈ Xs, γ j := by
    rw [prod_ite, prod_const_one, mul_one]
    congr 1
    ext j
    simp
  rw [hprod] at hbr
  have hKnn : 0 ≤ diagonalIntegral (tensorLaw K) F :=
    (ReflectionCut.Positive.tensor hKpos).diagonal_nonneg F
  have hγ0 : 0 ≤ ∏ j ∈ Xs, γ j := prod_nonneg hγ
  have hsq : Real.sqrt (diagonalIntegral ((∏ j ∈ Xs, γ j) • tensorLaw K) F) *
      Real.sqrt (diagonalIntegral ((∏ j ∈ Xs, γ j) • tensorLaw K) F) =
      (∏ j ∈ Xs, γ j) * diagonalIntegral (tensorLaw K) F := by
    rw [Real.mul_self_sqrt]
    · rfl
    · exact mul_nonneg hγ0 hKnn
  rw [hsq] at hbr
  refine hbr.trans (mul_le_mul_of_nonneg_left ?_ hγ0)
  -- `⊗_X (Diag - J) ⪯ ⊗_X Diag - ⊗_X J`
  obtain ⟨A, hA⟩ : ∃ A : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ,
      A = fun j => if j ∈ Xs then indepLaw c (m j) else N j := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ,
      R = fun j => if j ∈ Xs then c.diagonalLaw (m j) - indepLaw c (m j) else 0 := ⟨_, rfl⟩
  have hsum : (fun j => A j + R j) = fun j => if j ∈ Xs then c.diagonalLaw (m j) else N j := by
    funext j
    by_cases hj : j ∈ Xs
    · simp [hA, hR, hj]
    · simp [hA, hR, hj]
  have hexp := energy_add_eq_sum A R F
  rw [hsum] at hexp
  rw [hexp]
  have hterm_nn : ∀ f : J → Bool,
      0 ≤ diagonalIntegral (tensorLaw fun b => if f b then R b else A b) F := by
    intro f
    apply energy_nonneg_of_positive c
    intro b
    by_cases hb : f b = true
    · simp only [hb, ↓reduceIte, hR]
      by_cases hbX : b ∈ Xs
      · simp only [hbX, ↓reduceIte]
        exact positive_diagonal_sub_indep c (hm b hbX)
      · simp only [hbX, ↓reduceIte]
        exact positive_zero c
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, hA]
      by_cases hbX : b ∈ Xs
      · simp only [hbX, ↓reduceIte]
        exact positive_indepLaw c (hm b hbX)
      · simp only [hbX, ↓reduceIte]
        exact hNpos b hbX
  obtain ⟨fX, hfX⟩ : ∃ fX : J → Bool, fX = fun b => decide (b ∈ Xs) := ⟨_, rfl⟩
  obtain ⟨f0, hf0⟩ : ∃ f0 : J → Bool, f0 = fun _ => false := ⟨_, rfl⟩
  have hne : fX ≠ f0 := by
    obtain ⟨j, hj⟩ := hXs
    intro h
    have := congrFun h j
    simp [hfX, hf0, hj] at this
  have hX : diagonalIntegral (tensorLaw fun b => if fX b then R b else A b) F =
      diagonalIntegral (tensorLaw K) F := by
    congr 2
    funext b
    by_cases hb : b ∈ Xs
    · simp [hfX, hR, hK, hb]
    · simp [hfX, hA, hK, hb]
  have h0 : diagonalIntegral (tensorLaw fun b => if f0 b then R b else A b) F =
      diagonalIntegral (tensorLaw A) F := by
    simp [hf0]
  have hpair : diagonalIntegral (tensorLaw fun b => if fX b then R b else A b) F +
      diagonalIntegral (tensorLaw fun b => if f0 b then R b else A b) F ≤
      ∑ f : J → Bool, diagonalIntegral (tensorLaw fun b => if f b then R b else A b) F := by
    exact add_le_sum (fun f _ => hterm_nn f) (mem_univ fX) (mem_univ f0) hne
  rw [hX, h0] at hpair
  rw [← hA]
  linarith

end Sarkozy.Variance
