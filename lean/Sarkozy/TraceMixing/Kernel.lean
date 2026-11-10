module

public import Sarkozy.Mixing.Main
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Symmetric conditional operators and square-affine invariant kernels

Two ingredients of `lem:trace-mixing` (`paper/sections/12_labellings.tex`):

* `srcWeight_equiv`, `tgtWeight_equiv`, `condMatrix_equiv`, `gram_equiv`: if a joint law
  `κ` on `A × B` is invariant under a pair of bijections `(σ, τ)`, then so are its marginals,
  its conditional operator `T` (`T(τ b, σ a) = T(b, a)`) and the kernel
  `G = T^* T` (`gram`, in the Euclidean coordinates of `A`): `G(σ a, σ a') = G(a, a')`. This
  is "`S = T^*T` commutes with the unitaries `f ↦ f ∘ g`" of the proof.
* `twin_bound`: a positive semidefinite kernel `M` on a finite field `F` of odd characteristic
  that is invariant under the translations and the square dilations satisfies, for every
  `f` with `∑_x f(x) = 0`,
  `⟨f, M f⟩ ≤ 2/(q(q-1)) · (q tr M - ∑_{x,x'} M(x,x')) · ∑_x f(x)²`, `q = |F|`.

  This is the trace step of `lem:trace-mixing`(a). The paper diagonalizes `S` in the additive
  characters, with eigenvalues `κ₊`, `κ₋` on the squares and non-squares, and uses
  `max(κ₊, κ₋) ≤ κ₊ + κ₋`. Here the same inequality is proved without characters: for a
  non-square `ν` and `g(x) = f(νx)`, `⟨f, M f⟩ + ⟨g, M g⟩ = (2m₀ - m₊ - m₋) ∑ f²`, where
  `M(x, x') = m(x' - x)` and `m` takes the values `m₀`, `m₊`, `m₋` at `0`, the squares and the
  non-squares; and `⟨g, M g⟩ ≥ 0`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing

section Joint

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The source marginal of an invariant joint law is invariant. -/
theorem srcWeight_equiv (κ : FiniteLaw (A × B)) (σ : A ≃ A) (τ : B ≃ B)
    (h : ∀ a b, κ.weight (σ a, τ b) = κ.weight (a, b)) (a : A) :
    srcWeight κ (σ a) = srcWeight κ a := by
  unfold srcWeight
  calc ∑ b, κ.weight (σ a, b) = ∑ b, κ.weight (σ a, τ b) :=
        (Equiv.sum_comp τ (fun b => κ.weight (σ a, b))).symm
    _ = ∑ b, κ.weight (a, b) := by simp only [h]

/-- The target marginal of an invariant joint law is invariant. -/
theorem tgtWeight_equiv (κ : FiniteLaw (A × B)) (σ : A ≃ A) (τ : B ≃ B)
    (h : ∀ a b, κ.weight (σ a, τ b) = κ.weight (a, b)) (b : B) :
    tgtWeight κ (τ b) = tgtWeight κ b := by
  unfold tgtWeight
  calc ∑ a, κ.weight (a, τ b) = ∑ a, κ.weight (σ a, τ b) :=
        (Equiv.sum_comp σ (fun a => κ.weight (a, τ b))).symm
    _ = ∑ a, κ.weight (a, b) := by simp only [h]

/-- The conditional operator of an invariant joint law commutes with the symmetry. -/
theorem condMatrix_equiv (κ : FiniteLaw (A × B)) (σ : A ≃ A) (τ : B ≃ B)
    (h : ∀ a b, κ.weight (σ a, τ b) = κ.weight (a, b)) (b : B) (a : A) :
    condMatrix κ (τ b) (σ a) = condMatrix κ b a := by
  unfold condMatrix
  rw [tgtWeight_equiv κ σ τ h, srcWeight_equiv κ σ τ h, h]

/-- **`S = T^* T` commutes with the symmetry**: `G(σ a, σ a') = G(a, a')`. -/
theorem gram_equiv (κ : FiniteLaw (A × B)) (σ : A ≃ A) (τ : B ≃ B)
    (h : ∀ a b, κ.weight (σ a, τ b) = κ.weight (a, b)) (a a' : A) :
    gram κ (σ a) (σ a') = gram κ a a' := by
  unfold gram
  calc ∑ b, tgtWeight κ b * condMatrix κ b (σ a) * condMatrix κ b (σ a')
      = ∑ b, tgtWeight κ (τ b) * condMatrix κ (τ b) (σ a) * condMatrix κ (τ b) (σ a') :=
        (Equiv.sum_comp τ (fun b => tgtWeight κ b * condMatrix κ b (σ a) *
          condMatrix κ b (σ a'))).symm
    _ = ∑ b, tgtWeight κ b * condMatrix κ b a * condMatrix κ b a' := by
        simp only [tgtWeight_equiv κ σ τ h, condMatrix_equiv κ σ τ h]

/-- The Gram kernel is positive semidefinite. -/
theorem gram_quadratic_nonneg (κ : FiniteLaw (A × B)) (f : A → ℝ) :
    0 ≤ f ⬝ᵥ (gram κ *ᵥ f) := by
  rw [← energy_eq_gram]
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (tgtWeight_nonneg κ b) (sq_nonneg _))

/-- The total mass of the Gram kernel is `‖T 1‖² = 1`. -/
theorem gram_total (κ : FiniteLaw (A × B)) : ∑ a, ∑ a', gram κ a a' = 1 := by
  have h := energy_eq_gram κ (fun _ => (1 : ℝ))
  have h1 : ∀ b, condOp κ (fun _ => (1 : ℝ)) b = 1 := fun b => by
    simp only [condOp, Matrix.mulVec, dotProduct, mul_one]
    exact condMatrix_row_sum κ b
  simp only [h1, one_pow, mul_one, sum_tgtWeight, dotProduct, Matrix.mulVec, one_mul] at h
  exact h.symm

/-- The trace of the Gram kernel, `∑_a G(a, a) = ∑_b κ_B(b) ∑_a T(b, a)²`. -/
theorem gram_trace (κ : FiniteLaw (A × B)) :
    Matrix.trace (gram κ) = ∑ b, tgtWeight κ b * ∑ a, condMatrix κ b a ^ 2 := by
  have h (a : A) : gram κ a a = ∑ b, tgtWeight κ b * condMatrix κ b a ^ 2 := by
    simp only [gram, sq, mul_assoc]
  calc Matrix.trace (gram κ) = ∑ a, gram κ a a := rfl
    _ = ∑ a, ∑ b, tgtWeight κ b * condMatrix κ b a ^ 2 := by simp only [h]
    _ = ∑ b, ∑ a, tgtWeight κ b * condMatrix κ b a ^ 2 := Finset.sum_comm
    _ = ∑ b, tgtWeight κ b * ∑ a, condMatrix κ b a ^ 2 := by simp only [Finset.mul_sum]

end Joint

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- In a field, `q ≥ 2`. -/
theorem card_field_ge_two : (2 : ℝ) ≤ Fintype.card F := by
  have h : 2 ≤ Fintype.card F := Fintype.one_lt_card
  exact_mod_cast h

/-- Elements of equal quadratic character are related by a square dilation. -/
theorem quadraticChar_ratio {a b : F} (ha : a ≠ 0) (hab : quadraticChar F a = quadraticChar F b) :
    quadraticChar F (b * a⁻¹) = 1 := by
  rw [map_mul, ← hab, ← map_mul, mul_inv_cancel₀ ha, map_one]

/-- **The twin bound.** A positive semidefinite kernel `M` on a finite field `F` of odd
characteristic, invariant under translations and square dilations, satisfies
`⟨f, M f⟩ ≤ 2/(q(q-1)) · (q tr M - ∑_{x,x'} M(x,x')) · ∑ f²` on functions of sum zero. -/
theorem twin_bound (hF : ringChar F ≠ 2) (M : Matrix F F ℝ) (hpsd : ∀ f, 0 ≤ f ⬝ᵥ (M *ᵥ f))
    (htr : ∀ x x' β : F, M (x + β) (x' + β) = M x x')
    (hdil : ∀ α : F, quadraticChar F α = 1 → ∀ x x' : F, M (α * x) (α * x') = M x x')
    (f : F → ℝ) (hf : ∑ x, f x = 0) :
    f ⬝ᵥ (M *ᵥ f) ≤ 2 / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) *
      ((Fintype.card F : ℝ) * Matrix.trace M - ∑ x, ∑ x', M x x') * ∑ x, f x ^ 2 := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq2 : 2 ≤ q := card_field_ge_two
  -- the kernel is a function of the difference
  set m : F → ℝ := fun δ => M 0 δ with hm
  have hM (x x' : F) : M x x' = m (x' - x) := by
    have h := htr x x' (-x)
    rw [add_neg_cancel, ← sub_eq_add_neg] at h
    exact h.symm
  -- `m` depends only on the quadratic character of a nonzero argument
  have hclass {a b : F} (ha : a ≠ 0) (hab : quadraticChar F a = quadraticChar F b) :
      m a = m b := by
    have h := hdil (b * a⁻¹) (quadraticChar_ratio ha hab) 0 a
    rw [mul_zero, mul_assoc, inv_mul_cancel₀ ha, mul_one] at h
    simp only [hm]
    exact h.symm
  -- a non-square
  obtain ⟨ν, hνsq⟩ := FiniteField.exists_nonsquare hF
  have hν : quadraticChar F ν = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hνsq
  have hν0 : ν ≠ 0 := fun h => hνsq (h ▸ IsSquare.zero)
  have hνinv : quadraticChar F ν⁻¹ = -1 := by
    have h1 : quadraticChar F ν⁻¹ * quadraticChar F ν = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hν0, map_one]
    rw [hν] at h1
    linarith
  have hone : quadraticChar F (1 : F) = 1 := map_one _
  -- the twin sum is constant off the diagonal
  have hpair (δ : F) (hδ : δ ≠ 0) : m δ + m (ν⁻¹ * δ) = m 1 + m ν := by
    have hνδ : ν⁻¹ * δ ≠ 0 := mul_ne_zero (inv_ne_zero hν0) hδ
    rcases quadraticChar_dichotomy hδ with h | h
    · have h1 : m δ = m 1 := hclass hδ (by rw [h, hone])
      have h2 : m (ν⁻¹ * δ) = m ν := hclass hνδ (by rw [map_mul, h, hνinv, hν]; ring)
      rw [h1, h2]
    · have h1 : m δ = m ν := hclass hδ (by rw [h, hν])
      have h2 : m (ν⁻¹ * δ) = m 1 := hclass hνδ (by rw [map_mul, h, hνinv, hone]; ring)
      rw [h1, h2, add_comm]
  set c : ℝ := m 1 + m ν with hc
  have hcδ (δ : F) : m δ + m (ν⁻¹ * δ) = c + (if δ = 0 then 2 * m 0 - c else 0) := by
    by_cases hδ : δ = 0
    · subst hδ
      simp only [mul_zero, ite_true]
      ring
    · rw [hpair δ hδ, ite_eq_right hδ, add_zero]
  -- the quadratic forms as double sums
  have hquad (g : F → ℝ) : g ⬝ᵥ (M *ᵥ g) = ∑ y, ∑ y', g y * g y' * m (y' - y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hM]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro y' _
    ring
  set g : F → ℝ := fun x => f (ν * x) with hg
  have htwin : g ⬝ᵥ (M *ᵥ g) = ∑ y, ∑ y', f y * f y' * m (ν⁻¹ * (y' - y)) := by
    rw [hquad]
    have e := Equiv.mulLeft₀ ν hν0
    have hsum : ∀ H : F → F → ℝ, ∑ x, ∑ x', H (ν * x) (ν * x') = ∑ y, ∑ y', H y y' := by
      intro H
      rw [← Equiv.sum_comp (Equiv.mulLeft₀ ν hν0) (fun y => ∑ y', H y y')]
      apply sum_congr rfl
      intro x _
      exact Equiv.sum_comp (Equiv.mulLeft₀ ν hν0) (fun y' => H ((Equiv.mulLeft₀ ν hν0) x) y')
    have := hsum (fun y y' => f y * f y' * m (ν⁻¹ * (y' - y)))
    rw [← this]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro x' _
    simp only [hg]
    congr 2
    rw [← mul_sub, ← mul_assoc, inv_mul_cancel₀ hν0, one_mul]
  -- the twin identity
  have hident : f ⬝ᵥ (M *ᵥ f) + g ⬝ᵥ (M *ᵥ g) = (2 * m 0 - c) * ∑ x, f x ^ 2 := by
    rw [hquad f, htwin, ← Finset.sum_add_distrib]
    have h1 (y : F) : ∑ y', f y * f y' * m (y' - y) + ∑ y', f y * f y' * m (ν⁻¹ * (y' - y)) =
        c * (f y * ∑ y', f y') + (2 * m 0 - c) * f y ^ 2 := by
      rw [← Finset.sum_add_distrib]
      have h2 (y' : F) : f y * f y' * m (y' - y) + f y * f y' * m (ν⁻¹ * (y' - y)) =
          c * (f y * f y') + (if y' = y then (2 * m 0 - c) * f y ^ 2 else 0) := by
        rw [← mul_add, hcδ (y' - y)]
        by_cases hy : y' = y
        · subst hy
          simp only [sub_self, ite_true]
          ring
        · have hne : y' - y ≠ 0 := sub_ne_zero.mpr hy
          rw [ite_eq_right hne, ite_eq_right hy]
          ring
      simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp only [h1, Finset.sum_add_distrib]
    rw [hf]
    simp only [mul_zero, sum_const_zero, zero_add]
    rw [← Finset.mul_sum]
  -- trace and total mass
  have htrace : Matrix.trace M = q * m 0 := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, hM, sub_self, sum_const, card_univ, nsmul_eq_mul, hq]
  have hmsum : 2 * ∑ δ, m δ = q * c + (2 * m 0 - c) := by
    have h1 : ∑ δ, m (ν⁻¹ * δ) = ∑ δ, m δ :=
      Equiv.sum_comp (Equiv.mulLeft₀ ν⁻¹ (inv_ne_zero hν0)) m
    have h2 : ∑ δ, (m δ + m (ν⁻¹ * δ)) = q * c + (2 * m 0 - c) := by
      simp only [hcδ, Finset.sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
        Finset.sum_ite_eq', mem_univ, ite_true, hq]
    rw [Finset.sum_add_distrib, h1] at h2
    linarith
  have htotal : ∑ x, ∑ x', M x x' = q * ∑ δ, m δ := by
    have h (x : F) : ∑ x', M x x' = ∑ δ, m δ := by
      simp only [hM]
      exact Equiv.sum_comp (Equiv.subRight x) m
    simp only [h, sum_const, card_univ, nsmul_eq_mul, hq]
  have hcoef : 2 / (q * (q - 1)) * (q * Matrix.trace M - ∑ x, ∑ x', M x x') = 2 * m 0 - c := by
    rw [htrace, htotal]
    have hq0 : q ≠ 0 := by linarith
    have hq1 : q - 1 ≠ 0 := by linarith
    field_simp
    linarith [hmsum]
  rw [hcoef]
  have := hpsd g
  linarith

end Field

end Sarkozy.TraceMixing
