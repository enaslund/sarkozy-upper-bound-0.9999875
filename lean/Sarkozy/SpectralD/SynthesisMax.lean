module

public import Sarkozy.SpectralC.All
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-!
# The synthesis bound in the `λ_max` form (`lem:general-star`(f))

`paper/sections/14_spectral.tex`, `lem:general-star`(f): for the features `F_α` of a set of
supports (singletons `V_i`, stars `W_S/r`) and a symmetric nonnegative matrix `N` with
`‖F_α^*F_β‖ ≤ N_αβ` for `α ≠ β`, the synthesis `𝓕((h_α)_α) = ∑_α F_α h_α` satisfies
`‖𝓕‖² ≤ 1 + λ_max(N) ≤ 1 + max_α ∑_β N_αβ`.

WP-K proved the row-sum form (`SpectralC.synthesis_bound`). This file proves the `λ_max` form:

* `synthesis_bound_quad`: if `λ` bounds the quadratic form of `N` on nonnegative vectors,
  `∑_{α,β} N_αβ t_α t_β ≤ λ ∑_α t_α²` (in particular if `λ ≥ λ_max(N)` for symmetric `N`), then
  `‖∑_α F_α h_α‖² ≤ (1 + λ) ∑_α ‖h_α‖²`. The diagonal entries of `N` are unconstrained (they
  enter the quadratic form with `t_α² ≥ 0`), as in the paper.
* `quad_le_rowSum`: for symmetric nonnegative `N`, the largest row sum `max_α ∑_β N_αβ` is such
  a `λ` (the second inequality of (f), by the Schur test).
* `quad_le_eigenvalue_sup`: for a real symmetric matrix `N` (`Matrix.IsHermitian`),
  `∑_{α,β} N_αβ t_α t_β ≤ λ_max(N) ∑_α t_α²` for every real `t`, where `λ_max(N)` is the
  largest of Mathlib's eigenvalues `Matrix.IsHermitian.eigenvalues` (spectral theorem). With
  `synthesis_bound_quad` this is literally `‖𝓕‖² ≤ 1 + λ_max(N)`
  (`synthesis_bound_eigenvalue`).

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- **`lem:general-star`(f), the `λ_max` form**: for features `F_α` (real kernels `Y α`) with
`‖F_α h‖ ≤ ‖h‖` and `|⟨F_α h, F_β h'⟩| ≤ N_αβ ‖h‖ ‖h'‖` for `α ≠ β` on `L²_0`, `N ≥ 0`, and a
number `λ` with `∑_{α,β} N_αβ t_α t_β ≤ λ ∑_α t_α²` for `t ≥ 0`:
`‖∑_α F_α h_α‖² ≤ (1 + λ) ∑_α ‖h_α‖²`. -/
theorem synthesis_bound_quad {𝒴 ι : Type*} [Fintype 𝒴] [Fintype ι] [DecidableEq ι]
    (ν : 𝒴 → ℝ) (Y : ι → 𝒴 → ZMod p → ℝ) (N : ι → ι → ℝ) (hN0 : ∀ a b, 0 ≤ N a b) {lam : ℝ}
    (hlam : ∀ t : ι → ℝ, (∀ a, 0 ≤ t a) → ∑ a, ∑ b, N a b * t a * t b ≤ lam * ∑ a, t a ^ 2)
    (hdiag : ∀ (a : ι) (h : ZMod p → ℂ), meanC h = 0 →
      ∑ y, ν y * ‖kerMap (Y a) h y‖ ^ 2 ≤ l2sq h)
    (hoff : ∀ a b : ι, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ y, (ν y : ℂ) * (conj (kerMap (Y a) h y) * kerMap (Y b) h' y)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (h : ι → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 ≤ (1 + lam) * ∑ a, l2sq (h a) := by
  set G : ι → ι → ℂ := fun a b =>
    ∑ y, (ν y : ℂ) * (conj (kerMap (Y a) (h a) y) * kerMap (Y b) (h b) y) with hG
  set t : ι → ℝ := fun a => Real.sqrt (l2sq (h a)) with ht
  have hl2 : ∀ a, 0 ≤ l2sq (h a) := fun a => by unfold l2sq; positivity
  have ht2 : ∀ a, t a ^ 2 = l2sq (h a) := fun a => Real.sq_sqrt (hl2 a)
  have ht0 : ∀ a, 0 ≤ t a := fun a => Real.sqrt_nonneg _
  -- expand the square
  have hexp : ∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 = ∑ a, ∑ b, (G a b).re := by
    have hC : ((∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 : ℝ) : ℂ) = ∑ a, ∑ b, G a b := by
      push_cast
      simp only [hG]
      have hy : ∀ y, (ν y : ℂ) * (‖∑ a, kerMap (Y a) (h a) y‖ : ℂ) ^ 2 =
          ∑ a, ∑ b, (ν y : ℂ) * (conj (kerMap (Y a) (h a) y) * kerMap (Y b) (h b) y) := by
        intro y
        rw [← Complex.conj_mul', map_sum, sum_mul_sum, mul_sum]
        exact sum_congr rfl fun a _ => by rw [mul_sum]
      rw [sum_congr rfl fun y _ => hy y, sum_comm]
      exact sum_congr rfl fun a _ => sum_comm
    have := congrArg Complex.re hC
    rw [Complex.ofReal_re, Complex.re_sum] at this
    rw [this]
    exact sum_congr rfl fun a _ => Complex.re_sum _ _
  -- each entry is bounded by `δ_ab ‖h_a‖² + N_ab t_a t_b`
  have hent : ∀ a b, (G a b).re ≤ (if a = b then l2sq (h a) else 0) + N a b * t a * t b := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte]
      have h1 : (G a a).re = ∑ y, ν y * ‖kerMap (Y a) (h a) y‖ ^ 2 := by
        simp only [hG]
        rw [Complex.re_sum]
        refine sum_congr rfl fun y _ => ?_
        rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [h1]
      have h2 := hdiag a (h a) (hh a)
      have h3 : 0 ≤ N a a * t a * t a := mul_nonneg (mul_nonneg (hN0 a a) (ht0 a)) (ht0 a)
      linarith
    · simp only [hab, ↓reduceIte, zero_add]
      exact (Complex.re_le_norm _).trans (hoff a b hab (h a) (h b) (hh a) (hh b))
  rw [hexp]
  calc ∑ a, ∑ b, (G a b).re
      ≤ ∑ a, ∑ b, ((if a = b then l2sq (h a) else 0) + N a b * t a * t b) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hent a b
    _ = ∑ a, l2sq (h a) + ∑ a, ∑ b, N a b * t a * t b := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_add_distrib, sum_ite_eq]
        simp only [mem_univ, ↓reduceIte]
    _ ≤ ∑ a, l2sq (h a) + lam * ∑ a, t a ^ 2 := add_le_add (le_refl _) (hlam t ht0)
    _ = (1 + lam) * ∑ a, l2sq (h a) := by
        rw [sum_congr rfl fun a _ => ht2 a]; ring

/-- **The second inequality of `lem:general-star`(f)** (Schur test): for symmetric nonnegative
`N` whose row sums are at most `ρ`, `∑_{α,β} N_αβ t_α t_β ≤ ρ ∑_α t_α²` for every real `t`. -/
theorem quad_le_rowSum {ι : Type*} [Fintype ι] (N : ι → ι → ℝ) (hN0 : ∀ a b, 0 ≤ N a b)
    (hNsym : ∀ a b, N a b = N b a) {ρ : ℝ} (hrow : ∀ a, ∑ b, N a b ≤ ρ) (t : ι → ℝ) :
    ∑ a, ∑ b, N a b * t a * t b ≤ ρ * ∑ a, t a ^ 2 := by
  have h1 : ∀ a b, N a b * t a * t b ≤ N a b * t a ^ 2 / 2 + N a b * t b ^ 2 / 2 := by
    intro a b
    nlinarith [mul_nonneg (hN0 a b) (sq_nonneg (t a - t b))]
  have hrow' : ∀ b, ∑ a, N a b ≤ ρ := fun b => by
    rw [sum_congr rfl fun a _ => hNsym a b]; exact hrow b
  calc ∑ a, ∑ b, N a b * t a * t b
      ≤ ∑ a, ∑ b, (N a b * t a ^ 2 / 2 + N a b * t b ^ 2 / 2) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => h1 a b
    _ = (∑ a, t a ^ 2 * ∑ b, N a b) / 2 + (∑ b, t b ^ 2 * ∑ a, N a b) / 2 := by
        have e1 : ∑ a, ∑ b, N a b * t a ^ 2 / 2 = (∑ a, t a ^ 2 * ∑ b, N a b) / 2 := by
          rw [sum_div]
          exact sum_congr rfl fun a _ => by
            rw [mul_sum, sum_div]; exact sum_congr rfl fun b _ => by ring
        have e2 : ∑ a, ∑ b, N a b * t b ^ 2 / 2 = (∑ b, t b ^ 2 * ∑ a, N a b) / 2 := by
          rw [sum_comm, sum_div]
          exact sum_congr rfl fun b _ => by
            rw [mul_sum, sum_div]; exact sum_congr rfl fun a _ => by ring
        simp only [sum_add_distrib]
        rw [e1, e2]
    _ ≤ (∑ a, t a ^ 2 * ρ) / 2 + (∑ b, t b ^ 2 * ρ) / 2 := by
        gcongr with a _ b _
        · exact hrow a
        · exact hrow' b
    _ = ρ * ∑ a, t a ^ 2 := by rw [← sum_mul]; ring

/-- **`lem:general-star`(f), both inequalities, row-sum route**: with the hypotheses of
`synthesis_bound_quad` and `N` symmetric with row sums at most `ρ`,
`‖∑_α F_α h_α‖² ≤ (1 + ρ) ∑_α ‖h_α‖²` (here the row sums include the diagonal of `N`). -/
theorem synthesis_bound_rowSum {𝒴 ι : Type*} [Fintype 𝒴] [Fintype ι] [DecidableEq ι]
    (ν : 𝒴 → ℝ) (Y : ι → 𝒴 → ZMod p → ℝ) (N : ι → ι → ℝ) (hN0 : ∀ a b, 0 ≤ N a b)
    (hNsym : ∀ a b, N a b = N b a) {ρ : ℝ} (hrow : ∀ a, ∑ b, N a b ≤ ρ)
    (hdiag : ∀ (a : ι) (h : ZMod p → ℂ), meanC h = 0 →
      ∑ y, ν y * ‖kerMap (Y a) h y‖ ^ 2 ≤ l2sq h)
    (hoff : ∀ a b : ι, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ y, (ν y : ℂ) * (conj (kerMap (Y a) h y) * kerMap (Y b) h' y)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (h : ι → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 ≤ (1 + ρ) * ∑ a, l2sq (h a) :=
  synthesis_bound_quad ν Y N hN0 (fun t _ => quad_le_rowSum N hN0 hNsym hrow t) hdiag hoff h hh

open Matrix in
/-- **`λ_max` bounds the quadratic form** (the Rayleigh bound, from the spectral theorem): for a
real symmetric matrix `N` and every real `t`,
`∑_{α,β} N_αβ t_α t_β ≤ λ_max(N) ∑_α t_α²`, with `λ_max(N) = max_i` of Mathlib's eigenvalues. -/
theorem quad_le_eigenvalue_sup {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℝ)
    (hN : N.IsHermitian) (t : ι → ℝ) :
    ∑ a, ∑ b, N a b * t a * t b ≤ (⨆ i, hN.eigenvalues i) * ∑ a, t a ^ 2 := by
  set v : EuclideanSpace ℝ ι := WithLp.toLp 2 t with hv
  set B := hN.eigenvectorBasis with hB
  set c : ι → ℝ := fun i => inner ℝ (B i) v with hc
  have hvt : v.ofLp = t := rfl
  have ht : t = ∑ i, c i • (B i).ofLp := by
    have h1 := congrArg WithLp.ofLp (B.sum_repr v)
    rw [hvt] at h1
    rw [← h1, WithLp.ofLp_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [WithLp.ofLp_smul, B.repr_apply_apply]
  have hdot : ∀ i, t ⬝ᵥ (B i).ofLp = c i := by
    intro i
    simp only [hc]
    rw [EuclideanSpace.inner_eq_star_dotProduct, hvt, star_trivial, dotProduct_comm]
  have hQ : ∑ a, ∑ b, N a b * t a * t b = t ⬝ᵥ (N *ᵥ t) := by
    simp only [dotProduct, mulVec, mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hNt : N *ᵥ t = ∑ i, (c i * hN.eigenvalues i) • (B i).ofLp := by
    conv_lhs => rw [ht]
    rw [mulVec_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mulVec_smul, hN.mulVec_eigenvectorBasis i, smul_smul]
  have hQ2 : t ⬝ᵥ (N *ᵥ t) = ∑ i, hN.eigenvalues i * c i ^ 2 := by
    rw [hNt, dotProduct_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [dotProduct_smul, hdot i, smul_eq_mul]
    ring
  have hpars : ∑ i, c i ^ 2 = ∑ a, t a ^ 2 := by
    have h1 := B.sum_sq_norm_inner_right v
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)] at h1
    simp only [Real.norm_eq_abs, sq_abs] at h1
    rw [hvt] at h1
    exact h1
  rw [hQ, hQ2, ← hpars, mul_sum]
  refine sum_le_sum fun i _ => ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact le_ciSup (Set.finite_range _).bddAbove i

/-- **`lem:general-star`(f), `‖𝓕‖² ≤ 1 + λ_max(N)`**: with the hypotheses of
`synthesis_bound_quad` for a real symmetric nonnegative matrix `N`,
`‖∑_α F_α h_α‖² ≤ (1 + λ_max(N)) ∑_α ‖h_α‖²`, `λ_max(N)` the largest eigenvalue. -/
theorem synthesis_bound_eigenvalue {𝒴 ι : Type*} [Fintype 𝒴] [Fintype ι] [DecidableEq ι]
    (ν : 𝒴 → ℝ) (Y : ι → 𝒴 → ZMod p → ℝ) (N : Matrix ι ι ℝ) (hN : N.IsHermitian)
    (hN0 : ∀ a b, 0 ≤ N a b)
    (hdiag : ∀ (a : ι) (h : ZMod p → ℂ), meanC h = 0 →
      ∑ y, ν y * ‖kerMap (Y a) h y‖ ^ 2 ≤ l2sq h)
    (hoff : ∀ a b : ι, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ y, (ν y : ℂ) * (conj (kerMap (Y a) h y) * kerMap (Y b) h' y)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (h : ι → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 ≤
      (1 + ⨆ i, hN.eigenvalues i) * ∑ a, l2sq (h a) :=
  synthesis_bound_quad ν Y (fun a b => N a b) hN0 (fun t _ => quad_le_eigenvalue_sup N hN t)
    hdiag hoff h hh

end Sarkozy.SpectralD
