module

public import Sarkozy.Spectral.RouteB

/-!
# `lem:record:frame-inputs` (ii), (iii): the matrix steps

`paper/sections/14_spectral.tex`, `lem:record:frame-inputs`, the finite-dimensional steps of
(ii) and (iii), for bilinear forms `u^* N v` on `𝕜ⁿ` (`‖N‖ ≤ c` is `|u^* N v| ≤ c |u||v|`).

* `bilin_ones_le`: `|u^* 𝟙𝟙ᵀ v| ≤ n |u||v|`.
* `bilin_schur`: the Schur test, `|u^* M v| ≤ (R C)^{1/2} |u||v|` when `|M_ik| ≤ Φ_ik` with
  row sums of `Φ` at most `R` and column sums at most `C`; `quad_le_row`: for a matrix with
  `|H_kl| ≤ Φ_kl`, `Φ` symmetric with row sums at most `‖𝐇‖_row`, `|w^* H w| ≤ ‖𝐇‖_row |w|²`.
* `frame_inputs_ii`: (ii), the bound `ε_×`. If on a mode
  `𝐄^*𝐁/r - A(ξ) = a 𝟙𝟙ᵀ + b A(ξ) + d M^off` with `|a| ≤ 1/((p-1)r)`, `|b| ≤ 1/(p-1)`,
  `|d| ≤ p/(p-1)`, `‖A(ξ)‖ ≤ Λ_D` and `|M^off_ik| ≤ φ_k [ς_ik = 0]`, then its norm is at most
  `ε_× = n/((p-1)r) + Λ_D/(p-1) + p/(p-1) (max_i ∑_{k:ς_ik=0} φ_k · max_k ∑_{i:ς_ik=0} φ_k)^{1/2}`.
  The decomposition (from `lem:spec:affpair` (b)) and the entry bound `|m_ik| ≤ φ_k` are
  hypotheses.
* `frame_inputs_iii`: (iii), the last chain: from `w^*𝐁^*𝐁w/r² ≤ p/(p-1) (w^*𝐇⁰w + δ)` with
  `w^*𝐇⁰w ≤ w^*𝐇w + ε'_H|w|²` (`lem:spec2:gram`), `|δ| ≤ (ε_≠ + ε_rem)|w|²`
  (`lem:spec2:paley` and `|p c_ξ| r = 1`) and `w^*𝐇w ≤ ‖𝐇‖_row |w|²`, it gives
  `w^*𝐁^*𝐁w/r² ≤ w^*𝐇w + ε_𝐁|w|²` with
  `ε_𝐁 = (p/(p-1) - 1)‖𝐇‖_row + p/(p-1)(ε'_H + ε_≠ + ε_rem)`. The identity for `𝐁^*𝐁` on the
  modes (`lem:coupling-modes`) and the two cited bounds are hypotheses.
-/

@[expose] public section

open scoped Matrix
open RCLike

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

omit [Fintype n] in
theorem sum_norm_le_sqrt [Fintype n] (u : n → 𝕜) :
    ∑ i, ‖u i‖ ≤ √(Fintype.card n) * √(sqn u) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => ‖u i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have h0 : 0 ≤ ∑ i, ‖u i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  calc ∑ i, ‖u i‖ = √((∑ i, ‖u i‖) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ √(Fintype.card n * sqn u) := Real.sqrt_le_sqrt h

/-- `|u^* 𝟙𝟙ᵀ v| ≤ n |u||v|`. -/
theorem bilin_ones_le (u v : n → 𝕜) :
    ‖star u ⬝ᵥ ((Matrix.of fun _ _ => (1 : 𝕜)) *ᵥ v)‖ ≤
      Fintype.card n * (√(sqn u) * √(sqn v)) := by
  have e : star u ⬝ᵥ ((Matrix.of fun _ _ => (1 : 𝕜)) *ᵥ v) = (∑ i, star (u i)) * ∑ k, v k := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, one_mul, Pi.star_apply,
      Finset.sum_mul]
  rw [e, norm_mul]
  have h1 : ‖∑ i, star (u i)‖ ≤ ∑ i, ‖u i‖ :=
    (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_star _)
  have h2 : ‖∑ k, v k‖ ≤ ∑ k, ‖v k‖ := norm_sum_le _ _
  have hn := Real.mul_self_sqrt (Nat.cast_nonneg (α := ℝ) (Fintype.card n))
  calc ‖∑ i, star (u i)‖ * ‖∑ k, v k‖ ≤ (∑ i, ‖u i‖) * ∑ k, ‖v k‖ :=
        mul_le_mul h1 h2 (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg _)
    _ ≤ (√(Fintype.card n) * √(sqn u)) * (√(Fintype.card n) * √(sqn v)) :=
        mul_le_mul (sum_norm_le_sqrt u) (sum_norm_le_sqrt v)
          (Finset.sum_nonneg fun i _ => norm_nonneg _) (by positivity)
    _ = (√(Fintype.card n) * √(Fintype.card n)) * (√(sqn u) * √(sqn v)) := by ring
    _ = Fintype.card n * (√(sqn u) * √(sqn v)) := by rw [hn]

/-- **The Schur test** for a bilinear form. -/
theorem bilin_schur (M : Matrix n n 𝕜) (Φ : n → n → ℝ) (hΦ0 : ∀ i k, 0 ≤ Φ i k)
    (hΦ : ∀ i k, ‖M i k‖ ≤ Φ i k) {R C : ℝ} (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hR : ∀ i, ∑ k, Φ i k ≤ R) (hC : ∀ k, ∑ i, Φ i k ≤ C) (u v : n → 𝕜) :
    ‖star u ⬝ᵥ (M *ᵥ v)‖ ≤ √(R * C) * (√(sqn u) * √(sqn v)) := by
  -- the triangle inequality
  have h1 : ‖star u ⬝ᵥ (M *ᵥ v)‖ ≤ ∑ i, ∑ k, √(Φ i k) * ‖u i‖ * (√(Φ i k) * ‖v k‖) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun k _ => ?_))
    rw [norm_mul, norm_mul, norm_star]
    have hs := Real.mul_self_sqrt (hΦ0 i k)
    calc ‖u i‖ * (‖M i k‖ * ‖v k‖) ≤ ‖u i‖ * (Φ i k * ‖v k‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hΦ i k) (norm_nonneg _))
            (norm_nonneg _)
      _ = ‖u i‖ * ((√(Φ i k) * √(Φ i k)) * ‖v k‖) := by rw [hs]
      _ = √(Φ i k) * ‖u i‖ * (√(Φ i k) * ‖v k‖) := by ring
  -- Cauchy–Schwarz over the pairs `(i, k)`
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ ×ˢ Finset.univ)
    (fun x : n × n => √(Φ x.1 x.2) * ‖u x.1‖) (fun x : n × n => √(Φ x.1 x.2) * ‖v x.2‖)
  simp only [Finset.sum_product, mul_pow, Real.sq_sqrt (hΦ0 _ _)] at h2
  have hu : ∑ i, ∑ k, Φ i k * ‖u i‖ ^ 2 ≤ R * sqn u := by
    rw [sqn, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hR i) (sq_nonneg _)
  have hv : ∑ i, ∑ k, Φ i k * ‖v k‖ ^ 2 ≤ C * sqn v := by
    rw [Finset.sum_comm, sqn, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hC k) (sq_nonneg _)
  have hS0 : 0 ≤ ∑ i, ∑ k, √(Φ i k) * ‖u i‖ * (√(Φ i k) * ‖v k‖) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity
  have h3 : (∑ i, ∑ k, √(Φ i k) * ‖u i‖ * (√(Φ i k) * ‖v k‖)) ^ 2 ≤
      (√(R * C) * (√(sqn u) * √(sqn v))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hR0 hC0), Real.sq_sqrt (sqn_nonneg u),
      Real.sq_sqrt (sqn_nonneg v)]
    refine h2.trans ?_
    calc (∑ i, ∑ k, Φ i k * ‖u i‖ ^ 2) * ∑ i, ∑ k, Φ i k * ‖v k‖ ^ 2
        ≤ (R * sqn u) * (C * sqn v) :=
          mul_le_mul hu hv (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
            mul_nonneg (hΦ0 i k) (sq_nonneg _)) (mul_nonneg hR0 (sqn_nonneg u))
      _ = R * C * (sqn u * sqn v) := by ring
  exact h1.trans (abs_le_of_sq_le_sq' h3 (by positivity)).2

/-- **The row-sum bound** for a quadratic form: `|w^* H w| ≤ ‖𝐇‖_row |w|²` when
`|H_kl| ≤ Φ_kl` with `Φ` symmetric and its row sums at most `ρ`. -/
theorem quad_le_row (Hm : Matrix n n 𝕜) (Φ : n → n → ℝ) (hΦ0 : ∀ i k, 0 ≤ Φ i k)
    (hΦ : ∀ i k, ‖Hm i k‖ ≤ Φ i k) (hsymm : ∀ i k, Φ i k = Φ k i) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ i, ∑ k, Φ i k ≤ ρ) (w : n → 𝕜) : ‖star w ⬝ᵥ (Hm *ᵥ w)‖ ≤ ρ * sqn w := by
  have h := bilin_schur Hm Φ hΦ0 hΦ hρ0 hρ0 hρ (fun k => by
    simp_rw [hsymm _ k]
    exact hρ k) w w
  rwa [Real.sqrt_mul_self hρ0, Real.mul_self_sqrt (sqn_nonneg w)] at h

/-- **`lem:record:frame-inputs` (ii)**: `‖𝐄^*𝐁/r - A(ξ)‖ ≤ ε_×`, from the decomposition of the
matrix and the bounds on its three parts. -/
theorem frame_inputs_ii (N A M : Matrix n n 𝕜) (ca cb cd : 𝕜) (Φ : n → n → ℝ)
    {a b d Λ R C : ℝ} (hN : N = ca • (Matrix.of fun _ _ => (1 : 𝕜)) + cb • A + cd • M)
    (ha : ‖ca‖ ≤ a) (hb : ‖cb‖ ≤ b) (hd : ‖cd‖ ≤ d)
    (hA : ∀ u v, ‖star u ⬝ᵥ (A *ᵥ v)‖ ≤ Λ * (√(sqn u) * √(sqn v)))
    (hΦ0 : ∀ i k, 0 ≤ Φ i k) (hΦ : ∀ i k, ‖M i k‖ ≤ Φ i k) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (hR : ∀ i, ∑ k, Φ i k ≤ R) (hC : ∀ k, ∑ i, Φ i k ≤ C) (u v : n → 𝕜) :
    ‖star u ⬝ᵥ (N *ᵥ v)‖ ≤
      (a * Fintype.card n + b * Λ + d * √(R * C)) * (√(sqn u) * √(sqn v)) := by
  set X := √(sqn u) * √(sqn v) with hX
  have hX0 : 0 ≤ X := by positivity
  have e : star u ⬝ᵥ (N *ᵥ v) = ca * (star u ⬝ᵥ ((Matrix.of fun _ _ => (1 : 𝕜)) *ᵥ v)) +
      cb * (star u ⬝ᵥ (A *ᵥ v)) + cd * (star u ⬝ᵥ (M *ᵥ v)) := by
    rw [hN, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  rw [e]
  have h1 := bilin_ones_le u v
  have h2 := hA u v
  have h3 := bilin_schur M Φ hΦ0 hΦ hR0 hC0 hR hC u v
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  calc ‖ca * (star u ⬝ᵥ ((Matrix.of fun _ _ => (1 : 𝕜)) *ᵥ v)) + cb * (star u ⬝ᵥ (A *ᵥ v)) +
        cd * (star u ⬝ᵥ (M *ᵥ v))‖
      ≤ ‖ca‖ * ‖star u ⬝ᵥ ((Matrix.of fun _ _ => (1 : 𝕜)) *ᵥ v)‖ +
          ‖cb‖ * ‖star u ⬝ᵥ (A *ᵥ v)‖ + ‖cd‖ * ‖star u ⬝ᵥ (M *ᵥ v)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
        · rw [norm_mul, norm_mul]
        · rw [norm_mul]
    _ ≤ a * (Fintype.card n * X) + b * (Λ * X) + d * (√(R * C) * X) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul ha h1 (norm_nonneg _) ha0
        · exact mul_le_mul hb h2 (norm_nonneg _) hb0
        · exact mul_le_mul hd h3 (norm_nonneg _) hd0
    _ = (a * Fintype.card n + b * Λ + d * √(R * C)) * X := by ring

/-- **`lem:record:frame-inputs` (iii)**, the last chain of inequalities. -/
theorem frame_inputs_iii {p X h0 δ wHw sw εH εne εrem ρ : ℝ} (hp : 1 < p)
    (hX : X ≤ p / (p - 1) * (h0 + δ)) (hh0 : h0 ≤ wHw + εH * sw)
    (hδ : |δ| ≤ (εne + εrem) * sw) (hHrow : wHw ≤ ρ * sw) :
    X ≤ wHw + ((p / (p - 1) - 1) * ρ + p / (p - 1) * (εH + εne + εrem)) * sw := by
  have hp1 : 0 < p - 1 := by linarith
  have hq : 1 ≤ p / (p - 1) := by rw [le_div_iff₀ hp1]; linarith
  have hδ' : δ ≤ (εne + εrem) * sw := (le_abs_self δ).trans hδ
  have h1 : p / (p - 1) * (h0 + δ) ≤ p / (p - 1) * (wHw + (εH + εne + εrem) * sw) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (p / (p - 1) - 1) * wHw ≤ (p / (p - 1) - 1) * (ρ * sw) :=
    mul_le_mul_of_nonneg_left hHrow (by linarith)
  nlinarith [h1, h2]

end Sarkozy.Spectral
