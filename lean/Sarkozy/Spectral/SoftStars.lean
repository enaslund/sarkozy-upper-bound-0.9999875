module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt

/-!
# `thm:record:direct-star` (b): the soft-star bound

`paper/sections/14_spectral.tex`, proof of `thm:record:direct-star` (b), paragraph *Soft stars*,
the Cauchy–Schwarz step. On `t ∉ x(U⁺)`, `S_k g = a_k B_k g + coll_k g` with `|a_k - 1| ≤ ê_k`,
`‖B_k g‖ ≤ r (𝐇_kk + ε_𝐁)^{1/2} ‖g‖` (from (H1)) and `‖coll_k g‖ ≤ n 2^{r_k} p^{-1} ‖g‖`. These
enter as the hypotheses `‖(S_k - B_k) g‖ ≤ ê_k ‖B_k g‖ + d_k ‖g‖` and `‖B_k g‖ ≤ c_k ‖g‖`.

* `soft_star_bound`: `‖∑_k (S_k - B_k) g_k‖ ≤ ((∑_k ê_k² c_k²)^{1/2} + (∑_k d_k²)^{1/2}) |g|`; with
  `c_k = r (𝐇_kk + ε_𝐁)^{1/2}` and `d_k = n 2^{r_k}/p` this is
  `‖𝐒 - 𝐁‖ ≤ r (∑_k ê_k² (𝐇_kk + ε_𝐁))^{1/2} + (n/p)(∑_k 4^{r_k})^{1/2}`; with
  `‖𝐄‖ ≤ (1 + ε_V)^{1/2}` the two soft terms `(𝐒 - 𝐁)𝐄^* + 𝐄(𝐒 - 𝐁)^*` of `𝓡` then have norm at
  most `ε_soft` (that last step, with the adjoints, is not formalized here).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {K : Type*} [Fintype K]

/-- **The soft-star bound** (proof of `thm:record:direct-star` (b)). -/
theorem soft_star_bound (S B : K → G →ₗ[𝕜] H) (ehat c d : K → ℝ) (he : ∀ k, 0 ≤ ehat k)
    (hB : ∀ k g, ‖B k g‖ ≤ c k * ‖g‖)
    (hSB : ∀ k g, ‖S k g - B k g‖ ≤ ehat k * ‖B k g‖ + d k * ‖g‖) (g : K → G) :
    ‖∑ k, (S k (g k) - B k (g k))‖ ≤
      (√(∑ k, (ehat k * c k) ^ 2) + √(∑ k, d k ^ 2)) * √(∑ k, ‖g k‖ ^ 2) := by
  have h1 : ∀ k, ‖S k (g k) - B k (g k)‖ ≤ ehat k * c k * ‖g k‖ + d k * ‖g k‖ := fun k => by
    have h := hSB k (g k)
    have h' := mul_le_mul_of_nonneg_left (hB k (g k)) (he k)
    nlinarith [h, h']
  calc ‖∑ k, (S k (g k) - B k (g k))‖ ≤ ∑ k, ‖S k (g k) - B k (g k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, (ehat k * c k * ‖g k‖ + d k * ‖g k‖) := Finset.sum_le_sum fun k _ => h1 k
    _ = ∑ k, (ehat k * c k) * ‖g k‖ + ∑ k, d k * ‖g k‖ := Finset.sum_add_distrib
    _ ≤ √(∑ k, (ehat k * c k) ^ 2) * √(∑ k, ‖g k‖ ^ 2) +
          √(∑ k, d k ^ 2) * √(∑ k, ‖g k‖ ^ 2) :=
        add_le_add (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)
    _ = (√(∑ k, (ehat k * c k) ^ 2) + √(∑ k, d k ^ 2)) * √(∑ k, ‖g k‖ ^ 2) := by ring

/-- With `c_k = r (𝐇_kk + ε_𝐁)^{1/2}`: `(∑_k ê_k² c_k²)^{1/2} = r (∑_k ê_k² (𝐇_kk + ε_𝐁))^{1/2}`. -/
theorem soft_star_first_term (ehat h : K → ℝ) {r : ℝ} (hr : 0 ≤ r) (hh : ∀ k, 0 ≤ h k) :
    √(∑ k, (ehat k * (r * √(h k))) ^ 2) = r * √(∑ k, ehat k ^ 2 * h k) := by
  have e : ∑ k, (ehat k * (r * √(h k))) ^ 2 = r ^ 2 * ∑ k, ehat k ^ 2 * h k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt (hh k)]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

/-- With `d_k = n 2^{r_k}/p`: `(∑_k d_k²)^{1/2} = (n/p)(∑_k 4^{r_k})^{1/2}`. -/
theorem soft_star_second_term (rk : K → ℕ) {n p : ℝ} (hn : 0 ≤ n) (hp : 0 < p) :
    √(∑ k, (n * 2 ^ rk k / p) ^ 2) = n / p * √(∑ k, (4 : ℝ) ^ rk k) := by
  have e : ∑ k, (n * 2 ^ rk k / p) ^ 2 = (n / p) ^ 2 * ∑ k, (4 : ℝ) ^ rk k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (4 : ℝ) ^ rk k = (2 ^ rk k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hn hp.le)]

end Sarkozy.Spectral
