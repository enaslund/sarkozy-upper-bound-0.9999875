module

public import Sarkozy.Influence.OpBound
public import Sarkozy.FiveType.Rows
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The norm bookkeeping of `prop:conditional-star`(b), (c)

Source: `paper/sections/16_extraction.tex`, `prop:conditional-star` and its proof, Step 5
("complementary means") and Step 6 ("decay").

* `eStar d e = (d + √(d² + 4e²))/2` is the norm of the `2 × 2` matrix `(d e; e 0)` (`d, e ≥ 0`):
  `norm_matrix_two` gives `d ab + e(ab' + a'b) ≤ e_⋆ √(a² + a'²) √(b² + b'²)`.
* `mean_block_bound`: **Step 5, last display.** If an operator between orthogonal sums
  `𝒱_X ⊕ 𝒲_X ← 𝒱_Y ⊕ 𝒲_Y` has block norms at most `κ r d₁` (`𝒱 ← 𝒱`), `κ r e` (`𝒱 ← 𝒲` and
  `𝒲 ← 𝒱`) and a vanishing block `𝒲 ← 𝒲`, its norm is at most `κ r e_⋆`.
* `matrix_norms_schur`: an operator matrix between orthogonal sums is bounded by the norm of the
  matrix of the norms of its entries; with Schur's test (`Influence.opBound_schur`) for that
  matrix, `√(largest row sum · largest column sum)` (the bounds `𝖽_L`, `𝖽_R` of (b)).
* `gram_bound`: the `𝒱 ← 𝒲` block. The squared norm of a nonnegative matrix `(e_{iT'})` is at
  most the largest row sum of its Gram matrix `(∑_{T'} e_{iT'} e_{i'T'})`, which is `𝖾_L²`.
* `gram_entry_card`: the Gram entries of `(e_{iT'})`, `e_{iT'} = f_i(|T'|)` for
  `T' ⊆ N_X(i)` with `|T'| ≥ 2`, are `∑_{s=2}^{m_{ii'}} C(m_{ii'}, s) f_i(s) f_{i'}(s)`, which is
  the expression in the definition of `𝖾_L`.
* `decay_feature_bound`: **Step 6**, the choice of `ω_s`. If `‖W‖² ≤ κ r²` (Step 1) and
  `‖W‖² ≤ r² + ν^s` (Schur's test for the Gram kernel), `κ ≤ κ₀` and
  `κ₀ω² ≥ min(κ₀, 1 + ν^s/r²)`, then `‖W‖ ≤ √κ₀ r ω`.
* `decay_term_mono`: **(c), last sentence.** The term `ν^s/r² = (ν/r)^s r^{s-2}` decreases when
  `ν/r` and `r` decrease (`s ≥ 2`), so conditions checked at a threshold `p₀` hold at every `p ≥ p₀`
  for admissible `κ`, `ν_χ/r` (nonincreasing in `p`, `lem:majorant`).
-/

@[expose] public section

open scoped BigOperators RealInnerProductSpace

namespace Sarkozy.JointRows.Star

/-! ## The norm of `(d e; e 0)` -/

/-- `e_⋆ = (d + √(d² + 4e²))/2`, the largest eigenvalue of `(d e; e 0)`. -/
noncomputable def eStar (d e : ℝ) : ℝ := (d + Real.sqrt (d ^ 2 + 4 * e ^ 2)) / 2

theorem eStar_sq (d e : ℝ) : eStar d e ^ 2 = d * eStar d e + e ^ 2 := by
  unfold eStar
  have h := Real.sq_sqrt (show 0 ≤ d ^ 2 + 4 * e ^ 2 by positivity)
  nlinarith [h]

theorem le_eStar (d e : ℝ) : d ≤ eStar d e := by
  unfold eStar
  have : d ≤ Real.sqrt (d ^ 2 + 4 * e ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg e])
  linarith

theorem eStar_nonneg {d e : ℝ} (hd : 0 ≤ d) : 0 ≤ eStar d e := le_trans hd (le_eStar d e)

/-- Cauchy–Schwarz in `ℝ²`. -/
theorem cs_two (a a' x y : ℝ) :
    a * x + a' * y ≤ Real.sqrt (a ^ 2 + a' ^ 2) * Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (a * y - a' * x)]

/-- **The `2 × 2` matrix of norms**: `(d e; e 0)` has norm `e_⋆`. -/
theorem norm_matrix_two {d e : ℝ} (hd : 0 ≤ d) (a a' b b' : ℝ) :
    d * a * b + e * (a * b' + a' * b) ≤
      eStar d e * Real.sqrt (a ^ 2 + a' ^ 2) * Real.sqrt (b ^ 2 + b' ^ 2) := by
  set l := eStar d e with hl
  have hl0 : 0 ≤ l := eStar_nonneg hd
  have hld : d ≤ l := le_eStar d e
  have hsq := eStar_sq d e
  rw [← hl] at hsq
  -- `|M w|² ≤ l² |w|²`
  have hMw : (d * b + e * b') ^ 2 + (e * b) ^ 2 ≤ l ^ 2 * (b ^ 2 + b' ^ 2) := by
    have hle : l * (l - d) = e ^ 2 := by nlinarith [hsq]
    have hdisc : (-(d * e)) ^ 2 ≤ d * (l - d) * (d * l) := by
      rw [show d * (l - d) * (d * l) = d ^ 2 * (l * (l - d)) by ring, hle]
      exact le_of_eq (by ring)
    have hbin := FiveType.binary_nonneg (A := d * (l - d)) (B := -(d * e)) (C := d * l)
      (x := b) (y := b') (mul_nonneg hd (by linarith)) (mul_nonneg hd hl0) hdisc
    nlinarith [hbin]
  have h1 := cs_two a a' (d * b + e * b') (e * b)
  have h2 : Real.sqrt ((d * b + e * b') ^ 2 + (e * b) ^ 2) ≤ l * Real.sqrt (b ^ 2 + b' ^ 2) := by
    rw [show l * Real.sqrt (b ^ 2 + b' ^ 2) = Real.sqrt (l ^ 2 * (b ^ 2 + b' ^ 2)) by
      rw [Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq hl0]]
    exact Real.sqrt_le_sqrt hMw
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (a ^ 2 + a' ^ 2))
  nlinarith [h1, h3]

/-! ## Step 5: operators between orthogonal sums -/

section Blocks

variable {EX EY : Type*} [NormedAddCommGroup EX] [NormedAddCommGroup EY]

/-- **Step 5, the bound by the matrix of block norms**: with `L²₀(ν_X) = 𝒱_X ⊕ 𝒲_X`,
`L²₀(ν_Y) = 𝒱_Y ⊕ 𝒲_Y` (the components `pV`, `pW`, orthogonal: `‖x‖² = ‖x_𝒱‖² + ‖x_𝒲‖²`), a
bilinear form `t` with block bounds `κ r d₁`, `κ r e`, `κ r e` and `t(𝒲_X, 𝒲_Y) = 0` has
`|t(x, y)| ≤ κ r e_⋆ ‖x‖ ‖y‖` (`T_mean`, `‖T_mean‖ ≤ κ r 𝖾_⋆`). -/
theorem mean_block_bound (t : EX → EY → ℝ) (pVX pWX : EX → EX) (pVY pWY : EY → EY)
    {c d e : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hsplit : ∀ x y, t x y = t (pVX x) (pVY y) + t (pVX x) (pWY y) + t (pWX x) (pVY y) +
      t (pWX x) (pWY y))
    (hnX : ∀ x, ‖x‖ ^ 2 = ‖pVX x‖ ^ 2 + ‖pWX x‖ ^ 2)
    (hnY : ∀ y, ‖y‖ ^ 2 = ‖pVY y‖ ^ 2 + ‖pWY y‖ ^ 2)
    (hVV : ∀ x y, |t (pVX x) (pVY y)| ≤ c * d * ‖pVX x‖ * ‖pVY y‖)
    (hVW : ∀ x y, |t (pVX x) (pWY y)| ≤ c * e * ‖pVX x‖ * ‖pWY y‖)
    (hWV : ∀ x y, |t (pWX x) (pVY y)| ≤ c * e * ‖pWX x‖ * ‖pVY y‖)
    (hWW : ∀ x y, t (pWX x) (pWY y) = 0) (x : EX) (y : EY) :
    |t x y| ≤ c * eStar d e * ‖x‖ * ‖y‖ := by
  have hx : ‖x‖ = Real.sqrt (‖pVX x‖ ^ 2 + ‖pWX x‖ ^ 2) := by
    rw [← hnX, Real.sqrt_sq (norm_nonneg _)]
  have hy : ‖y‖ = Real.sqrt (‖pVY y‖ ^ 2 + ‖pWY y‖ ^ 2) := by
    rw [← hnY, Real.sqrt_sq (norm_nonneg _)]
  have hm := norm_matrix_two (e := e) hd ‖pVX x‖ ‖pWX x‖ ‖pVY y‖ ‖pWY y‖
  rw [← hx, ← hy] at hm
  rw [hsplit, hWW, add_zero]
  calc |t (pVX x) (pVY y) + t (pVX x) (pWY y) + t (pWX x) (pVY y)|
      ≤ |t (pVX x) (pVY y)| + |t (pVX x) (pWY y)| + |t (pWX x) (pVY y)| := by
        have := abs_add_le (t (pVX x) (pVY y) + t (pVX x) (pWY y)) (t (pWX x) (pVY y))
        have := abs_add_le (t (pVX x) (pVY y)) (t (pVX x) (pWY y))
        linarith
    _ ≤ c * d * ‖pVX x‖ * ‖pVY y‖ + c * e * ‖pVX x‖ * ‖pWY y‖ + c * e * ‖pWX x‖ * ‖pVY y‖ := by
        linarith [hVV x y, hVW x y, hWV x y]
    _ = c * (d * ‖pVX x‖ * ‖pVY y‖ + e * (‖pVX x‖ * ‖pWY y‖ + ‖pWX x‖ * ‖pVY y‖)) := by ring
    _ ≤ c * (eStar d e * ‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left hm hc
    _ = c * eStar d e * ‖x‖ * ‖y‖ := by ring

end Blocks

/-! ## Matrices of norms: Schur's test and the Gram bound -/

section Matrices

variable {U V : Type*}

/-- The bilinear form of a bounded matrix: `∑ a_i N_{ij} b_j ≤ Λ ‖a‖ ‖b‖` from
`OpBound` (`‖N b‖ ≤ Λ‖b‖`). -/
theorem bilin_le_of_opBound {R : Finset U} {C : Finset V} {N : U → V → ℝ} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (h : Influence.OpBound R C N Λ) (a : U → ℝ) (b : V → ℝ) :
    ∑ i ∈ R, a i * ∑ j ∈ C, N i j * b j ≤
      Λ * Influence.vnorm R a * Influence.vnorm C b := by
  have h1 : ∑ i ∈ R, a i * ∑ j ∈ C, N i j * b j ≤
      Influence.vnorm R a * Influence.vnorm R (fun i => ∑ j ∈ C, N i j * b j) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq R a (fun i => ∑ j ∈ C, N i j * b j)
    unfold Influence.vnorm
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (a i))]
    exact Real.le_sqrt_of_sq_le hcs
  have h2 : Influence.vnorm R (fun i => ∑ j ∈ C, N i j * b j) ≤ Λ * Influence.vnorm C b := by
    unfold Influence.vnorm
    rw [show Λ * Real.sqrt (∑ j ∈ C, b j ^ 2) = Real.sqrt (Λ ^ 2 * ∑ j ∈ C, b j ^ 2) by
      rw [Real.sqrt_mul (sq_nonneg Λ), Real.sqrt_sq hΛ]]
    exact Real.sqrt_le_sqrt (h b)
  have h3 := mul_le_mul_of_nonneg_left h2 (Influence.vnorm_nonneg R a)
  linarith

/-- **An operator matrix between orthogonal sums is bounded by the matrix of the norms of its
entries**, and that matrix by Schur's test: if `|⟨x_i, T_{ij} y_j⟩| ≤ N_{ij}‖x_i‖‖y_j‖` with
`N ≥ 0` of largest row sum `ρ` and largest column sum `γ`, then
`|∑_{ij} ⟨x_i, T_{ij} y_j⟩| ≤ √(ργ) (∑_i ‖x_i‖²)^{1/2} (∑_j ‖y_j‖²)^{1/2}`. -/
theorem matrix_norms_schur {R : Finset U} {C : Finset V} (t : U → V → ℝ) (N : U → V → ℝ)
    (α : U → ℝ) (β : V → ℝ) (hN : ∀ i j, 0 ≤ N i j)
    (ht : ∀ i j, |t i j| ≤ N i j * α i * β j) {ρ γ : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 ≤ γ)
    (hrow : ∀ i ∈ R, ∑ j ∈ C, N i j ≤ ρ) (hcol : ∀ j ∈ C, ∑ i ∈ R, N i j ≤ γ) :
    |∑ i ∈ R, ∑ j ∈ C, t i j| ≤
      Real.sqrt (ρ * γ) * Influence.vnorm R α * Influence.vnorm C β := by
  have hS := Influence.opBound_schur hN hρ hγ hrow hcol
  have hb := bilin_le_of_opBound (Real.sqrt_nonneg _) hS α β
  calc |∑ i ∈ R, ∑ j ∈ C, t i j| ≤ ∑ i ∈ R, ∑ j ∈ C, |t i j| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ R, ∑ j ∈ C, N i j * α i * β j :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ht i j
    _ = ∑ i ∈ R, α i * ∑ j ∈ C, N i j * β j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ _ := hb

/-- **The Gram bound** (the `𝒱 ← 𝒲` block of Step 5): for a nonnegative matrix `E`,
`∑_{i,T} a_i E_{iT} b_T ≤ √G ‖a‖ ‖b‖` whenever every row sum of the Gram matrix
`(∑_T E_{iT} E_{i'T})_{i,i'}` is at most `G`. -/
theorem gram_bound {R : Finset U} {C : Finset V} (E : U → V → ℝ) (hE : ∀ i j, 0 ≤ E i j)
    {G : ℝ} (hG0 : 0 ≤ G) (hG : ∀ i ∈ R, ∑ i' ∈ R, ∑ j ∈ C, E i j * E i' j ≤ G)
    (a : U → ℝ) (b : V → ℝ) :
    ∑ j ∈ C, b j * ∑ i ∈ R, E i j * a i ≤
      Real.sqrt G * Influence.vnorm R a * Influence.vnorm C b := by
  -- `‖Eᵀ a‖² = ⟨a, (E Eᵀ) a⟩ ≤ G ‖a‖²` (Schur's test for the symmetric Gram matrix)
  have hgram : ∑ j ∈ C, (∑ i ∈ R, E i j * a i) ^ 2 ≤ G * ∑ i ∈ R, a i ^ 2 := by
    have e1 : ∑ j ∈ C, (∑ i ∈ R, E i j * a i) ^ 2 =
        ∑ i ∈ R, ∑ i' ∈ R, a i * a i' * ∑ j ∈ C, E i j * E i' j := by
      have hj : ∀ j, (∑ i ∈ R, E i j * a i) ^ 2 =
          ∑ i ∈ R, ∑ i' ∈ R, a i * a i' * (E i j * E i' j) := fun j => by
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
      simp_rw [hj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i' _ => by rw [Finset.mul_sum]
    rw [e1]
    have e2 : ∀ i i', a i * a i' * ∑ j ∈ C, E i j * E i' j ≤
        (a i ^ 2 + a i' ^ 2) / 2 * ∑ j ∈ C, E i j * E i' j := fun i i' => by
      have hs : 0 ≤ ∑ j ∈ C, E i j * E i' j :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hE i j) (hE i' j)
      have : a i * a i' ≤ (a i ^ 2 + a i' ^ 2) / 2 := by nlinarith [sq_nonneg (a i - a i')]
      exact mul_le_mul_of_nonneg_right this hs
    calc ∑ i ∈ R, ∑ i' ∈ R, a i * a i' * ∑ j ∈ C, E i j * E i' j
        ≤ ∑ i ∈ R, ∑ i' ∈ R, (a i ^ 2 + a i' ^ 2) / 2 * ∑ j ∈ C, E i j * E i' j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => e2 i i'
      _ = ∑ i ∈ R, a i ^ 2 * ∑ i' ∈ R, ∑ j ∈ C, E i j * E i' j := by
          have hsym : ∑ i ∈ R, ∑ i' ∈ R, a i' ^ 2 * ∑ j ∈ C, E i j * E i' j =
              ∑ i ∈ R, ∑ i' ∈ R, a i ^ 2 * ∑ j ∈ C, E i j * E i' j := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by
              rw [Finset.sum_congr rfl fun j _ => mul_comm (E i' j) (E i j)]
          have hsplit : ∑ i ∈ R, ∑ i' ∈ R, (a i ^ 2 + a i' ^ 2) / 2 * ∑ j ∈ C, E i j * E i' j =
              (∑ i ∈ R, ∑ i' ∈ R, a i ^ 2 * ∑ j ∈ C, E i j * E i' j +
                ∑ i ∈ R, ∑ i' ∈ R, a i' ^ 2 * ∑ j ∈ C, E i j * E i' j) / 2 := by
            rw [← Finset.sum_add_distrib, Finset.sum_div]
            exact Finset.sum_congr rfl fun i _ => by
              rw [← Finset.sum_add_distrib, Finset.sum_div]
              exact Finset.sum_congr rfl fun i' _ => by ring
          rw [hsplit, hsym]
          rw [show ∀ s : ℝ, (s + s) / 2 = s from fun s => by ring]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ R, a i ^ 2 * G :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hG i hi) (sq_nonneg _)
      _ = G * ∑ i ∈ R, a i ^ 2 := by rw [← Finset.sum_mul, mul_comm]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq C b (fun j => ∑ i ∈ R, E i j * a i)
  have h1 : ∑ j ∈ C, b j * ∑ i ∈ R, E i j * a i ≤
      Influence.vnorm C b * Real.sqrt (∑ j ∈ C, (∑ i ∈ R, E i j * a i) ^ 2) := by
    unfold Influence.vnorm
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg (b j))]
    exact Real.le_sqrt_of_sq_le hcs
  have h2 : Real.sqrt (∑ j ∈ C, (∑ i ∈ R, E i j * a i) ^ 2) ≤
      Real.sqrt G * Influence.vnorm R a := by
    unfold Influence.vnorm
    rw [← Real.sqrt_mul hG0]
    exact Real.sqrt_le_sqrt hgram
  have h3 := mul_le_mul_of_nonneg_left h2 (Influence.vnorm_nonneg C b)
  linarith

/-- **The Gram entries of `(e_{iT'})`**: if `e_{iT'} = f_i(|T'|)` for `T' ⊆ N(i)` and zero
otherwise, then `∑_{T' ⊆ A} e_{iT'} e_{i'T'}` over the subsets of `A = N(i) ∩ N(i')` is
`∑_{s} C(|A|, s) f_i(s) f_{i'}(s)`; in `𝖾_L` the sets have `|T'| ≥ 2` (`f(0) = f(1) = 0`). -/
theorem gram_entry_card {W : Type*} [DecidableEq W] (A : Finset W) (f g : ℕ → ℝ) :
    ∑ T ∈ A.powerset, f T.card * g T.card =
      ∑ s ∈ Finset.range (A.card + 1), (A.card.choose s : ℝ) * (f s * g s) := by
  rw [Finset.sum_powerset_apply_card (f := fun s => f s * g s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [nsmul_eq_mul]

end Matrices

/-! ## Step 6 and (c): decay -/

/-- **Step 6, the choice of `ω_s`**: if `‖W‖² ≤ κ r²` (Step 1) and `‖W‖² ≤ r² + ν^s` (Schur's
test for the Gram kernel of `W_S 𝟙_Ω`), `κ ≤ κ₀`, `0 < r`, `0 < ω` and
`κ₀ ω² ≥ min(κ₀, 1 + ν^s/r²)`, then `‖W‖ ≤ √κ₀ r ω`. -/
theorem decay_feature_bound {w κ κ₀ r ω νs : ℝ} (hr : 0 < r) (hω : 0 < ω)
    (h1 : w ^ 2 ≤ κ * r ^ 2) (h2 : w ^ 2 ≤ r ^ 2 + νs) (hκ : κ ≤ κ₀)
    (hω2 : min κ₀ (1 + νs / r ^ 2) ≤ κ₀ * ω ^ 2) :
    w ≤ Real.sqrt κ₀ * r * ω := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hsq : w ^ 2 ≤ κ₀ * ω ^ 2 * r ^ 2 := by
    rcases min_choice κ₀ (1 + νs / r ^ 2) with h | h
    · rw [h] at hω2
      nlinarith [mul_le_mul_of_nonneg_right hκ hr2.le]
    · rw [h] at hω2
      have : r ^ 2 + νs = (1 + νs / r ^ 2) * r ^ 2 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right hω2 hr2.le]
  have hκ0 : 0 ≤ κ₀ := by
    by_contra hneg
    push Not at hneg
    have : κ₀ * ω ^ 2 * r ^ 2 < 0 := by
      have := mul_pos (pow_pos hω 2) hr2
      nlinarith
    nlinarith [sq_nonneg w]
  rw [show Real.sqrt κ₀ * r * ω = Real.sqrt (κ₀ * ω ^ 2 * r ^ 2) by
    rw [Real.sqrt_mul (mul_nonneg hκ0 (sq_nonneg ω)), Real.sqrt_mul hκ0, Real.sqrt_sq hω.le,
      Real.sqrt_sq hr.le]
    ring]
  exact Real.le_sqrt_of_sq_le hsq

/-- **(c), the threshold**: `ν^s/r² = (ν/r)^s r^{s-2}` decreases when `ν/r` and `r` decrease
(`s ≥ 2`). For admissible `κ` and `ν_χ/r` (nonincreasing in `p`, `lem:majorant`), conditions
`κ₀ ≥ κ`, `κ₀ω_s² ≥ min(κ₀, 1 + ν_χ^s/r²)` at `p₀` thus hold at every `p ≥ p₀`. -/
theorem decay_term_mono {q q' r r' : ℝ} {s : ℕ} (hq' : 0 ≤ q') (hqq : q' ≤ q)
    (hr' : 0 ≤ r') (hrr : r' ≤ r) : q' ^ s * r' ^ (s - 2) ≤ q ^ s * r ^ (s - 2) := by
  have hq : 0 ≤ q := le_trans hq' hqq
  exact mul_le_mul (pow_le_pow_left₀ hq' hqq s) (pow_le_pow_left₀ hr' hrr _)
    (pow_nonneg hr' _) (pow_nonneg hq _)

/-- `(ν r)^s r^{-2}` identity used in (c): `ν^s/r² = (ν/r)^s r^{s-2}` for `r > 0`, `s ≥ 2`. -/
theorem decay_term_eq {ν r : ℝ} {s : ℕ} (hr : 0 < r) (hs : 2 ≤ s) :
    ν ^ s / r ^ 2 = (ν / r) ^ s * r ^ (s - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  rw [show k + 2 - 2 = k by omega, div_pow]
  field_simp
  ring

end Sarkozy.JointRows.Star
