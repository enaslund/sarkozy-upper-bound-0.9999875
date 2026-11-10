module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The matching frame (`lem:oct24:feature-block`(c), Step 6)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`(c): in `L²(m_{E,𝔅})` the three
matching features have pairwise correlations at most `1/(b-1)` and their synthesis map has squared
norm at most `Γ_E = 1 + 1/(b-1)`.

**Proved.**
* `distinct_pair_sum` (the prime step): for the uniform law on injective pairs of a finite label
  set of size `N`, `E[f(x_i) g(x_j)] = -⟨f, g⟩_unif/(N - 1)` for centred `g`; in sum form
  `∑_{y ≠ y'} f(y) g(y') = -∑_y f(y) g(y)`. So `V_i^* V_j = -I/(p - 1)` on `L²₀` at a prime.
* `sector_constant` : on an exact support `S` the off-diagonal Gram entry is
  `c_S = ∏_{p∈S} (-1/(p-1))`; for odd `|S|`, `-1/(b-1) ≤ c_S ≤ 0`, and for even nonempty `|S|`,
  `0 ≤ c_S ≤ 1/(b-1)²`, when every `p ≥ b ≥ 3`.
* `three_frame` : if `⟪u_i, u_j⟫ = c ⟪z_i, z_j⟫` (`i ≠ j`) and `‖u_i‖ = ‖z_i‖`, then
  `‖∑ u_i‖² ≤ (1 - c) ∑‖z_i‖²` for `c ≤ 0` and `≤ (1 + 2c) ∑‖z_i‖²` for `c ≥ 0` (the Gram matrix
  has the eigenvalues `1 - c, 1 - c, 1 + 2c`);
* `matching_frame_sector` : hence on every nonempty sector `‖∑ u_i‖² ≤ (1 + 1/(b-1)) ∑‖z_i‖²`,
  and `matching_frame_constant` : `1 + 1/(b-1) ≤ Γ_E = 19951586/19951585` for `b ≥ Q₃`.

The orthogonality of distinct sectors in the product law (the sector lemma of Part II) and the
identification of the features are not formalized; the sector bound is what the frame bound
sums.
-/

namespace Sarkozy.Envelopes

open Finset
open scoped RealInnerProductSpace

/-- **The prime step of Step 6.** `∑_{y ≠ y'} f(y) g(y') = -∑_y f(y) g(y)` when `∑ g = 0`: under
the uniform law on distinct pairs, `E[f(x_i) g(x_j)] = -⟨f, g⟩/(N - 1)` with `⟨f, g⟩` the uniform
inner product. -/
theorem distinct_pair_sum {L : Type*} [Fintype L] [DecidableEq L] (f g : L → ℝ)
    (hg : ∑ y, g y = 0) :
    ∑ y, ∑ y', (if y = y' then 0 else f y * g y') = -∑ y, f y * g y := by
  have e : ∀ y, ∑ y', (if y = y' then 0 else f y * g y') = f y * (∑ y', g y') - f y * g y := by
    intro y
    have h1 : ∑ y', (if y = y' then 0 else f y * g y') =
        ∑ y', f y * g y' - ∑ y', (if y = y' then f y * g y' else 0) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun y' _ => ?_
      split_ifs <;> ring
    rw [h1, sum_ite_eq, mul_sum]
    simp
  simp only [e, hg, mul_zero, zero_sub, sum_neg_distrib]

/-- **The sector constant.** `c_S = ∏_{p∈S} (-1/(p-1))`; if every `p ∈ S` has `p ≥ b ≥ 3`, then for
odd `|S|`, `-1/(b-1) ≤ c_S ≤ 0`, and for even nonempty `|S|`, `0 ≤ c_S ≤ 1/(b-1)²`. -/
theorem sector_constant (S : Finset ℝ) {b : ℝ} (hb : 3 ≤ b) (hS : ∀ p ∈ S, b ≤ p) :
    (Odd S.card → -(1 / (b - 1)) ≤ ∏ p ∈ S, (-(1 / (p - 1))) ∧ ∏ p ∈ S, (-(1 / (p - 1))) ≤ 0) ∧
    (Even S.card → S.Nonempty →
      0 ≤ ∏ p ∈ S, (-(1 / (p - 1))) ∧ ∏ p ∈ S, (-(1 / (p - 1))) ≤ 1 / (b - 1) ^ 2) := by
  have hb1 : 0 < b - 1 := by linarith
  have hx0 : ∀ p ∈ S, 0 ≤ 1 / (p - 1) := fun p hp => by
    have := hS p hp; exact div_nonneg (by norm_num) (by linarith)
  have hx1 : ∀ p ∈ S, 1 / (p - 1) ≤ 1 / (b - 1) := fun p hp => by
    have := hS p hp
    exact one_div_le_one_div_of_le hb1 (by linarith)
  have hneg : ∏ p ∈ S, (-(1 / (p - 1))) = (-1) ^ S.card * ∏ p ∈ S, (1 / (p - 1)) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_congr rfl fun p _ => by ring
  set P := ∏ p ∈ S, (1 / (p - 1)) with hP
  have hP0 : 0 ≤ P := prod_nonneg hx0
  have hPle : P ≤ (1 / (b - 1)) ^ S.card := by
    rw [hP, ← prod_const]
    exact prod_le_prod₀ hx0 hx1
  have hq1 : 1 / (b - 1) ≤ 1 := by rw [div_le_one hb1]; linarith
  have hq0 : 0 ≤ 1 / (b - 1) := by positivity
  rw [hneg]
  refine ⟨fun hodd => ?_, fun heven hne => ?_⟩
  · rw [hodd.neg_one_pow]
    have hc : 1 ≤ S.card := hodd.pos
    have : (1 / (b - 1)) ^ S.card ≤ 1 / (b - 1) := by
      calc (1 / (b - 1)) ^ S.card ≤ (1 / (b - 1)) ^ 1 := pow_le_pow_of_le_one hq0 hq1 hc
        _ = 1 / (b - 1) := pow_one _
    constructor <;> nlinarith
  · rw [heven.neg_one_pow, one_mul]
    have hc : 2 ≤ S.card := by
      rcases heven with ⟨k, hk⟩
      have : 0 < S.card := hne.card_pos
      omega
    have : (1 / (b - 1)) ^ S.card ≤ (1 / (b - 1)) ^ 2 := pow_le_pow_of_le_one hq0 hq1 hc
    refine ⟨hP0, hPle.trans (this.trans (le_of_eq ?_))⟩
    rw [div_pow, one_pow]

/-- **The three-feature frame.** If `⟪u_i, u_j⟫ = c ⟪z_i, z_j⟫` for `i ≠ j` and `‖u_i‖ = ‖z_i‖`
(`V_i^* V_j = cI`, `V_i^* V_i = I`), then `‖∑ u_i‖² = (1 - c) ∑ ‖z_i‖² + c ‖∑ z_i‖²`; hence the
bound `(1 - c) ∑ ‖z_i‖²` for `c ≤ 0` and `(1 + 2c) ∑ ‖z_i‖²` for `c ≥ 0`. -/
theorem three_frame {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (u : Fin 3 → H) (z : Fin 3 → K) (c : ℝ)
    (hoff : ∀ i j, i ≠ j → ⟪u i, u j⟫ = c * ⟪z i, z j⟫) (hdiag : ∀ i, ‖u i‖ = ‖z i‖) :
    ‖∑ i, u i‖ ^ 2 = (1 - c) * ∑ i, ‖z i‖ ^ 2 + c * ‖∑ i, z i‖ ^ 2 ∧
      (c ≤ 0 → ‖∑ i, u i‖ ^ 2 ≤ (1 - c) * ∑ i, ‖z i‖ ^ 2) ∧
      (0 ≤ c → ‖∑ i, u i‖ ^ 2 ≤ (1 + 2 * c) * ∑ i, ‖z i‖ ^ 2) := by
  have hu : ‖∑ i, u i‖ ^ 2 = ∑ i, ∑ j, ⟪u i, u j⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  have hz : ‖∑ i, z i‖ ^ 2 = ∑ i, ∑ j, ⟪z i, z j⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  simp only [Fin.sum_univ_three] at hu hz ⊢
  have h01 := hoff 0 1 (by decide)
  have h02 := hoff 0 2 (by decide)
  have h10 := hoff 1 0 (by decide)
  have h12 := hoff 1 2 (by decide)
  have h20 := hoff 2 0 (by decide)
  have h21 := hoff 2 1 (by decide)
  have d0 : ⟪u 0, u 0⟫ = ⟪z 0, z 0⟫ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hdiag]
  have d1 : ⟪u 1, u 1⟫ = ⟪z 1, z 1⟫ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hdiag]
  have d2 : ⟪u 2, u 2⟫ = ⟪z 2, z 2⟫ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hdiag]
  have n0 : ⟪z 0, z 0⟫ = ‖z 0‖ ^ 2 := real_inner_self_eq_norm_sq _
  have n1 : ⟪z 1, z 1⟫ = ‖z 1‖ ^ 2 := real_inner_self_eq_norm_sq _
  have n2 : ⟪z 2, z 2⟫ = ‖z 2‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hid : ‖u 0 + u 1 + u 2‖ ^ 2 =
      (1 - c) * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2) + c * ‖z 0 + z 1 + z 2‖ ^ 2 := by
    rw [hu, hz, h01, h02, h10, h12, h20, h21, d0, d1, d2, n0, n1, n2]
    ring
  -- `‖z₀ + z₁ + z₂‖² ≤ 3 ∑ ‖z_i‖²`
  have h3 : ‖z 0 + z 1 + z 2‖ ^ 2 ≤ 3 * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2) := by
    have a := norm_add_le (z 0 + z 1) (z 2)
    have b := norm_add_le (z 0) (z 1)
    have hn : ‖z 0 + z 1 + z 2‖ ≤ ‖z 0‖ + ‖z 1‖ + ‖z 2‖ := by linarith
    have hsq : ‖z 0 + z 1 + z 2‖ ^ 2 ≤ (‖z 0‖ + ‖z 1‖ + ‖z 2‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖z 0‖ - ‖z 1‖), sq_nonneg (‖z 1‖ - ‖z 2‖),
      sq_nonneg (‖z 0‖ - ‖z 2‖)]
  refine ⟨hid, fun hc => ?_, fun hc => ?_⟩
  · rw [hid]
    have : c * ‖z 0 + z 1 + z 2‖ ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg _)
    linarith
  · rw [hid]
    have := mul_le_mul_of_nonneg_left h3 hc
    nlinarith

/-- **`lem:oct24:feature-block`(c), one sector.** On a sector with off-diagonal Gram constant `c`
satisfying the conclusion of `sector_constant` (odd: `-1/(b-1) ≤ c ≤ 0`; even: `0 ≤ c ≤ 1/(b-1)²`),
`b ≥ 3`, the synthesis has `‖∑ u_i‖² ≤ (1 + 1/(b-1)) ∑ ‖z_i‖²`. -/
theorem matching_frame_sector {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (u : Fin 3 → H) (z : Fin 3 → K) {c b : ℝ}
    (hb : 3 ≤ b) (hoff : ∀ i j, i ≠ j → ⟪u i, u j⟫ = c * ⟪z i, z j⟫)
    (hdiag : ∀ i, ‖u i‖ = ‖z i‖)
    (hc : (-(1 / (b - 1)) ≤ c ∧ c ≤ 0) ∨ (0 ≤ c ∧ c ≤ 1 / (b - 1) ^ 2)) :
    ‖∑ i, u i‖ ^ 2 ≤ (1 + 1 / (b - 1)) * ∑ i, ‖z i‖ ^ 2 := by
  obtain ⟨-, hneg, hpos⟩ := three_frame u z c hoff hdiag
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hb1 : 0 < b - 1 := by linarith
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := hneg h2
    have : (1 - c) * ∑ i, ‖z i‖ ^ 2 ≤ (1 + 1 / (b - 1)) * ∑ i, ‖z i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hS
    linarith
  · have := hpos h1
    have hq : 2 * (1 / (b - 1) ^ 2) ≤ 1 / (b - 1) := by
      have hx : 1 / (b - 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      have h0 : 0 ≤ 1 / (b - 1) := by positivity
      rw [← one_div_pow]
      nlinarith
    have : (1 + 2 * c) * ∑ i, ‖z i‖ ^ 2 ≤ (1 + 1 / (b - 1)) * ∑ i, ‖z i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hS
    linarith

/-- **`eq:oct24:feature-constants`, `Γ_E`.** For every middle block (`b ≥ Q₃ = 19951586`),
`1 + 1/(b-1) ≤ Γ_E = 19951586/19951585`. -/
theorem matching_frame_constant {b : ℝ} (hb : 19951586 ≤ b) :
    1 + 1 / (b - 1) ≤ 19951586 / 19951585 := by
  have hb1 : (19951585 : ℝ) ≤ b - 1 := by linarith
  have : 1 / (b - 1) ≤ 1 / 19951585 := one_div_le_one_div_of_le (by norm_num) hb1
  have e : (19951586 / 19951585 : ℝ) = 1 + 1 / 19951585 := by norm_num
  linarith

end Sarkozy.Envelopes
