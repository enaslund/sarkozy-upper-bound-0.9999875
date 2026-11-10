module

public import Sarkozy.SecondOrder.StarBudgets
public import Sarkozy.Spectral.GlueStars

/-!
# Coarse uniform bounds for the star variance and mean

For the 36-vertex root halves, the finite pivot budgets give
M_star ≤ 2^84/sqrt(p) and z_star ≤ 2^88/p, provided the internal
degree is at most 10 and the pinned count error is at most one half.
-/

@[expose] public section

namespace Sarkozy.SecondOrder

open Finset

variable {p : ℕ} [Fact p.Prime] {U K : Type*} [Fintype U] [DecidableEq U]
  [LinearOrder U] [Fintype K]

theorem star_sqrt_pivotD2_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U = 36) (hK : Fintype.card K = 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    Real.sqrt (pivotD2 L supports3 (starCoeff N c) i) ≤ 2 ^ 71 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  convert star_pivotD2_le L N c hc hn hK hd he i using 1
  norm_num

theorem star_prefix_D_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U = 36) (hK : Fintype.card K = 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L supports3 (starCoeff N c) j) ≤
      36 * 2 ^ 71 := by
  calc _ ≤ ∑ j : U, Real.sqrt (pivotD2 L supports3 (starCoeff N c) j) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Real.sqrt_nonneg _)
    _ ≤ ∑ _j : U, (2 : ℝ) ^ 71 :=
        sum_le_sum fun j _ => star_sqrt_pivotD2_le L N c hc hn hK hd he j
    _ = 36 * 2 ^ 71 := by simp only [sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_ofNat]

theorem starMstar_uniform (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U = 36) (hK : Fintype.card K = 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) :
    Sarkozy.Spectral.starMstar L N c ≤ 2 ^ 84 * (1 / Real.sqrt p) := by
  let r : ℝ := 1 / Real.sqrt p
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := one_div_sqrt_prime_le_one
  have hD : ∑ i, pivotD2 L supports3 (starCoeff N c) i ≤ 36 * 2 ^ 142 := by
    calc _ ≤ ∑ _i : U, (2 : ℝ) ^ 142 :=
          sum_le_sum fun i _ => star_pivotD2_le L N c hc hn hK hd he i
      _ = _ := by simp only [sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_ofNat]
  have hcross : ∑ i, pivotK L supports3 (starCoeff N c) i *
      ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L supports3 (starCoeff N c) j) ≤
      36 * (2 ^ 80 * (36 * 2 ^ 71)) := by
    calc _ ≤ ∑ _i : U, (2 : ℝ) ^ 80 * (36 * 2 ^ 71) := sum_le_sum fun i _ =>
          mul_le_mul (star_pivotK_le L N c hc hn hK hd he i)
            (star_prefix_D_le L N c hc hn hK hd he i)
            (sum_nonneg fun _ _ => Real.sqrt_nonneg _) (by positivity)
      _ = _ := by simp only [sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_ofNat]
  have hm : ∑ i, pivotD2 L supports3 (starCoeff N c) i + 2 * r *
      ∑ i, pivotK L supports3 (starCoeff N c) i *
        ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L supports3 (starCoeff N c) j) ≤
      (2 : ℝ) ^ 168 := by
    have hx := (mul_le_mul_of_nonneg_left hcross (by positivity : 0 ≤ 2 * r)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr1 (by norm_num : (0 : ℝ) ≤ 2)) (by positivity))
    have hsum := add_le_add hD hx
    exact hsum.trans (by norm_num)
  unfold Sarkozy.Spectral.starMstar
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (pow_nonneg (by norm_num) 84) hr, ?_⟩
  calc _ ≤ r ^ 2 * (2 : ℝ) ^ 168 := mul_le_mul_of_nonneg_left hm (sq_nonneg r)
    _ = (2 ^ 84 * (1 / Real.sqrt p)) ^ 2 := by dsimp [r]; ring

theorem starZstar_uniform (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U = 36) (hK : Fintype.card K = 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) :
    Sarkozy.Spectral.starZstar L N c ≤ 2 ^ 88 * (1 / Real.sqrt p) ^ 2 := by
  have hsum : ∑ i, pivotK L supports3 (starCoeff N c) i ≤ 36 * 2 ^ 80 := by
    calc _ ≤ ∑ _i : U, (2 : ℝ) ^ 80 :=
          sum_le_sum fun i _ => star_pivotK_le L N c hc hn hK hd he i
      _ = _ := by simp only [sum_const, card_univ, hn, nsmul_eq_mul, Nat.cast_ofNat]
  have ht : ∑ i, pivotK L supports3 (starCoeff N c) i + |starBEven N c| ≤ (2 : ℝ) ^ 88 :=
    (add_le_add hsum (starBEven_abs_le N c hc hn hK)).trans (by norm_num)
  unfold Sarkozy.Spectral.starZstar
  exact (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (mul_comm _ _)

end Sarkozy.SecondOrder
