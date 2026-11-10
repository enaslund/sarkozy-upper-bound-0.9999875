module

public import Sarkozy.SecondOrder.StarUniform

/-!
# Uniform star bounds for halves of size at most thirty-six

The root estimates also hold for every smaller half. Their proofs use
upper bounds on the numbers of supports and coefficients throughout.
-/

@[expose] public section

namespace Sarkozy.SecondOrder.AtMost

open Finset

variable {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]

omit [DecidableEq U] [Fintype K] in
theorem sum_const_bound (hn : Fintype.card U ≤ 36) {a : ℝ} (ha : 0 ≤ a) :
    ∑ _i : U, a ≤ 36 * a := by
  simp only [sum_const, card_univ, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ha

theorem starBEven_abs_le (N : K → Finset U) (c : K → Finset U → ℝ)
    (hc : ∀ k T, |c k T| ≤ 1) (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36) :
    |starBEven N c| ≤ 2 ^ 60 := by
  have hb : ∀ T, |starCoeff N c T| ≤ 36 := by
    intro T
    exact (starCoeff_abs_le N c hc T).trans (by exact_mod_cast hK)
  unfold starBEven
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ T : Finset U, |starCoeff N c T| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ 2 ^ 60 := sum_le_pivot_budget (by
      rw [Fintype.card_finset]
      exact Nat.pow_le_pow_right (by norm_num) hn) _
        (fun T => (hb T).trans (by norm_num))

variable [LinearOrder U]

theorem pivotGroup_card_bound (hn : Fintype.card U ≤ 36) (i : U) :
    Fintype.card (pivotGroup (supports3 (U := U)) i) ≤ 2 ^ 36 := by
  rw [Fintype.card_coe]
  exact (card_le_univ _).trans (by
    rw [Fintype.card_finset]
    exact Nat.pow_le_pow_right (by norm_num) hn)

theorem pivotGroup_sizes (hn : Fintype.card U ≤ 36) (i : U)
    (T : pivotGroup (supports3 (U := U)) i) :
    1 ≤ T.1.card - 1 ∧ T.1.card - 1 ≤ 36 := by
  have h3 := supports3_card (mem_filter.mp T.2).1
  have h36 := card_le_univ T.1
  omega

theorem star_pivot_budgets (N : K → Finset U) (c : K → Finset U → ℝ)
    (hc : ∀ k T, |c k T| ≤ 1) (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36)
    (i : U) :
    PivotBudgets (fun T : pivotGroup supports3 i => starCoeff N c T.1)
      (fun T => T.1.card - 1) := by
  apply pivotBudgets_of_card (pivotGroup_card_bound hn i)
  · intro T
    exact (starCoeff_abs_le N c hc T.1).trans (by exact_mod_cast hK)
  · exact fun T => (pivotGroup_sizes hn i T).1
  · exact fun T => (pivotGroup_sizes hn i T).2

variable {p : ℕ} [Fact p.Prime]

theorem star_pivotD2_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    pivotD2 L supports3 (starCoeff N c) i ≤ 2 ^ 142 :=
  pivD2_uniform _ _ (fun T => (pivotGroup_sizes hn i T).1)
    (star_pivot_budgets N c hc hn hK i) (by positivity) one_div_sqrt_prime_le_one (hd i) (he i)

theorem star_pivotK_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    pivotK L supports3 (starCoeff N c) i ≤ 2 ^ 80 :=
  pivK_uniform _ _ (fun T => (pivotGroup_sizes hn i T).1)
    (star_pivot_budgets N c hc hn hK i) one_div_sqrt_prime_le_one (hd i)
    (Fintype.card_pos_iff.mpr ⟨i⟩) hn (he i)


theorem star_sqrt_pivotD2_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    Real.sqrt (pivotD2 L supports3 (starCoeff N c) i) ≤ 2 ^ 71 := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  convert star_pivotD2_le L N c hc hn hK hd he i using 1
  norm_num

theorem star_prefix_D_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L supports3 (starCoeff N c) j) ≤
      36 * 2 ^ 71 := by
  calc _ ≤ ∑ j : U, Real.sqrt (pivotD2 L supports3 (starCoeff N c) j) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Real.sqrt_nonneg _)
    _ ≤ ∑ _j : U, (2 : ℝ) ^ 71 :=
        sum_le_sum fun j _ => star_sqrt_pivotD2_le L N c hc hn hK hd he j
    _ ≤ 36 * 2 ^ 71 := sum_const_bound hn (by positivity)

theorem starMstar_uniform (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) :
    Sarkozy.Spectral.starMstar L N c ≤ 2 ^ 84 * (1 / Real.sqrt p) := by
  let r : ℝ := 1 / Real.sqrt p
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := one_div_sqrt_prime_le_one
  have hD : ∑ i, pivotD2 L supports3 (starCoeff N c) i ≤ 36 * 2 ^ 142 := by
    calc _ ≤ ∑ _i : U, (2 : ℝ) ^ 142 :=
          sum_le_sum fun i _ => star_pivotD2_le L N c hc hn hK hd he i
      _ ≤ _ := sum_const_bound hn (by positivity)
  have hcross : ∑ i, pivotK L supports3 (starCoeff N c) i *
      ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L supports3 (starCoeff N c) j) ≤
      36 * (2 ^ 80 * (36 * 2 ^ 71)) := by
    calc _ ≤ ∑ _i : U, (2 : ℝ) ^ 80 * (36 * 2 ^ 71) := sum_le_sum fun i _ =>
          mul_le_mul (star_pivotK_le L N c hc hn hK hd he i)
            (star_prefix_D_le L N c hc hn hK hd he i)
            (sum_nonneg fun _ _ => Real.sqrt_nonneg _) (by positivity)
      _ ≤ _ := sum_const_bound hn (by positivity)
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
    (hn : Fintype.card U ≤ 36) (hK : Fintype.card K ≤ 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) :
    Sarkozy.Spectral.starZstar L N c ≤ 2 ^ 88 * (1 / Real.sqrt p) ^ 2 := by
  have hsum : ∑ i, pivotK L supports3 (starCoeff N c) i ≤ 36 * 2 ^ 80 := by
    calc _ ≤ ∑ _i : U, (2 : ℝ) ^ 80 :=
          sum_le_sum fun i _ => star_pivotK_le L N c hc hn hK hd he i
      _ ≤ _ := sum_const_bound hn (by positivity)
  have ht : ∑ i, pivotK L supports3 (starCoeff N c) i + |starBEven N c| ≤ (2 : ℝ) ^ 88 :=
    (add_le_add hsum (starBEven_abs_le N c hc hn hK)).trans (by norm_num)
  unfold Sarkozy.Spectral.starZstar
  exact (mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (mul_comm _ _)


end Sarkozy.SecondOrder.AtMost
