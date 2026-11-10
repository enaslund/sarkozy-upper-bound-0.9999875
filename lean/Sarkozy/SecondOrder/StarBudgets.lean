module

public import Sarkozy.SecondOrder.PivotUniform
public import Sarkozy.SecondOrder.StarMean
public import Sarkozy.Spectral.GlueStarOp
public import Sarkozy.Spectral.TwoVariable

/-!
# Finite support and coefficient budgets for the root stars

These estimates count all possible supports. They are deliberately generous
and are used only in the very large prime tail.
-/

@[expose] public section

namespace Sarkozy.SecondOrder

open Finset Sarkozy.Target

variable {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]

omit [Fintype U] in
theorem starCoeff_abs_le (N : K → Finset U) (c : K → Finset U → ℝ)
    (hc : ∀ k T, |c k T| ≤ 1) (T : Finset U) :
    |starCoeff N c T| ≤ Fintype.card K := by
  unfold starCoeff
  calc |∑ k, if T ⊆ N k then c k T else 0|
      ≤ ∑ k, |if T ⊆ N k then c k T else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : K, (1 : ℝ) := sum_le_sum fun k _ => by split_ifs <;> simp_all
    _ = Fintype.card K := by simp

theorem starBEven_abs_le (N : K → Finset U) (c : K → Finset U → ℝ)
    (hc : ∀ k T, |c k T| ≤ 1) (hn : Fintype.card U = 36) (hK : Fintype.card K = 36) :
    |starBEven N c| ≤ 2 ^ 60 := by
  have hb : ∀ T, |starCoeff N c T| ≤ 36 := by
    intro T
    simpa only [hK, Nat.cast_ofNat] using starCoeff_abs_le N c hc T
  unfold starBEven
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ T : Finset U, |starCoeff N c T| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ 2 ^ 60 := sum_le_pivot_budget (by simp [Fintype.card_finset, hn]) _
        (fun T => (hb T).trans (by norm_num))

variable [LinearOrder U]

theorem pivotGroup_card_bound (hn : Fintype.card U = 36) (i : U) :
    Fintype.card (pivotGroup (supports3 (U := U)) i) ≤ 2 ^ 36 := by
  rw [Fintype.card_coe]
  exact (card_le_univ _).trans_eq (by rw [Fintype.card_finset, hn])

theorem pivotGroup_sizes (hn : Fintype.card U = 36) (i : U)
    (T : pivotGroup (supports3 (U := U)) i) :
    1 ≤ T.1.card - 1 ∧ T.1.card - 1 ≤ 36 := by
  have h3 := supports3_card (mem_filter.mp T.2).1
  have h36 := card_le_univ T.1
  rw [hn] at h36
  omega

theorem star_pivot_budgets (N : K → Finset U) (c : K → Finset U → ℝ)
    (hc : ∀ k T, |c k T| ≤ 1) (hn : Fintype.card U = 36) (hK : Fintype.card K = 36)
    (i : U) :
    PivotBudgets (fun T : pivotGroup supports3 i => starCoeff N c T.1)
      (fun T => T.1.card - 1) := by
  apply pivotBudgets_of_card (pivotGroup_card_bound hn i)
  · intro T
    simpa only [hK, Nat.cast_ofNat] using starCoeff_abs_le N c hc T.1
  · exact fun T => (pivotGroup_sizes hn i T).1
  · exact fun T => (pivotGroup_sizes hn i T).2

variable {p : ℕ} [Fact p.Prime]

theorem one_div_sqrt_prime_le_one : (1 : ℝ) / Real.sqrt p ≤ 1 := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact (div_le_one (Real.sqrt_pos.mpr (by linarith))).mpr (Real.one_le_sqrt.mpr hp)

theorem star_pivotD2_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U = 36) (hK : Fintype.card K = 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    pivotD2 L supports3 (starCoeff N c) i ≤ 2 ^ 142 :=
  pivD2_uniform _ _ (fun T => (pivotGroup_sizes hn i T).1)
    (star_pivot_budgets N c hc hn hK i) (by positivity) one_div_sqrt_prime_le_one (hd i) (he i)

theorem star_pivotK_le (L : PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) (hc : ∀ k T, |c k T| ≤ 1)
    (hn : Fintype.card U = 36) (hK : Fintype.card K = 36)
    (hd : ∀ i, (L.N i).card ≤ 10) (he : ∀ i, L.e i ≤ 1 / 2) (i : U) :
    pivotK L supports3 (starCoeff N c) i ≤ 2 ^ 80 :=
  pivK_uniform _ _ (fun T => (pivotGroup_sizes hn i T).1)
    (star_pivot_budgets N c hc hn hK i) one_div_sqrt_prime_le_one (hd i)
    (by omega) hn.le (he i)

end Sarkozy.SecondOrder

namespace Sarkozy.Spectral

open Finset Sarkozy.Labellings

theorem starCoef_abs_le {p : ℕ} [Fact p.Prime] {V : Type*} [Fintype V] [DecidableEq V]
    (D : Cuts.SpecData V) (k : D.cut.Half) (J : Finset D.cut.Half) :
    |starCoef (p := p) D k J| ≤ 1 := by
  unfold starCoef
  rw [abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
    (fun j _ => abs_quadraticChar_le_one _)

end Sarkozy.Spectral
