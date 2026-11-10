module

public import Sarkozy.JointRows.StarMeanBound

/-! Bounding the star Gram matrices by common exact supports. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

def commonSupports (N : X → Finset Y) (i i' : X) : ℕ :=
  ((N i ∩ N i').powerset.filter fun T => 2 ≤ T.card).card

omit [Fintype X] [DecidableEq X] in
theorem coef_gram_le_count (N : X → Finset Y) (A : X → Finset Y → ℝ)
    (hA : ∀ i T, |A i T| ≤ 1)
    (hsupp : ∀ i T, A i T ≠ 0 → T ⊆ N i) (i i' : X) :
    ∑ T ∈ sets2 Y, |A i T| * |A i' T| ≤ commonSupports N i i' := by
  have ht (T : Finset Y) : |A i T| * |A i' T| ≤
      if T ⊆ N i ∩ N i' then (1 : ℝ) else 0 := by
    split_ifs with hT
    · exact (mul_le_mul (hA i T) (hA i' T) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
    · have hz : A i T = 0 ∨ A i' T = 0 := by
        by_cases h : A i T = 0
        · exact Or.inl h
        · right
          by_contra h'
          exact hT (subset_inter (hsupp i T h) (hsupp i' T h'))
      rcases hz with h | h <;> simp [h]
  calc
    _ ≤ ∑ T ∈ sets2 Y, if T ⊆ N i ∩ N i' then (1 : ℝ) else 0 :=
      sum_le_sum fun T _ => ht T
    _ = commonSupports N i i' := by
      rw [← sum_filter]
      have heq : (sets2 Y).filter (fun T => T ⊆ N i ∩ N i') =
          (N i ∩ N i').powerset.filter (fun T => 2 ≤ T.card) := by
        ext T
        simp only [mem_filter, mem_sets2, mem_powerset, and_comm]
      rw [heq]
      simp [commonSupports]

omit [Fintype X] [DecidableEq X] [Fintype Y] in
theorem prod_support (N : Finset Y) (D : Y → ℝ) (hzero : ∀ j, j ∉ N → D j = 0)
    (T : Finset Y) (hT : (∏ j ∈ T, D j) ≠ 0) : T ⊆ N := by
  intro j hj
  by_contra hn
  exact hT (prod_eq_zero hj (hzero j hn))

variable {p : ℕ} [Fact p.Prime]

theorem rowParity_gram_le_count (D : X → X → ℝ) (N : X → Finset X)
    (hD : ∀ i j, |D i j| ≤ 1) (hzero : ∀ i j, j ∉ N i → D i j = 0) (i i' : X) :
    ∑ T ∈ sets2 X, |rowParityCoef (p := p) D i T| *
      |rowParityCoef (p := p) D i' T| ≤ commonSupports N i i' := by
  apply coef_gram_le_count N _ (abs_rowParityCoef_le_one D hD) _ i i'
  intro k T hT
  exact prod_support (N k) (D k) (hzero k) T (mul_ne_zero_iff.mp hT).2

theorem coefB_gram_le_count (D : X → X → ℝ) (N : X → Finset X)
    (hD : ∀ i j, |D i j| ≤ 1) (hzero : ∀ j i, i ∉ N j → D i j = 0) (j j' : X) :
    ∑ S ∈ sets2 X, |coefB D j S| * |coefB D j' S| ≤ commonSupports N j j' := by
  apply coef_gram_le_count N _ (abs_coefB_le_one D hD) _ j j'
  intro k S hS
  exact prod_support (N k) (fun i => D i k) (hzero k) S hS

end Sarkozy.JointRows.StarOps
