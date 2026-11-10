module

public import Sarkozy.L20Cap.BalancedGeometry

/-!
# The actual subset polynomial for balanced L20 collisions

For every set of pinned vertices, retain its internal-edge price `2^{e(I)}`.
The exact sums in degrees two through six give the polynomial used in the paper.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy.Extraction

noncomputable def balancedPoly (k : ℕ) (a c x y : ℝ) : ℝ :=
  ∑ I ∈ (univ : Finset (Fin 6)).powersetCard k,
    (2 : ℝ) ^ collisionEdgesIn G6 I * ∏ i ∈ I, ![a, a, x, y, c, c] i

theorem balancedPoly_2 (a c x y : ℝ) :
    balancedPoly 2 a c x y =
      a ^ 2 + 8 * a * c + c ^ 2 + 2 * (a + c) * (x + y) + x * y := by
  have hs : (univ : Finset (Fin 6)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3},
        {0, 4}, {0, 5}, {1, 2},
        {1, 3}, {1, 4}, {1, 5},
        {2, 3}, {2, 4}, {2, 5},
        {3, 4}, {3, 5}, {4, 5}} := by
    decide +kernel
  unfold balancedPoly
  rw [hs]
  simp (disch := decide) only [sum_insert, sum_singleton]
  norm_num [collisionEdgesIn, G6, filter_insert, filter_singleton]
  ring

theorem balancedPoly_3 (a c x y : ℝ) :
    balancedPoly 3 a c x y =
      8 * a * c * (a + c) + (a ^ 2 + 8 * a * c + c ^ 2) * (x + y) +
      2 * (a + c) * x * y := by
  have hs : (univ : Finset (Fin 6)).powersetCard 3 =
      {{0, 1, 2}, {0, 1, 3}, {0, 1, 4},
        {0, 1, 5}, {0, 2, 3}, {0, 2, 4},
        {0, 2, 5}, {0, 3, 4}, {0, 3, 5},
        {0, 4, 5}, {1, 2, 3}, {1, 2, 4},
        {1, 2, 5}, {1, 3, 4}, {1, 3, 5},
        {1, 4, 5}, {2, 3, 4}, {2, 3, 5},
        {2, 4, 5}, {3, 4, 5}} := by
    decide +kernel
  unfold balancedPoly
  rw [hs]
  simp (disch := decide) only [sum_insert, sum_singleton]
  norm_num [collisionEdgesIn, G6, filter_insert, filter_singleton]
  ring

theorem balancedPoly_4 (a c x y : ℝ) :
    balancedPoly 4 a c x y =
      16 * a ^ 2 * c ^ 2 + 8 * a * c * (a + c) * (x + y) +
      (a ^ 2 + 8 * a * c + c ^ 2) * x * y := by
  have hs : (univ : Finset (Fin 6)).powersetCard 4 =
      {{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5},
        {0, 1, 3, 4}, {0, 1, 3, 5}, {0, 1, 4, 5},
        {0, 2, 3, 4}, {0, 2, 3, 5}, {0, 2, 4, 5},
        {0, 3, 4, 5}, {1, 2, 3, 4}, {1, 2, 3, 5},
        {1, 2, 4, 5}, {1, 3, 4, 5}, {2, 3, 4, 5}} := by
    decide +kernel
  unfold balancedPoly
  rw [hs]
  simp (disch := decide) only [sum_insert, sum_singleton]
  norm_num [collisionEdgesIn, G6, filter_insert, filter_singleton]
  ring

theorem balancedPoly_5 (a c x y : ℝ) :
    balancedPoly 5 a c x y =
      16 * a ^ 2 * c ^ 2 * (x + y) + 8 * a * c * (a + c) * x * y := by
  have hs : (univ : Finset (Fin 6)).powersetCard 5 =
      {{0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 4, 5},
        {0, 1, 3, 4, 5}, {0, 2, 3, 4, 5}, {1, 2, 3, 4, 5}} := by
    decide +kernel
  unfold balancedPoly
  rw [hs]
  simp (disch := decide) only [sum_insert, sum_singleton]
  norm_num [collisionEdgesIn, G6, filter_insert, filter_singleton]
  ring

theorem balancedPoly_6 (a c x y : ℝ) :
    balancedPoly 6 a c x y =
      16 * a ^ 2 * c ^ 2 * x * y := by
  have hs : (univ : Finset (Fin 6)).powersetCard 6 =
      {{0, 1, 2, 3, 4, 5}} := by
    decide +kernel
  unfold balancedPoly
  rw [hs]
  simp (disch := decide) only [sum_singleton]
  norm_num [collisionEdgesIn, G6, filter_insert, filter_singleton]
  ring

/-- The degree-at-least-two subset sum equals the balanced generating polynomial
with its constant and linear terms removed. -/
theorem balancedPoly_sum (a c x y : ℝ) :
    ∑ k ∈ Icc 2 6, balancedPoly k a c x y =
      Fpoly a c * (1 + x) * (1 + y) - 1 - 2 * (a + c) - x - y := by
  have hk : Icc 2 6 = ({2, 3, 4, 5, 6} : Finset ℕ) := by decide +kernel
  rw [hk]
  norm_num [balancedPoly_2, balancedPoly_3, balancedPoly_4, balancedPoly_5,
    balancedPoly_6, Fpoly_eq]
  ring

end Sarkozy.L20Cap
