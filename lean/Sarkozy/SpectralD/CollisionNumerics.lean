module

public import Sarkozy.Extraction.CollisionStrata
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Uniform numerical bounds for the root collision estimates

At q ≥ 2^64 the internal degree bound 10 gives a lower count factor, and
the total degree bound 22 gives an upper factor. Both comparisons use exact
rational arithmetic at the endpoint and the proved monotonicity in q.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Labellings Sarkozy.Extraction

theorem sqrt_collision_endpoint : Real.sqrt ((2 : ℝ) ^ 64) = 2 ^ 32 := by
  rw [show 64 = 32 * 2 by rfl, pow_mul, Real.sqrt_sq (by positivity)]

theorem collision_error10 {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    coarseError 10 q 36 ≤ 1 / 10000 := by
  refine (collision_coarseError_anti 10 (by norm_num) (by positivity) hq).trans ?_
  unfold coarseError
  rw [sqrt_collision_endpoint]
  norm_num [coarseH]

theorem collision_error22 {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    coarseError 22 q 72 ≤ 1 / 100 := by
  refine (collision_coarseError_anti 22 (by norm_num) (by positivity) hq).trans ?_
  unfold coarseError
  rw [sqrt_collision_endpoint]
  norm_num [coarseH]

theorem exp_remainder_le_square {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ x ^ 2 := by
  have h := Real.exp_bound (x := x) (by rwa [abs_of_nonneg hx0]) (n := 2) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, Nat.factorial] at h
  rw [abs_le, abs_of_nonneg hx0] at h
  norm_num at h
  nlinarith [h.2, sq_nonneg x]

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem collision_Lint_lower (G : OrientedGraph U) (hn : Fintype.card U = 36)
    (hd : ∀ i, rowsDeg0 G i ≤ 10) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    (9999 / 10000 : ℝ) ^ 36 ≤ collisionLint G q 36 := by
  have he : ∀ i, coarseError (rowsDeg0 G i) q 36 ≤ 1 / 10000 := fun i =>
    (coarseError_mono (by norm_num) (hd i)).trans (collision_error10 hq)
  calc (9999 / 10000 : ℝ) ^ 36 = ∏ _i : U, (9999 / 10000 : ℝ) := by
        simp only [prod_const, card_univ, hn]
    _ ≤ collisionLint G q 36 := prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => by
      dsimp
      linarith [he i])

theorem collision_Ups_upper (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U = 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    collisionUps G ς q 36 ≤ (101 / 100 : ℝ) ^ 36 := by
  have he : ∀ i, coarseError (rowsDeg0 G i + collisionR ς i) q 72 ≤ 1 / 100 := fun i =>
    (coarseError_mono (by norm_num) (by have := hd i; have := hr i; omega)).trans
      (collision_error22 hq)
  calc collisionUps G ς q 36 ≤ ∏ _i : U, (101 / 100 : ℝ) :=
        prod_le_prod₀ (fun i _ => by
          have := coarseError_nonneg (q := q) (by norm_num : (0 : ℝ) ≤ 72)
            (rowsDeg0 G i + collisionR ς i)
          norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 36 = 72 by norm_num]
          linarith) (fun i _ => by
            norm_num only [Nat.cast_ofNat, show (2 : ℝ) * 36 = 72 by norm_num]
            linarith [he i])
    _ = (101 / 100 : ℝ) ^ 36 := by simp only [prod_const, card_univ, hn]

theorem collision_count_ratio (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U = 36) (hd : ∀ i, rowsDeg0 G i ≤ 10)
    (hr : ∀ i, collisionR ς i ≤ 12) {q : ℝ} (hq : 2 ^ 64 ≤ q) :
    collisionUps G ς q 36 / collisionLint G q 36 ≤ 2 := by
  have hL := collision_Lint_lower G hn hd hq
  have hU := collision_Ups_upper G ς hn hd hr hq
  have hL0 : 0 < collisionLint G q 36 := lt_of_lt_of_le (by positivity) hL
  apply (div_le_iff₀ hL0).mpr
  have hnum : (101 / 100 : ℝ) ^ 36 ≤ 2 * (9999 / 10000 : ℝ) ^ 36 := by norm_num
  linarith

end Sarkozy.SpectralD
