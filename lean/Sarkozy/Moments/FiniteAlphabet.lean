module

public import Sarkozy.Moments.Energy

/-!
# A mixed `Lᵖ` constant on a fixed finite alphabet

In the proof of `lem:density:global-moment` (`paper/sections/31_density_induction_upgrade.tex`)
the coordinates outside the tail take values in one finite set independent of the
scale, and "ordinary Hölder and finite-space norm comparison give them a finite
mixed `L³⁶` constant". This is that statement: every probability law on `V → X`
has mixed `Lᵖ` constant at most `|X|^(|V|/p)`, because `‖f‖_∞ ≤ |X|^(1/p) ‖f‖_p`
for the uniform probability on `X`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {X : Type*} [Fintype X] [Nonempty X]

/-- `|f x| ≤ |X|^(1/p) ‖f‖_p` for the uniform probability on `X`. -/
theorem abs_le_card_rpow_mul_lpNorm {p : ℝ} (hp : 0 < p) (f : X → ℝ) (x : X) :
    |f x| ≤ (Fintype.card X : ℝ) ^ (1 / p) * (FiniteLaw.uniform X).lpNorm p f := by
  set U := FiniteLaw.uniform X
  have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hsum : |f x| ^ p ≤ ∑ y, |f y| ^ p :=
    Finset.single_le_sum (f := fun y => |f y| ^ p)
      (fun y _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ x)
  have hmom : U.moment p f = (∑ y, |f y| ^ p) / Fintype.card X := by
    unfold FiniteLaw.moment
    exact FiniteLaw.expect_uniform _
  have hpow : |f x| ^ p ≤ (Fintype.card X : ℝ) * U.moment p f := by
    rw [hmom, mul_div_cancel₀ _ hcard.ne']
    exact hsum
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) hpow
    (by positivity : (0 : ℝ) ≤ 1 / p)
  rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one,
    Real.mul_rpow hcard.le (U.moment_nonneg p f)] at hroot
  exact hroot

/-- **Finite-alphabet mixed constant.** Every probability law on labellings of `V`
by a finite alphabet `X` has mixed `Lᵖ` constant at most `|X|^(|V|/p)`. -/
theorem mixedLpBound_finite_alphabet {V : Type*} [Fintype V] [DecidableEq V]
    (μ : FiniteLaw (V → X)) {p : ℝ} (hp : 0 < p) :
    MixedLpBound μ p ((Fintype.card X : ℝ) ^ ((Fintype.card V : ℝ) / p)) := by
  intro f
  set U := FiniteLaw.uniform X
  set c : ℝ := (Fintype.card X : ℝ) ^ (1 / p)
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpt (z : V → X) : |∏ v, f v (z v)| ≤ ∏ v, (c * U.lpNorm p (f v)) := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun v _ => abs_nonneg _)
      (fun v _ => abs_le_card_rpow_mul_lpNorm hp (f v) (z v))
  have h := (μ.abs_expect_le _).trans (μ.expect_le_const hpt)
  refine h.trans_eq ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

end Sarkozy
