module

public import Sarkozy.Moments.Normalization

/-!
# Typed mixtures of mixed moment bounds

The multilinear mixture estimate is reduced to one-coordinate norm deficits.
The final theorem explicitly balances bad components against the deficit
provided by low-exponent components; middle components need no charge.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {V X J : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype X] [Nonempty X] [Fintype J]

theorem mixedLpBound_mixture_of_scalar (weights : FiniteLaw J)
    (laws : J → FiniteLaw (V → X)) (r : J → ℝ) {R : ℝ} (hR : 0 < R)
    (hlocal : ∀ j, MixedLpBound (laws j) (r j) 1)
    (hscalar : ∀ f : X → ℝ, (∀ x, 0 ≤ f x) → (FiniteLaw.uniform X).lpNorm R f = 1 →
      weights.expect (fun j => (FiniteLaw.uniform X).lpNorm (r j) f ^ Fintype.card V) ≤ 1) :
    MixedLpBound (FiniteLaw.mixture weights laws) R 1 := by
  apply mixedLpBound_of_normalized _ hR
  intro f hf hn
  rw [FiniteLaw.expect_mixture]
  apply (weights.expect_mono (fun j =>
    (le_abs_self _).trans (by simpa only [one_mul] using hlocal j f))).trans
  have hc : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply weights.expect_prod_le_one_of_moments (fun _ : V => Fintype.card V)
    (fun _ => hc) (by simp [hc.ne'])
    (fun v j => (FiniteLaw.uniform X).lpNorm (r j) (f v))
    (fun _ _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _)
  intro v
  simpa only [Real.rpow_natCast] using hscalar (f v) (hf v) (hn v)

omit [DecidableEq V] [Nonempty V] in
theorem scalar_typed_mixture (weights : FiniteLaw J) (r C : J → ℝ)
    {s R : ℝ} (hs : 0 < s) (hsR : s < R) (hr : ∀ j, 0 < r j)
    (hbalance : (∑ j ∈ Finset.univ.filter (fun j => R < r j), weights.weight j * C j) ≤
      ∑ j ∈ Finset.univ.filter (fun j => r j ≤ s), weights.weight j)
    (f : X → ℝ) (hn : (FiniteLaw.uniform X).lpNorm R f = 1)
    (hbad : ∀ j, R < r j → (FiniteLaw.uniform X).lpNorm (r j) f ^ Fintype.card V - 1 ≤
      C j * (1 - (FiniteLaw.uniform X).lpNorm s f ^ Fintype.card V)) :
    weights.expect (fun j => (FiniteLaw.uniform X).lpNorm (r j) f ^ Fintype.card V) ≤ 1 := by
  classical
  let a : ℝ := (FiniteLaw.uniform X).lpNorm s f ^ Fintype.card V
  have hsone : (FiniteLaw.uniform X).lpNorm s f ≤ 1 := by
    simpa only [hn] using (FiniteLaw.uniform X).lpNorm_mono hs hsR.le f
  have ha : a ≤ 1 := pow_le_one₀ ((FiniteLaw.uniform X).lpNorm_nonneg _ _) hsone
  let cost : J → ℝ := fun j => (if R < r j then C j else 0) - (if r j ≤ s then 1 else 0)
  have hcost : weights.expect cost ≤ 0 := by
    unfold FiniteLaw.expect cost
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      ← Finset.sum_filter]
    exact sub_nonpos.mpr hbalance
  have hpoint (j : J) : (FiniteLaw.uniform X).lpNorm (r j) f ^ Fintype.card V ≤
      1 + cost j * (1 - a) := by
    by_cases hjlow : r j ≤ s
    · have hjbad : ¬R < r j := by linarith
      have hnorm := (FiniteLaw.uniform X).lpNorm_mono (hr j) hjlow f
      have hp := pow_le_pow_left₀ ((FiniteLaw.uniform X).lpNorm_nonneg _ _) hnorm (Fintype.card V)
      simp only [cost, ite_eq_right hjbad, ite_eq_left hjlow]
      dsimp only [a]
      linarith
    · by_cases hjbad : R < r j
      · simp only [cost, ite_eq_left hjbad, ite_eq_right hjlow]
        have hh := hbad j hjbad
        dsimp only [a]
        linarith
      · have hnorm : (FiniteLaw.uniform X).lpNorm (r j) f ≤ 1 := by
          simpa only [hn] using (FiniteLaw.uniform X).lpNorm_mono (hr j) (le_of_not_gt hjbad) f
        have hp := pow_le_one₀ ((FiniteLaw.uniform X).lpNorm_nonneg _ _) hnorm (n := Fintype.card V)
        simpa only [cost, ite_eq_right hjbad, ite_eq_right hjlow, sub_self, zero_mul, add_zero] using hp
  apply (weights.expect_mono hpoint).trans
  rw [FiniteLaw.expect_add, FiniteLaw.expect_const, FiniteLaw.expect_mul_const]
  have hnegative := mul_nonpos_of_nonpos_of_nonneg hcost (sub_nonneg.mpr ha)
  linarith

/-- The finite mixture part of the typed-mixture lemma. The remaining scalar
input is the quantitative comparison between high and low norms. -/
theorem mixedLpBound_typed_mixture (weights : FiniteLaw J)
    (laws : J → FiniteLaw (V → X)) (r C : J → ℝ)
    {s R : ℝ} (hs : 0 < s) (hsR : s < R) (hr : ∀ j, 0 < r j)
    (hlocal : ∀ j, MixedLpBound (laws j) (r j) 1)
    (hbalance : (∑ j ∈ Finset.univ.filter (fun j => R < r j), weights.weight j * C j) ≤
      ∑ j ∈ Finset.univ.filter (fun j => r j ≤ s), weights.weight j)
    (hscalar : ∀ f : X → ℝ, (∀ x, 0 ≤ f x) → (FiniteLaw.uniform X).lpNorm R f = 1 →
      ∀ j, R < r j → (FiniteLaw.uniform X).lpNorm (r j) f ^ Fintype.card V - 1 ≤
        C j * (1 - (FiniteLaw.uniform X).lpNorm s f ^ Fintype.card V)) :
    MixedLpBound (FiniteLaw.mixture weights laws) R 1 := by
  apply mixedLpBound_mixture_of_scalar weights laws r (hs.trans hsR) hlocal
  intro f hf hn
  exact scalar_typed_mixture weights r C hs hsR hr hbalance f hn (hscalar f hf hn)

end Sarkozy
