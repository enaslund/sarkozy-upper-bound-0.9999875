module

public import Sarkozy.Moments.FiniteAlphabet
public import Sarkozy.Moments.Mixed

/-!
# The prefix allowances at density exponent `θ ≤ 51/50` (`thm:density:iid-prefix`(d), arithmetic)

`paper/sections/30_density_moment_upgrade.tex`, proof of `thm:density:iid-prefix`(d).

* `lpNorm_le_card_rpow_mul_lpNorm`: finite-space norm comparison,
  `‖f‖_q ≤ Q^{1/p - 1/q} ‖f‖_p` for `0 < p ≤ q` and the uniform probability on `Q` points.
* `mixedLpBound_uniform_marginals_theta`: the paper's bound for the unchanged small primes. Every
  law with uniform one-slot marginals on `d` slots satisfies
  `|Λ((f_v)_v)| ≤ Q^{θ - 1} ∏_v ‖f_v‖_{d/θ}` for `θ ≥ 1` (ordinary Hölder and norm comparison);
  at `d = 72` this is the displayed inequality of the proof.
* `small_prime_sum_le`, `large_prime_sum_le`: bounding the number of primes by the number of
  integers, the sums of the per-prime terms `12 · 2^{-m} · Q^{θ-1} · p^{2ma}` (`p < 2^16`,
  `Q = p^{2m}`) and `12 · 2^{-m} · p^{2ma}` (`p < 2^512`) are at most
  `12 · 2^{16 + m(-1 + 32(a+θ-1))}` and `12 · 2^{512 + m(-1 + 1024 a)}`.
* `prefix_allowance_bound`: at `m = 8192`, `0 < a ≤ 91/100000` and `1 < θ ≤ 51/50`,
  `12·2^{16+m(-1+32(a+θ-1))} + 12·2^{512+m(-1+1024a)} ≤ 12(2^{-2694} + 2^{-46}) < 2·10^{-13} < 10^{-12}`,
  and the first term is below `2^{-2600}`.

Not formalized: the definitions of the aggregate allowances `S, A, T` of
`def:closing-quantities` and the identification of their prefix terms with the per-prime terms
above (mass `2^{-m}` of an equality event, the factor `12 = 6 · 2`, the conductor price
`p^{2ma}`); here those terms are taken as given by the paper's proof.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

variable {X : Type*} [Fintype X] [Nonempty X]

/-- **Finite-space norm comparison**: `‖f‖_q ≤ |X|^{1/p - 1/q} ‖f‖_p` for `0 < p ≤ q`. -/
theorem lpNorm_le_card_rpow_mul_lpNorm {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (f : X → ℝ) :
    (FiniteLaw.uniform X).lpNorm q f ≤
      (Fintype.card X : ℝ) ^ (1 / p - 1 / q) * (FiniteLaw.uniform X).lpNorm p f := by
  set U := FiniteLaw.uniform X
  set Q : ℝ := (Fintype.card X : ℝ) with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact_mod_cast Fintype.card_pos
  have hq : 0 < q := hp.trans_le hpq
  set N := U.lpNorm p f with hN
  have hN0 : 0 ≤ N := U.lpNorm_nonneg _ _
  -- pointwise `|f|^q ≤ |f|^p (Q^{1/p} N)^{q-p}`
  have hpt : ∀ x, |f x| ^ q ≤ |f x| ^ p * (Q ^ (1 / p) * N) ^ (q - p) := by
    intro x
    have hb := abs_le_card_rpow_mul_lpNorm hp f x
    have hsplit : |f x| ^ q = |f x| ^ p * |f x| ^ (q - p) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by linarith)]
      congr 1
      ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hb (by linarith))
      (Real.rpow_nonneg (abs_nonneg _) _)
  have hmom : U.moment q f ≤ U.moment p f * (Q ^ (1 / p) * N) ^ (q - p) := by
    unfold FiniteLaw.moment
    rw [← FiniteLaw.expect_mul_const]
    exact U.expect_mono hpt
  have hmp : U.moment p f = N ^ p := (U.lpNorm_rpow hp.ne' f).symm
  rw [hmp] at hmom
  have hrhs : N ^ p * (Q ^ (1 / p) * N) ^ (q - p) = (Q ^ (1 / p - 1 / q) * N) ^ q := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by linarith) _) hN0,
      Real.mul_rpow (Real.rpow_nonneg (by linarith) _) hN0, ← Real.rpow_mul (by linarith),
      ← Real.rpow_mul (by linarith)]
    have e1 : 1 / p * (q - p) = (1 / p - 1 / q) * q := by field_simp
    rw [e1]
    have e2 : N ^ p * N ^ (q - p) = N ^ q := by
      rcases hN0.eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow hp.ne', Real.zero_rpow hq.ne', zero_mul]
      · rw [← Real.rpow_add hpos]
        congr 1
        ring
    calc N ^ p * (Q ^ ((1 / p - 1 / q) * q) * N ^ (q - p))
        = Q ^ ((1 / p - 1 / q) * q) * (N ^ p * N ^ (q - p)) := by ring
      _ = Q ^ ((1 / p - 1 / q) * q) * N ^ q := by rw [e2]
  rw [hrhs] at hmom
  have hc0 : 0 ≤ Q ^ (1 / p - 1 / q) * N := mul_nonneg (Real.rpow_nonneg (by linarith) _) hN0
  calc U.lpNorm q f = U.moment q f ^ (1 / q) := rfl
    _ ≤ ((Q ^ (1 / p - 1 / q) * N) ^ q) ^ (1 / q) :=
        Real.rpow_le_rpow (U.moment_nonneg _ _) hmom (by positivity)
    _ = Q ^ (1 / p - 1 / q) * N := by
        rw [← Real.rpow_mul hc0, mul_one_div_cancel hq.ne', Real.rpow_one]

/-- **The unchanged small primes** (proof of `thm:density:iid-prefix`(d)): a law with uniform
one-slot marginals on `d` slots has `|Λ((f_v)_v)| ≤ Q^{θ-1} ∏_v ‖f_v‖_{d/θ}`, `θ ≥ 1`. -/
theorem mixedLpBound_uniform_marginals_theta {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (μ : FiniteLaw (V → X)) (hm : HasUniformMarginals μ) {θ : ℝ} (hθ : 1 ≤ θ) :
    MixedLpBound μ ((Fintype.card V : ℝ) / θ) ((Fintype.card X : ℝ) ^ (θ - 1)) := by
  have hd : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hθ0 : 0 < θ := by linarith
  have h := mixedLpBound_of_uniform_marginals μ hm
  have hp : 0 < (Fintype.card V : ℝ) / θ := div_pos hd hθ0
  have hpq : (Fintype.card V : ℝ) / θ ≤ Fintype.card V := div_le_self hd.le hθ
  intro f
  refine (h f).trans ?_
  rw [one_mul]
  have hexp : (Fintype.card X : ℝ) ^ (θ - 1) =
      ∏ _v : V, (Fintype.card X : ℝ) ^ (1 / ((Fintype.card V : ℝ) / θ) - 1 / Fintype.card V) := by
    rw [Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    field_simp
  rw [hexp, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun v _ => (FiniteLaw.uniform X).lpNorm_nonneg _ _)
    (fun v _ => lpNorm_le_card_rpow_mul_lpNorm hp hpq (f v))

/-- **Small primes, counted by integers**: for any set `P` of integers below `2^B` (`B = 16`),
`∑_{p ∈ P} 12 · 2^{-m} · (p^{2m})^{θ-1} · (p^{2m})^a ≤ 12 · 2^{B + m(-1 + 2B(a+θ-1))}`. -/
theorem small_prime_sum_le {B m : ℕ} {a θ : ℝ} (ha : 0 ≤ a) (hθ : 1 ≤ θ) (P : Finset ℕ)
    (hP : P ⊆ range (2 ^ B)) :
    ∑ p ∈ P, 12 * (2 : ℝ) ^ (-(m : ℝ)) * ((p : ℝ) ^ (2 * m)) ^ (θ - 1) * ((p : ℝ) ^ (2 * m)) ^ a ≤
      12 * (2 : ℝ) ^ ((B : ℝ) + m * (-1 + 2 * B * (a + θ - 1))) := by
  have hterm : ∀ p ∈ P, 12 * (2 : ℝ) ^ (-(m : ℝ)) * ((p : ℝ) ^ (2 * m)) ^ (θ - 1) *
      ((p : ℝ) ^ (2 * m)) ^ a ≤ 12 * (2 : ℝ) ^ ((m : ℝ) * (-1 + 2 * B * (a + θ - 1))) := by
    intro p hp
    have hpB : (p : ℝ) ≤ (2 : ℝ) ^ B := by
      have := mem_range.mp (hP hp)
      exact_mod_cast this.le
    have hQ : (p : ℝ) ^ (2 * m) ≤ (2 : ℝ) ^ ((2 * B * m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      calc (p : ℝ) ^ (2 * m) ≤ ((2 : ℝ) ^ B) ^ (2 * m) := pow_le_pow_left₀ (Nat.cast_nonneg _) hpB _
        _ = (2 : ℝ) ^ (2 * B * m) := by rw [← pow_mul]; ring_nf
    have hQ0 : (0 : ℝ) ≤ (p : ℝ) ^ (2 * m) := by positivity
    have h1 := Real.rpow_le_rpow hQ0 hQ (by linarith : (0 : ℝ) ≤ θ - 1)
    have h2 := Real.rpow_le_rpow hQ0 hQ ha
    rw [← Real.rpow_mul (by norm_num)] at h1 h2
    calc 12 * (2 : ℝ) ^ (-(m : ℝ)) * ((p : ℝ) ^ (2 * m)) ^ (θ - 1) * ((p : ℝ) ^ (2 * m)) ^ a
        ≤ 12 * (2 : ℝ) ^ (-(m : ℝ)) * (2 : ℝ) ^ (((2 * B * m : ℕ) : ℝ) * (θ - 1)) *
            (2 : ℝ) ^ (((2 * B * m : ℕ) : ℝ) * a) := by
          apply mul_le_mul _ h2 (Real.rpow_nonneg hQ0 _) (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 12 * (2 : ℝ) ^ ((m : ℝ) * (-1 + 2 * B * (a + θ - 1))) := by
          rw [mul_assoc, mul_assoc, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
          congr 2
          push_cast
          ring
  calc ∑ p ∈ P, 12 * (2 : ℝ) ^ (-(m : ℝ)) * ((p : ℝ) ^ (2 * m)) ^ (θ - 1) *
        ((p : ℝ) ^ (2 * m)) ^ a
      ≤ ∑ _p ∈ P, 12 * (2 : ℝ) ^ ((m : ℝ) * (-1 + 2 * B * (a + θ - 1))) := sum_le_sum hterm
    _ = (P.card : ℝ) * (12 * (2 : ℝ) ^ ((m : ℝ) * (-1 + 2 * B * (a + θ - 1)))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((2 : ℝ) ^ (B : ℝ)) * (12 * (2 : ℝ) ^ ((m : ℝ) * (-1 + 2 * B * (a + θ - 1)))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc := card_le_card hP
        rw [card_range] at hc
        rw [Real.rpow_natCast]
        exact_mod_cast hc
    _ = 12 * (2 : ℝ) ^ ((B : ℝ) + m * (-1 + 2 * B * (a + θ - 1))) := by
        rw [Real.rpow_add (by norm_num)]
        ring

/-- **Large primes, counted by integers**: for any set `P` of integers below `2^B` (`B = 512`),
`∑_{p ∈ P} 12 · 2^{-m} · (p^{2m})^a ≤ 12 · 2^{B + m(-1 + 2B a)}`. -/
theorem large_prime_sum_le {B m : ℕ} {a : ℝ} (ha : 0 ≤ a) (P : Finset ℕ) (hP : P ⊆ range (2 ^ B)) :
    ∑ p ∈ P, 12 * (2 : ℝ) ^ (-(m : ℝ)) * ((p : ℝ) ^ (2 * m)) ^ a ≤
      12 * (2 : ℝ) ^ ((B : ℝ) + m * (-1 + 2 * B * a)) := by
  have h := small_prime_sum_le (m := m) (a := a) (θ := 1) ha le_rfl P hP
  simp only [sub_self, Real.rpow_zero, mul_one, add_sub_cancel_right] at h
  exact h

/-- **The numerical bound of `thm:density:iid-prefix`(d)** at `m = 8192`, for `a ≤ 91/100000` and
`θ ≤ 51/50` (the paper's ranges `0 < a`, `1 < θ`; the lower ends are not needed). Only the
arithmetic of (d): the allowances `S, A, T` themselves are not defined here. -/
theorem prefix_allowance_bound {a θ : ℝ} (ha1 : a ≤ 91 / 100000) (hθ1 : θ ≤ 51 / 50) :
    12 * (2 : ℝ) ^ ((16 : ℝ) + 8192 * (-1 + 32 * (a + θ - 1))) +
        12 * (2 : ℝ) ^ ((512 : ℝ) + 8192 * (-1 + 1024 * a)) ≤
      12 * ((2 : ℝ) ^ (-2694 : ℝ) + (2 : ℝ) ^ (-46 : ℝ)) ∧
    12 * ((2 : ℝ) ^ (-2694 : ℝ) + (2 : ℝ) ^ (-46 : ℝ)) < 2 * 10 ^ (-13 : ℤ) ∧
    (2 * 10 ^ (-13 : ℤ) : ℝ) < 10 ^ (-12 : ℤ) ∧
    12 * (2 : ℝ) ^ ((16 : ℝ) + 8192 * (-1 + 32 * (a + θ - 1))) < (2 : ℝ) ^ (-2600 : ℝ) := by
  have he1 : (16 : ℝ) + 8192 * (-1 + 32 * (a + θ - 1)) ≤ -2694 := by nlinarith
  have he2 : (512 : ℝ) + 8192 * (-1 + 1024 * a) ≤ -46 := by nlinarith
  have hp1 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he1
  have hp2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he2
  have h100 : (2 : ℝ) ^ (-2694 : ℝ) ≤ (2 : ℝ) ^ (-100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hz100 : (2 : ℝ) ^ (-100 : ℝ) = 1 / 2 ^ 100 := by
    rw [show (-100 : ℝ) = ((-100 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hz46 : (2 : ℝ) ^ (-46 : ℝ) = 1 / 2 ^ 46 := by
    rw [show (-46 : ℝ) = ((-46 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  refine ⟨by linarith, ?_, by norm_num, ?_⟩
  · calc 12 * ((2 : ℝ) ^ (-2694 : ℝ) + (2 : ℝ) ^ (-46 : ℝ))
        ≤ 12 * ((2 : ℝ) ^ (-100 : ℝ) + (2 : ℝ) ^ (-46 : ℝ)) := by linarith
      _ < 2 * 10 ^ (-13 : ℤ) := by rw [hz100, hz46]; norm_num
  · have hsplit : (2 : ℝ) ^ (-2694 : ℝ) = (2 : ℝ) ^ (-94 : ℝ) * (2 : ℝ) ^ (-2600 : ℝ) := by
      rw [← Real.rpow_add (by norm_num)]
      norm_num
    have hz94 : (2 : ℝ) ^ (-94 : ℝ) = 1 / 2 ^ 94 := by
      rw [show (-94 : ℝ) = ((-94 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-2600 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    calc 12 * (2 : ℝ) ^ ((16 : ℝ) + 8192 * (-1 + 32 * (a + θ - 1)))
        ≤ 12 * (2 : ℝ) ^ (-2694 : ℝ) := by linarith
      _ = (12 * (1 / 2 ^ 94)) * (2 : ℝ) ^ (-2600 : ℝ) := by rw [hsplit, hz94]; ring
      _ < 1 * (2 : ℝ) ^ (-2600 : ℝ) := by
          apply mul_lt_mul_of_pos_right _ hpos
          norm_num
      _ = (2 : ℝ) ^ (-2600 : ℝ) := one_mul _

end Sarkozy.DensityMoments
