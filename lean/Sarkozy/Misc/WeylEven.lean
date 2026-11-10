module

public import Sarkozy.Kernel.RationalApproximation
public import Sarkozy.Kernel.Pairing

@[expose] public section

/-!
# Weyl's inequality with a linear twist (`lem:record:weyl-even`)

`paper/sections/C_kernel.tex`, `lem:record:weyl-even`: let `α ∈ ℝ` and let `a/q` be a reduced
fraction with `q ≥ 1` and `|α - a/q| ≤ q⁻²`. For all `λ ∈ ℝ` and all integers `1 ≤ M' ≤ M`,
`|∑_{m=1}^{M'} e(α m² + λ m)|² ≤ M + 200 (M/q + 1)(M + q log(2q))`; no parity condition on `q`.

**Proof used here.** The paper's proof is Weyl differencing, the geometric-sum bound
`min(|I|, (2‖x‖)⁻¹)`, and a spacing count in blocks of `max(1, ⌊q/4⌋)` consecutive shifts. The
same three steps are in the kernel library ported from OpenAI (`Sarkozy.Kernel`, WP-K):
`quadratic_sum_differencing`, `rational_spacing_sum` (blocks of `⌊q/4⌋` shifts, for `q ≥ 8`) and
their combination `rational_quadratic_sum`, which gives, for `q ≥ 8` and `L ≤ M`,
`‖∑_{m<L} e(α m² + θ m)‖² ≤ M + 2 (8M/q + 1)(2M + 4q(1 + log q))`. This file adds the glue:

* the shift `m ↦ m + 1` from `∑_{m=1}^{M'}` to `∑_{m<M'}` (it changes the linear coefficient to
  `λ + 2α`, which is harmless because the bound is uniform in the twist);
* the comparison `2 (8M/q + 1)(2M + 4q(1 + log q)) ≤ 200 (M/q + 1)(M + q log(2q))`, which uses
  `log 2 > 0.69`;
* the small denominators `q ≤ 7` by the trivial bound `|∑| ≤ M' ≤ M` and `M² ≤ 200 (M/q) M`
  (the paper treats `q ≤ 3` this way and `4 ≤ q ≤ 7` by blocks of one shift).

`e(t) = exp(2πit)` is `Sarkozy.Kernel.expPhase` (`expPhase_eq_exp`); `weyl_even_exp` restates the
lemma with `Complex.exp`.

The reduced fraction is `IsCoprime a q` over `ℤ` (equivalently `Int.gcd a q = 1`,
`weyl_even_gcd`). The lemma is fully proved.
-/

namespace Sarkozy.Misc

open Finset Sarkozy.Kernel

/-- `∑_{m=1}^{M'} e(α m² + λ m)` has the same modulus as `∑_{m<M'} e(α m² + (λ + 2α) m)`. -/
theorem norm_sum_Icc_one_eq (α lam : ℝ) (M' : ℕ) :
    ‖∑ m ∈ Icc 1 M', expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ =
      ‖∑ m ∈ range M', expPhase (α * (m : ℝ) ^ 2 + (lam + 2 * α) * m)‖ := by
  rw [← quadratic_sum_shift α lam M', ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  congr 1
  refine sum_congr (by simp) fun m _ => ?_
  congr 1
  push_cast
  ring

/-- The constant comparison for `q ≥ 8`:
`M + 2 (8M/q + 1)(2M + 4q(1 + log q)) ≤ M + 200 (M/q + 1)(M + q log(2q))`. -/
theorem weyl_constant_le (M q : ℕ) (hq : 8 ≤ q) :
    (M : ℝ) + 2 * (8 * (M : ℝ) / q + 1) * (2 * M + 4 * q * (1 + Real.log q)) ≤
      M + 200 * ((M : ℝ) / q + 1) * (M + q * Real.log (2 * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlog2 : 0.69 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2q : Real.log (2 * q) = Real.log 2 + Real.log q :=
    Real.log_mul (by norm_num) hq0.ne'
  set u : ℝ := (M : ℝ) / q with hu
  have hu0 : 0 ≤ u := div_nonneg (Nat.cast_nonneg M) hq0.le
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h8 : 8 * (M : ℝ) / q = 8 * u := by rw [hu]; ring
  rw [h8, hlog2q]
  have hA : 0 ≤ 2 * (M : ℝ) + 4 * q * (1 + Real.log q) := by positivity
  have hstep1 : 2 * (8 * u + 1) * (2 * M + 4 * q * (1 + Real.log q)) ≤
      16 * (u + 1) * (2 * M + 4 * q * (1 + Real.log q)) := by
    have : 2 * (8 * u + 1) ≤ 16 * (u + 1) := by linarith
    exact mul_le_mul_of_nonneg_right this hA
  have hstep2 : 16 * (2 * (M : ℝ) + 4 * q * (1 + Real.log q)) ≤
      200 * ((M : ℝ) + q * (Real.log 2 + Real.log q)) := by
    nlinarith
  have hstep3 : 16 * (u + 1) * (2 * M + 4 * q * (1 + Real.log q)) ≤
      200 * (u + 1) * ((M : ℝ) + q * (Real.log 2 + Real.log q)) := by
    have hu1 : 0 ≤ u + 1 := by linarith
    have := mul_le_mul_of_nonneg_left hstep2 hu1
    linarith
  linarith

/-- **Weyl's inequality with a linear twist** (`lem:record:weyl-even`): if `a/q` is reduced,
`q ≥ 1` and `|α - a/q| ≤ q⁻²`, then for every `λ` and all `1 ≤ M' ≤ M`,
`|∑_{m=1}^{M'} e(α m² + λ m)|² ≤ M + 200 (M/q + 1)(M + q log(2q))`. No parity condition on `q`.
(The hypothesis `1 ≤ M'` of the paper is not needed: the bound holds for `M' = 0` too.) -/
theorem weyl_even (α lam : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hc : IsCoprime a (q : ℤ))
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (M' M : ℕ) (hM : M' ≤ M) :
    ‖∑ m ∈ Icc 1 M', expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ^ 2 ≤
      M + 200 * ((M : ℝ) / q + 1) * (M + q * Real.log (2 * q)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hlog : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  rcases le_or_gt 8 q with h8 | h8
  · -- `q ≥ 8`: the ported Weyl bound
    rw [norm_sum_Icc_one_eq]
    have hb := rational_quadratic_sum α (lam + 2 * α) a q h8 hc ha M' M hM
    have hrad : 0 ≤ (M : ℝ) + 2 * (8 * (M : ℝ) / q + 1) * (2 * M + 4 * q * (1 + Real.log q)) := by
      have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
      positivity
    have hsq : ‖∑ m ∈ range M', expPhase (α * (m : ℝ) ^ 2 + (lam + 2 * α) * m)‖ ^ 2 ≤
        (M : ℝ) + 2 * (8 * (M : ℝ) / q + 1) * (2 * M + 4 * q * (1 + Real.log q)) := by
      calc _ ≤ (Real.sqrt ((M : ℝ) + 2 * (8 * (M : ℝ) / q + 1) *
            (2 * M + 4 * q * (1 + Real.log q)))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hb 2
        _ = _ := Real.sq_sqrt hrad
    exact hsq.trans (weyl_constant_le M q h8)
  · -- `q ≤ 7`: the trivial bound
    have htriv : ‖∑ m ∈ Icc 1 M', expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ≤ M := by
      calc _ ≤ ∑ m ∈ Icc 1 M', ‖expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ := norm_sum_le _ _
        _ = (M' : ℝ) := by simp
        _ ≤ M := by exact_mod_cast hM
    have hsq : ‖∑ m ∈ Icc 1 M', expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ^ 2 ≤ (M : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriv 2
    have hq7 : (q : ℝ) ≤ 7 := by exact_mod_cast (show q ≤ 7 by omega)
    have hu0 : 0 ≤ (M : ℝ) / q := div_nonneg hM0 hq0.le
    have h1 : (M : ℝ) ^ 2 ≤ 200 * ((M : ℝ) / q) * M := by
      have : (M : ℝ) ≤ 200 * ((M : ℝ) / q) := by
        rw [mul_div_assoc', le_div_iff₀ hq0]
        nlinarith
      nlinarith
    have h2 : 200 * ((M : ℝ) / q) * M ≤ 200 * ((M : ℝ) / q + 1) * (M + q * Real.log (2 * q)) := by
      have hql : 0 ≤ (q : ℝ) * Real.log (2 * q) := mul_nonneg hq0.le hlog
      have : ((M : ℝ) / q) * M ≤ ((M : ℝ) / q + 1) * (M + q * Real.log (2 * q)) :=
        mul_le_mul (by linarith) (by linarith) hM0 (by linarith)
      linarith
    linarith

/-- `lem:record:weyl-even` with the reduced fraction written `gcd(a, q) = 1`. -/
theorem weyl_even_gcd (α lam : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hc : Int.gcd a q = 1)
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (M' M : ℕ) (hM : M' ≤ M) :
    ‖∑ m ∈ Icc 1 M', expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ^ 2 ≤
      M + 200 * ((M : ℝ) / q + 1) * (M + q * Real.log (2 * q)) :=
  weyl_even α lam a q hq (Int.isCoprime_iff_gcd_eq_one.mpr hc) ha M' M hM

/-- `lem:record:weyl-even` with `e(t) = exp(2πit)` written out. -/
theorem weyl_even_exp (α lam : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hc : IsCoprime a (q : ℤ))
    (ha : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (M' M : ℕ) (hM : M' ≤ M) :
    ‖∑ m ∈ Icc 1 M',
        Complex.exp (2 * Real.pi * Complex.I * ((α * (m : ℝ) ^ 2 + lam * m : ℝ) : ℂ))‖ ^ 2 ≤
      M + 200 * ((M : ℝ) / q + 1) * (M + q * Real.log (2 * q)) := by
  simp_rw [← expPhase_eq_exp]
  exact weyl_even α lam a q hq hc ha M' M hM

end Sarkozy.Misc
