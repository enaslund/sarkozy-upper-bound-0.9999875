module

public import Sarkozy.Kernel.UniformRates

@[expose] public section

/-!
# Kernel rates at the cutoff exponent `β = 1/20`

This module does the rate bookkeeping for the uniform kernel approximation
at the exponents of the paper's corollary `cor:kernel20`: moduli
`D ≤ C_D N^(1/20)` and cutoffs `C_H⁻¹ N^(1/40) ≤ H ≤ C_H N^(1/40)`
(`κ = β = 1/20`, cutoff exponent `β/2 = 1/40`). The conclusion is the
uniform bound `‖S - S₀‖_∞ ≤ C H^(-1/3)` of `lem:record:K20-approx`, with
`C` depending only on `C_D` and `C_H`; this is the analytic input to
`prop:record:kernel20`.

The proof applies the parametric estimate `actual_kernel_uniform`
(ported from upstream `FiniteKernel.lean`) with internal circle-method
parameters chosen here: the Dirichlet parameter `T = ⌈N^(7/10)⌉`, the
major-arc threshold `X = N^(3/10)`, the model denominator bound
`L = ⌈D H⌉` and the square-root length `M = ⌊√N⌋`. These internal choices
differ from the paper's arc exponent `η = 17/100` (Appendix C): the upstream
argument bounds the model kernel on minor arcs differently, and its four
error exponents at `(β, κ) = (1/20, 1/20)` with this choice are
`-1/20` (actual kernel, major arcs), `-1/40` (actual kernel, minor arcs,
with `1 + log T ≤ 18 N^(1/16)`), `-3/40` (model kernel), all below `-1/120`,
plus the coefficient error `2^64 H^(-1/3)`. The arc parameters are internal
to the proof and do not appear in the statement.

The bookkeeping follows the upstream rate lemmas `kernel_rate_log`,
`kernel_rate_first`, `kernel_rate_sqrt`, `kernel_rate_second`,
`kernel_rate_third`, `kernel_all_rates`, `kernel_parameter_bounds` and the
assembly `actual_kernel_power_error` of
`lean/OAI/Combinatorics/SquareDifference/UniformRates.lean` in OpenAI's math
repository (revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, Apache
License 2.0), which do the same at the exponents `1/1000, 7/8, 1/8`. The
exponents, the constants and the threshold are new.
-/

namespace Sarkozy

namespace Kernel

open Finset

/-- Exponent monotonicity for a base at least one. -/
lemma rpow_mono_one {n : ℝ} (hn : 1 ≤ n) {a b : ℝ} (h : a ≤ b) : n ^ a ≤ n ^ b :=
  Real.rpow_le_rpow_of_exponent_le hn h

/-- The major-arc error of the actual kernel at the exponents of `cor:kernel20`. -/
lemma twentieth_major (n P D H T M CD CH : ℝ) (hn : 1 ≤ n)
    (hP0 : 0 ≤ P) (hPD : P ≤ D) (hD1 : 1 ≤ D) (hDn : D ≤ CD * n ^ ((1 : ℝ) / 20))
    (hH1 : 1 ≤ H) (hHn : H ≤ CH * n ^ ((1 : ℝ) / 40))
    (hT : n ^ ((7 : ℝ) / 10) ≤ T + 1) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    H * (2 * P * H + 1) * P * (4 * n ^ ((3 : ℝ) / 10) + 8 * Real.pi * n / (T + 1)) * M / n ≤
      3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 * n ^ (-(1 : ℝ) / 20) := by
  have hn0 : 0 < n := by linarith
  have hp : 0 < n ^ ((7 : ℝ) / 10) := Real.rpow_pos_of_pos hn0 _
  have hT0 : 0 < T + 1 := hp.trans_le hT
  have hH0 : 0 ≤ H := by linarith
  have hDH : 1 ≤ D * H := by nlinarith
  have hcost : H * (2 * P * H + 1) * P ≤ 3 * CD ^ 2 * CH ^ 2 * n ^ ((3 : ℝ) / 20) := by
    have hsq1 : (n ^ ((1 : ℝ) / 20)) ^ 2 = n ^ ((1 : ℝ) / 10) := by
      rw [← Real.rpow_natCast (n ^ ((1 : ℝ) / 20)), ← Real.rpow_mul hn0.le]
      norm_num
    have hsq2 : (n ^ ((1 : ℝ) / 40)) ^ 2 = n ^ ((1 : ℝ) / 20) := by
      rw [← Real.rpow_natCast (n ^ ((1 : ℝ) / 40)), ← Real.rpow_mul hn0.le]
      norm_num
    have hsum : n ^ ((1 : ℝ) / 10) * n ^ ((1 : ℝ) / 20) = n ^ ((3 : ℝ) / 20) := by
      rw [← Real.rpow_add hn0]
      norm_num
    calc
      H * (2 * P * H + 1) * P ≤ H * (2 * D * H + 1) * D := by gcongr
      _ ≤ H * (3 * D * H) * D := by gcongr; nlinarith
      _ = 3 * D ^ 2 * H ^ 2 := by ring
      _ ≤ 3 * (CD * n ^ ((1 : ℝ) / 20)) ^ 2 * (CH * n ^ ((1 : ℝ) / 40)) ^ 2 := by
        gcongr
      _ = 3 * CD ^ 2 * CH ^ 2 * ((n ^ ((1 : ℝ) / 20)) ^ 2 * (n ^ ((1 : ℝ) / 40)) ^ 2) := by
        ring
      _ = 3 * CD ^ 2 * CH ^ 2 * n ^ ((3 : ℝ) / 20) := by rw [hsq1, hsq2, hsum]
  have hdiv : n / (T + 1) ≤ n ^ ((3 : ℝ) / 10) := by
    calc
      n / (T + 1) ≤ n / n ^ ((7 : ℝ) / 10) := div_le_div_of_nonneg_left hn0.le hp hT
      _ = n ^ (1 : ℝ) / n ^ ((7 : ℝ) / 10) := by rw [Real.rpow_one]
      _ = n ^ ((3 : ℝ) / 10) := by rw [← Real.rpow_sub hn0]; norm_num
  have hfreq : 4 * n ^ ((3 : ℝ) / 10) + 8 * Real.pi * n / (T + 1) ≤
      (4 + 8 * Real.pi) * n ^ ((3 : ℝ) / 10) := by
    have he : 8 * Real.pi * n / (T + 1) = 8 * Real.pi * (n / (T + 1)) := by ring
    rw [he]
    have hpi := Real.pi_pos
    nlinarith
  have hfreq0 : 0 ≤ 4 * n ^ ((3 : ℝ) / 10) + 8 * Real.pi * n / (T + 1) := by
    have hpi := Real.pi_pos
    have h1 : 0 ≤ n ^ ((3 : ℝ) / 10) := by positivity
    have h2 : 0 ≤ 8 * Real.pi * n / (T + 1) := div_nonneg (by positivity) hT0.le
    linarith
  have hcost0 : 0 ≤ 3 * CD ^ 2 * CH ^ 2 * n ^ ((3 : ℝ) / 20) := by positivity
  calc
    H * (2 * P * H + 1) * P * (4 * n ^ ((3 : ℝ) / 10) + 8 * Real.pi * n / (T + 1)) * M / n ≤
        (3 * CD ^ 2 * CH ^ 2 * n ^ ((3 : ℝ) / 20)) *
          ((4 + 8 * Real.pi) * n ^ ((3 : ℝ) / 10)) * n ^ ((1 : ℝ) / 2) / n := by
      apply div_le_div_of_nonneg_right _ hn0.le
      exact mul_le_mul (mul_le_mul hcost hfreq hfreq0 hcost0) hM hM0
        (mul_nonneg hcost0 (by positivity))
    _ = 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 *
        (n ^ ((3 : ℝ) / 20) * n ^ ((3 : ℝ) / 10) * n ^ ((1 : ℝ) / 2) / n ^ (1 : ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 * n ^ (-(1 : ℝ) / 20) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_sub hn0]
      norm_num

/-- The square root in the minor-arc (Weyl) error, with `X = n^(3/10)` and
`T ≤ 2 n^(7/10)`. -/
lemma twentieth_sqrt (n T M : ℝ) (hn : 1 ≤ n) (hT : 0 < T)
    (hTn : T ≤ 2 * n ^ ((7 : ℝ) / 10)) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    Real.sqrt (5 * M + 32 * M ^ 2 / n ^ ((3 : ℝ) / 10) + (64 * M + 8 * T) * (1 + Real.log T)) ≤
      39 * n ^ ((2 : ℝ) / 5) := by
  have hn0 : 0 < n := by linarith
  have hx : 0 < n ^ ((3 : ℝ) / 10) := Real.rpow_pos_of_pos hn0 _
  have h12 : n ^ ((1 : ℝ) / 2) ≤ n ^ ((7 : ℝ) / 10) := rpow_mono_one hn (by norm_num)
  have h78 : n ^ ((7 : ℝ) / 10) ≤ n ^ ((7 : ℝ) / 8) := rpow_mono_one hn (by norm_num)
  have h745 : n ^ ((7 : ℝ) / 10) ≤ n ^ ((4 : ℝ) / 5) := rpow_mono_one hn (by norm_num)
  have h6145 : n ^ ((61 : ℝ) / 80) ≤ n ^ ((4 : ℝ) / 5) := rpow_mono_one hn (by norm_num)
  have hM45 : M ≤ n ^ ((4 : ℝ) / 5) := hM.trans (h12.trans h745)
  have hs : M ^ 2 / n ^ ((3 : ℝ) / 10) ≤ n ^ ((7 : ℝ) / 10) := by
    calc
      M ^ 2 / n ^ ((3 : ℝ) / 10) ≤ (n ^ ((1 : ℝ) / 2)) ^ 2 / n ^ ((3 : ℝ) / 10) := by gcongr
      _ = n ^ ((7 : ℝ) / 10) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_sub hn0]
        norm_num
  have hlin : 64 * M + 8 * T ≤ 80 * n ^ ((7 : ℝ) / 10) := by nlinarith [hM.trans h12]
  have hlog := kernel_rate_log n T hn hT (by linarith)
  have hprod : (64 * M + 8 * T) * (1 + Real.log T) ≤ 1440 * n ^ ((4 : ℝ) / 5) := by
    calc
      (64 * M + 8 * T) * (1 + Real.log T) ≤ (64 * M + 8 * T) * (18 * n ^ ((1 : ℝ) / 16)) := by
        gcongr
      _ ≤ (80 * n ^ ((7 : ℝ) / 10)) * (18 * n ^ ((1 : ℝ) / 16)) := by gcongr
      _ = 1440 * n ^ ((61 : ℝ) / 80) := by
        rw [mul_mul_mul_comm, ← Real.rpow_add hn0]
        norm_num
      _ ≤ 1440 * n ^ ((4 : ℝ) / 5) := by gcongr
  have hinside : 5 * M + 32 * M ^ 2 / n ^ ((3 : ℝ) / 10) + (64 * M + 8 * T) * (1 + Real.log T) ≤
      1477 * n ^ ((4 : ℝ) / 5) := by
    rw [show 32 * M ^ 2 / n ^ ((3 : ℝ) / 10) = 32 * (M ^ 2 / n ^ ((3 : ℝ) / 10)) by ring]
    linarith [hs.trans h745]
  apply (Real.sqrt_le_left (by positivity)).mpr
  have heq : (39 * n ^ ((2 : ℝ) / 5)) ^ 2 = 1521 * n ^ ((4 : ℝ) / 5) := by
    rw [mul_pow, ← Real.rpow_natCast (n ^ ((2 : ℝ) / 5)), ← Real.rpow_mul hn0.le]
    norm_num
  rw [heq]
  exact hinside.trans (by gcongr; norm_num)

/-- The minor-arc (Weyl) error of the actual kernel at the exponents of
`cor:kernel20`. -/
lemma twentieth_minor (n P D H T M CD CH : ℝ) (hn : 1 ≤ n)
    (hPD : P ≤ D) (hDn : D ≤ CD * n ^ ((1 : ℝ) / 20))
    (hH0 : 0 ≤ H) (hHn : H ≤ CH * n ^ ((1 : ℝ) / 40)) (hCD : 0 ≤ CD) (hCH : 0 ≤ CH)
    (hT : 0 < T) (hTn : T ≤ 2 * n ^ ((7 : ℝ) / 10)) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    (P * H) * (4 * M / n) *
        Real.sqrt (5 * M + 32 * M ^ 2 / n ^ ((3 : ℝ) / 10) + (64 * M + 8 * T) * (1 + Real.log T)) ≤
      156 * CD * CH * n ^ (-(1 : ℝ) / 40) := by
  have hn0 : 0 < n := by linarith
  have hs := twentieth_sqrt n T M hn hT hTn hM0 hM
  have hPH : P * H ≤ CD * CH * n ^ ((3 : ℝ) / 40) := by
    calc
      P * H ≤ D * H := by gcongr
      _ ≤ (CD * n ^ ((1 : ℝ) / 20)) * (CH * n ^ ((1 : ℝ) / 40)) := by
        gcongr
      _ = CD * CH * (n ^ ((1 : ℝ) / 20) * n ^ ((1 : ℝ) / 40)) := by ring
      _ = CD * CH * n ^ ((3 : ℝ) / 40) := by rw [← Real.rpow_add hn0]; norm_num
  calc
    (P * H) * (4 * M / n) *
        Real.sqrt (5 * M + 32 * M ^ 2 / n ^ ((3 : ℝ) / 10) + (64 * M + 8 * T) * (1 + Real.log T)) ≤
        (CD * CH * n ^ ((3 : ℝ) / 40)) * (4 * n ^ ((1 : ℝ) / 2) / n) *
          (39 * n ^ ((2 : ℝ) / 5)) := by gcongr
    _ = 156 * CD * CH * (n ^ ((3 : ℝ) / 40) * n ^ ((1 : ℝ) / 2) * n ^ ((2 : ℝ) / 5) /
        n ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = 156 * CD * CH * n ^ (-(1 : ℝ) / 40) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_sub hn0]
      norm_num

/-- The model-kernel error at the exponents of `cor:kernel20`. -/
lemma twentieth_model (n D H T L CD CH : ℝ) (hn : 1 ≤ n)
    (hDn : D ≤ CD * n ^ ((1 : ℝ) / 20))
    (hH0 : 0 ≤ H) (hHn : H ≤ CH * n ^ ((1 : ℝ) / 40)) (hCD : 0 ≤ CD)
    (hT0 : 0 ≤ T) (hTn : T ≤ 2 * n ^ ((7 : ℝ) / 10)) (hL0 : 0 ≤ L) (hLD : L ≤ 2 * D * H) :
    L ^ 2 * (T * L / n) ≤ 16 * CD ^ 3 * CH ^ 3 * n ^ (-(3 : ℝ) / 40) := by
  have hn0 : 0 < n := by linarith
  have hLn : L ≤ 2 * CD * CH * n ^ ((3 : ℝ) / 40) := by
    calc
      L ≤ 2 * D * H := hLD
      _ ≤ 2 * (CD * n ^ ((1 : ℝ) / 20)) * (CH * n ^ ((1 : ℝ) / 40)) := by
        gcongr
      _ = 2 * CD * CH * (n ^ ((1 : ℝ) / 20) * n ^ ((1 : ℝ) / 40)) := by ring
      _ = 2 * CD * CH * n ^ ((3 : ℝ) / 40) := by rw [← Real.rpow_add hn0]; norm_num
  calc
    L ^ 2 * (T * L / n) ≤ (2 * CD * CH * n ^ ((3 : ℝ) / 40)) ^ 2 *
        ((2 * n ^ ((7 : ℝ) / 10)) * (2 * CD * CH * n ^ ((3 : ℝ) / 40)) / n) := by gcongr
    _ = 16 * CD ^ 3 * CH ^ 3 * ((n ^ ((3 : ℝ) / 40)) ^ 3 * n ^ ((7 : ℝ) / 10) / n ^ (1 : ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = 16 * CD ^ 3 * CH ^ 3 * n ^ (-(3 : ℝ) / 40) := by
      rw [← Real.rpow_natCast (n ^ ((3 : ℝ) / 40)), ← Real.rpow_mul hn0.le,
        ← Real.rpow_add hn0, ← Real.rpow_sub hn0]
      norm_num

/-- `n^(-1/120)` is at most `C_H^(1/3) H^(-1/3)` when `H ≤ C_H n^(1/40)`. -/
lemma twentieth_saving (n H CH : ℝ) (hn : 1 ≤ n) (hH0 : 0 < H) (hCH0 : 0 < CH)
    (hHn : H ≤ CH * n ^ ((1 : ℝ) / 40)) :
    n ^ (-(1 : ℝ) / 120) ≤ CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3) := by
  have hn0 : 0 < n := by linarith
  have hb : (CH * n ^ ((1 : ℝ) / 40)) ^ (-(1 : ℝ) / 3) ≤ H ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hH0 hHn (by norm_num)
  have hsplit : (CH * n ^ ((1 : ℝ) / 40)) ^ (-(1 : ℝ) / 3) =
      CH ^ (-(1 : ℝ) / 3) * n ^ (-(1 : ℝ) / 120) := by
    rw [Real.mul_rpow hCH0.le (by positivity), ← Real.rpow_mul hn0.le]
    norm_num
  have hcancel : CH ^ ((1 : ℝ) / 3) * CH ^ (-(1 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hCH0]
    norm_num
  calc
    n ^ (-(1 : ℝ) / 120) = CH ^ ((1 : ℝ) / 3) * (CH ^ (-(1 : ℝ) / 3) * n ^ (-(1 : ℝ) / 120)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3) := by
      rw [← hsplit]
      exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- The constant of `actual_kernel_rate_twentieth`; it depends only on `C_D` and `C_H`. -/
noncomputable def twentiethRateConstant (CD CH : ℝ) : ℝ :=
  2 ^ 64 + (3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 + 156 * CD * CH + 16 * CD ^ 3 * CH ^ 3) *
    CH ^ ((1 : ℝ) / 3)

lemma twentiethRateConstant_pos (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    0 < twentiethRateConstant CD CH := by
  unfold twentiethRateConstant
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 ≤ CH := by linarith
  have hpi := Real.pi_pos
  have h1 : 0 ≤ 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 + 156 * CD * CH +
      16 * CD ^ 3 * CH ^ 3 := by positivity
  have h2 : 0 ≤ CH ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hCH0 _
  have h3 : (0 : ℝ) < 2 ^ 64 := by norm_num
  nlinarith [mul_nonneg h1 h2]

/-- The four error terms of `actual_kernel_uniform`, with the major-arc threshold
`X = n^(3/10)`, are at most `twentiethRateConstant C_D C_H · H^(-1/3)` at the exponents
of `cor:kernel20`. Here `P` stands for the product of the root primes, `D` for
`rootSquareModulus`, `T` for the Dirichlet parameter, `M` for `⌊√N⌋` and `L` for the
model denominator bound. -/
lemma twentieth_all (n P D H T M L CD CH : ℝ) (hn : 1 ≤ n)
    (hP0 : 0 ≤ P) (hPD : P ≤ D) (hD1 : 1 ≤ D) (hDn : D ≤ CD * n ^ ((1 : ℝ) / 20))
    (hH1 : 1 ≤ H) (hHn : H ≤ CH * n ^ ((1 : ℝ) / 40)) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH)
    (hT : 0 < T) (hTlo : n ^ ((7 : ℝ) / 10) ≤ T + 1) (hTn : T ≤ 2 * n ^ ((7 : ℝ) / 10))
    (hL0 : 0 ≤ L) (hLD : L ≤ 2 * D * H) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    2 ^ 64 * H ^ (-(1 : ℝ) / 3) +
      (H * (2 * P * H + 1) * P) * (4 * n ^ ((3 : ℝ) / 10) + 8 * Real.pi * n / (T + 1)) * M / n +
      (P * H) * (4 * M / n) *
        Real.sqrt (5 * M + 32 * M ^ 2 / n ^ ((3 : ℝ) / 10) + (64 * M + 8 * T) * (1 + Real.log T)) +
      L ^ 2 * (T * L / n) ≤
      twentiethRateConstant CD CH * H ^ (-(1 : ℝ) / 3) := by
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 ≤ CH := by linarith
  have h1 := twentieth_major n P D H T M CD CH hn hP0 hPD hD1 hDn hH1 hHn hTlo hM0 hM
  have h2 := twentieth_minor n P D H T M CD CH hn hPD hDn (by linarith) hHn hCD0 hCH0
    hT hTn hM0 hM
  have h3 := twentieth_model n D H T L CD CH hn hDn (by linarith) hHn hCD0 hT.le hTn hL0 hLD
  have hw := twentieth_saving n H CH hn (by linarith) (by linarith) hHn
  have e1 : n ^ (-(1 : ℝ) / 20) ≤ n ^ (-(1 : ℝ) / 120) := rpow_mono_one hn (by norm_num)
  have e2 : n ^ (-(1 : ℝ) / 40) ≤ n ^ (-(1 : ℝ) / 120) := rpow_mono_one hn (by norm_num)
  have e3 : n ^ (-(3 : ℝ) / 40) ≤ n ^ (-(1 : ℝ) / 120) := rpow_mono_one hn (by norm_num)
  have hpi := Real.pi_pos
  have hA1 : 0 ≤ 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 := by positivity
  have hA2 : 0 ≤ 156 * CD * CH := by positivity
  have hA3 : 0 ≤ 16 * CD ^ 3 * CH ^ 3 := by positivity
  have k1 := mul_le_mul_of_nonneg_left (e1.trans hw) hA1
  have k2 := mul_le_mul_of_nonneg_left (e2.trans hw) hA2
  have k3 := mul_le_mul_of_nonneg_left (e3.trans hw) hA3
  have hfinal : twentiethRateConstant CD CH * H ^ (-(1 : ℝ) / 3) =
      2 ^ 64 * H ^ (-(1 : ℝ) / 3) +
        3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 * (CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3)) +
        156 * CD * CH * (CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3)) +
        16 * CD ^ 3 * CH ^ 3 * (CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3)) := by
    unfold twentiethRateConstant
    ring
  rw [hfinal]
  linarith

/-- The threshold of `actual_kernel_rate_twentieth`: `N₀ = ⌈K^40⌉` with
`K = max 8 (4 C_D C_H)`, so that `N^(1/40) ≥ K` for `N ≥ N₀`. -/
noncomputable def twentiethThreshold (CD CH : ℝ) : ℕ := ⌈(max 8 (4 * CD * CH)) ^ 40⌉₊

/-- **Uniform kernel approximation at `β = κ = 1/20`** (paper: `lem:record:K20-approx`
at the exponents of `cor:kernel20`, the analytic input of `prop:record:kernel20`).

Fix `C_D, C_H ≥ 1`. There are `C > 0` and `N₀`, depending only on `C_D` and `C_H`, such
that for every `N ≥ N₀`, every injective finite family `p` of primes with root primes
`R` and root classes `c` (with `2` among the root primes, root class `1` at `2` and
nonzero root classes at the odd root primes), every cutoff
`C_H⁻¹ N^(1/40) ≤ H ≤ C_H N^(1/40)`, root modulus `D = rootSquareModulus p R ≤ C_D N^(1/20)`,
and every family containing all primes of every denominator up to `N^(3/10)`, the
actual-square transform `S` (`actualSquareTransform`, square roots up to `⌊√N⌋`) and the
model transform `S₀` (`actualModelTransform`, centres of denominator at most `⌈D H⌉`)
satisfy `‖S(α) - S₀(α)‖ ≤ C H^(-1/3)` for every real `α`.

The constant is `twentiethRateConstant C_D C_H` and the threshold is
`twentiethThreshold C_D C_H`. The covering hypothesis on the prime family is the
upstream `hcover` hypothesis at the major-arc threshold `N^(3/10)` used in this proof;
it holds, for instance, when the family contains all primes up to `N`. -/
theorem actual_kernel_rate_twentieth (CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ {I : Type} [Fintype I] [DecidableEq I] (p : I → ℕ) [∀ i, Fact (p i).Prime]
        (R : Finset I) (c : ∀ i, ZMod (p i)), Function.Injective p →
      ∀ H : ℝ, CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) ≤ H → H ≤ CH * (N : ℝ) ^ ((1 : ℝ) / 40) →
      (rootSquareModulus p R : ℝ) ≤ CD * (N : ℝ) ^ ((1 : ℝ) / 20) →
      (∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 10) → b.den ∣ ∏ i, primaryModulus b.den (p i)) →
      (∀ i, p i = 2 → i ∈ R) →
      (∀ i ∈ R, if p i = 2 then c i = 1 else c i ≠ 0) →
      ∀ α : ℝ, ‖actualSquareTransform p R c H N.sqrt N α -
        actualModelTransform p R c H ⌈(rootSquareModulus p R : ℝ) * H⌉₊ N α‖ ≤
          C * H ^ (-(1 : ℝ) / 3) := by
  refine ⟨twentiethRateConstant CD CH, twentiethRateConstant_pos CD CH hCD hCH,
    twentiethThreshold CD CH, ?_⟩
  intro N hN I _ _ p _ R c hinj H hHlo hHhi hD hcover htwo hc α
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 < CH := by linarith
  -- the scale `n = N`
  have hK8 : (8 : ℝ) ≤ max 8 (4 * CD * CH) := le_max_left _ _
  have hK4 : 4 * CD * CH ≤ max 8 (4 * CD * CH) := le_max_right _ _
  have hK0 : 0 < max 8 (4 * CD * CH) := by linarith
  have hnK : (max 8 (4 * CD * CH)) ^ 40 ≤ (N : ℝ) := by
    have h : ((twentiethThreshold CD CH : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact (Nat.le_ceil _).trans h
  have hn1 : (1 : ℝ) ≤ N := by
    have : (1 : ℝ) ≤ (max 8 (4 * CD * CH)) ^ 40 := one_le_pow₀ (by linarith)
    linarith
  have hn0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hn1
  have hroot : max 8 (4 * CD * CH) ≤ (N : ℝ) ^ ((1 : ℝ) / 40) := by
    have h := Real.rpow_le_rpow (by positivity) hnK (by norm_num : (0 : ℝ) ≤ 1 / 40)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le] at h
    norm_num at h
    exact max_le h.1 h.2
  have hpow : ∀ e : ℝ, (1 : ℝ) / 40 ≤ e → max 8 (4 * CD * CH) ≤ (N : ℝ) ^ e :=
    fun e he => hroot.trans (rpow_mono_one hn1 he)
  -- the cutoff
  have hH1 : 1 ≤ H := by
    have h1 : CH⁻¹ * (4 * CD * CH) ≤ CH⁻¹ * (N : ℝ) ^ ((1 : ℝ) / 40) :=
      mul_le_mul_of_nonneg_left (hK4.trans hroot) (inv_nonneg.mpr hCH0.le)
    have h2 : CH⁻¹ * (4 * CD * CH) = 4 * CD := by field_simp
    linarith
  have hH0 : 0 < H := by linarith
  -- the root modulus
  have hD1 : (1 : ℝ) ≤ (rootSquareModulus p R : ℝ) := by
    exact_mod_cast rootSquareModulus_pos p R
  have hP0 : (0 : ℝ) ≤ ((∏ i ∈ R, p i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hPD : ((∏ i ∈ R, p i : ℕ) : ℝ) ≤ (rootSquareModulus p R : ℝ) := by
    exact_mod_cast rootProduct_le_squareModulus p R
  have hDH : 1 ≤ (rootSquareModulus p R : ℝ) * H := by nlinarith
  have hDHn : (rootSquareModulus p R : ℝ) * H ≤ CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40) := by
    calc
      (rootSquareModulus p R : ℝ) * H ≤
          (CD * (N : ℝ) ^ ((1 : ℝ) / 20)) * (CH * (N : ℝ) ^ ((1 : ℝ) / 40)) := by
        gcongr
      _ = CD * CH * ((N : ℝ) ^ ((1 : ℝ) / 20) * (N : ℝ) ^ ((1 : ℝ) / 40)) := by ring
      _ = CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40) := by rw [← Real.rpow_add hn0]; norm_num
  -- the model denominator bound `L = ⌈D H⌉`
  have hLD : (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ) ≤ 2 * (rootSquareModulus p R : ℝ) * H := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (rootSquareModulus p R : ℝ) * H by linarith)
    linarith
  have hmodel : (rootSquareModulus p R : ℝ) * H ≤ (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ) :=
    Nat.le_ceil _
  -- the Dirichlet parameter `T = ⌈N^(7/10)⌉`
  have hp7 : 0 < (N : ℝ) ^ ((7 : ℝ) / 10) := Real.rpow_pos_of_pos hn0 _
  have hT : 0 < ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := Nat.ceil_pos.mpr hp7
  have hTlo : (N : ℝ) ^ ((7 : ℝ) / 10) ≤ (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) := Nat.le_ceil _
  have hThi : (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ ((7 : ℝ) / 10) := by
    have h := Nat.ceil_lt_add_one hp7.le
    have h1 : 1 ≤ (N : ℝ) ^ ((7 : ℝ) / 10) := Real.one_le_rpow hn1 (by norm_num)
    linarith
  -- `2 L ≤ T + 1`
  have hLT : 2 * ⌈(rootSquareModulus p R : ℝ) * H⌉₊ ≤ ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ + 1 := by
    have h1 : 2 * (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 10) := by
      calc
        2 * (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ) ≤ 4 * ((rootSquareModulus p R : ℝ) * H) := by
          linarith
        _ ≤ 4 * (CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40)) := by gcongr
        _ = (4 * CD * CH) * (N : ℝ) ^ ((3 : ℝ) / 40) := by ring
        _ ≤ (N : ℝ) ^ ((5 : ℝ) / 8) * (N : ℝ) ^ ((3 : ℝ) / 40) := by
          gcongr
          exact hK4.trans (hpow _ (by norm_num))
        _ = (N : ℝ) ^ ((7 : ℝ) / 10) := by rw [← Real.rpow_add hn0]; norm_num
    have h2 : ((2 * ⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℕ) : ℝ) ≤
        (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) := by
      push_cast
      linarith
    have h3 : 2 * ⌈(rootSquareModulus p R : ℝ) * H⌉₊ ≤ ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ := by
      exact_mod_cast h2
    omega
  -- the major-arc threshold `X = N^(3/10)`
  have hX : (8 : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 10) := hK8.trans (hpow _ (by norm_num))
  have hLX : (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 10) := by
    have h9 := hpow ((9 : ℝ) / 40) (by norm_num)
    have hK2 : 2 * CD * CH ≤ (N : ℝ) ^ ((9 : ℝ) / 40) := by nlinarith
    calc
      (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ) ≤ 2 * ((rootSquareModulus p R : ℝ) * H) := by
        linarith
      _ ≤ 2 * (CD * CH * (N : ℝ) ^ ((3 : ℝ) / 40)) := by gcongr
      _ = (2 * CD * CH) * (N : ℝ) ^ ((3 : ℝ) / 40) := by ring
      _ ≤ (N : ℝ) ^ ((9 : ℝ) / 40) * (N : ℝ) ^ ((3 : ℝ) / 40) := by gcongr
      _ = (N : ℝ) ^ ((3 : ℝ) / 10) := by rw [← Real.rpow_add hn0]; norm_num
  -- the square-root length `M = ⌊√N⌋`
  obtain ⟨hM, hlo, hhi, hMn⟩ := natural_sqrt_bounds N hN1
  have hk := actual_kernel_uniform p R c hinj H hH0 ⌈(rootSquareModulus p R : ℝ) * H⌉₊
    ⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ ((N : ℝ) ^ ((3 : ℝ) / 10)) hT hLT hX hLX hmodel hcover htwo hc
    N.sqrt N hM hlo hhi α
  refine hk.trans ?_
  exact twentieth_all (N : ℝ) ((∏ i ∈ R, p i : ℕ) : ℝ) (rootSquareModulus p R : ℝ) H
    (⌈(N : ℝ) ^ ((7 : ℝ) / 10)⌉₊ : ℝ) (N.sqrt : ℝ) (⌈(rootSquareModulus p R : ℝ) * H⌉₊ : ℝ)
    CD CH hn1 hP0 hPD hD1 hD hH1 hHhi hCD hCH (by exact_mod_cast hT)
    (by linarith) hThi (Nat.cast_nonneg _) hLD (Nat.cast_nonneg _) hMn

end Kernel

end Sarkozy
