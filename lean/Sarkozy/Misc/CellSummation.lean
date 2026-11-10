module

public import Sarkozy.Target
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

/-!
# Partial summation over the primes `p ≡ 3 (mod 4)` of a sequence of cells

`paper/sections/20_middle_reference.tex`, the analytic step ("Partial summation") of the proof of
`lem:record:block-charge`(i) (`eq:record:cell-charge`), which is also the step of
`lem:record:lower-start-sums`(i).

For cell points `x_0 < x_1 < … < x_𝗇` (here any nondecreasing sequence with `x_0 > 1`), weights
`g_j ≥ 0`, an exponent `s ≥ 0` and a constant `e` with `|θ(t; 4, 3) - t/2| ≤ e t` on `[x_0, x_𝗇]`,
put `f_s(t) = t^{-s} / log t` and `I_j(s) = ∫_{x_j}^{x_{j+1}} f_s`. Then
`|∑_j g_j ∑_{p ∈ [x_j, x_{j+1}), p ≡ 3 (4)} p^{-s} - ½ ∑_j g_j I_j(s)|` is at most
`e [∑_j g_j I_j(s) + 2 g_0 x_0^{1-s}/log x_0 + 2 ∑_{0<j<𝗇} (g_j - g_{j-1})_+ x_j^{1-s}/log x_j]`
(`cells_partial_summation`), which gives the upper bound with `½ + e` (`cells_sum_upper`) and the
lower bound with `½ - e` (`cells_sum_lower`).

The proof is the paper's: Abel summation in each cell (mathlib's
`sum_mul_eq_sub_sub_integral_mul`, with `c(k) = log k` on primes `k ≡ 3 (mod 4)`, whose partial sums
are `θ(t; 4, 3)`), the splitting `θ = t/2 + η`, integration by parts
`∫ t f_s' = [t f_s] - ∫ f_s`, and
the telescoping of the endpoint terms of consecutive cells (`sum_range_mul_sub`), which leaves the
first-cell term `2 e g_0 x_0 f_s(x_0)` and the jump terms `2 e (g_j - g_{j-1})_+ x_j f_s(x_j)`.

**Endpoints.** The paper takes `x`, `Y` even, so that no cell endpoint is a prime `≡ 3 (mod 4)`;
here
this is the hypothesis `NotPrime3 (x j)` for `0 ≤ j ≤ 𝗇` (it is what the proof uses: it makes the
half-open cells `[x_j, x_{j+1})` agree with Abel's `(x_j, x_{j+1}]`).

The error constant `e` is a hypothesis of the general statement; it is supplied by `thm:bmor`
(`Target.BMOR`) above `X_Ch` and by `Target.ThetaSmall`/`Target.ThetaSmallTable` below `10¹⁰`
(`Sarkozy.Misc.BlockCharge`).
-/

open Finset MeasureTheory intervalIntegral

namespace Sarkozy.Misc

/-! ## The weight and `θ(t; 4, 3)` -/

/-- The weight `c(k) = log k` at the primes `k ≡ 3 (mod 4)`, zero elsewhere. -/
noncomputable def c3 (k : ℕ) : ℝ := if k.Prime ∧ k % 4 = 3 then Real.log k else 0

theorem range_succ_eq_Icc_zero (m : ℕ) : range (m + 1) = Icc 0 m := by
  ext k
  simp only [mem_range, mem_Icc, Nat.zero_le, true_and]
  omega

/-- `θ(t; 4, 3) = ∑_{k ≤ t} c(k)`. -/
theorem theta4_three_eq (t : ℝ) : Target.theta4 t 3 = ∑ k ∈ Icc 0 ⌊t⌋₊, c3 k := by
  unfold Target.theta4 c3
  rw [Finset.sum_filter, range_succ_eq_Icc_zero]

/-- `η(t) = θ(t; 4, 3) - t/2`. -/
noncomputable def eta3 (t : ℝ) : ℝ := Target.theta4 t 3 - t / 2

/-! ## The function `f_s(t) = t^{-s} / log t` -/

/-- `f_s(t) = t^{-s} / log t`. -/
noncomputable def fs (s t : ℝ) : ℝ := t ^ (-s) / Real.log t

/-- The derivative of `f_s` on `(1, ∞)`. -/
noncomputable def fsDeriv (s t : ℝ) : ℝ :=
  ((-s) * t ^ (-s - 1) * Real.log t - t ^ (-s) * t⁻¹) / Real.log t ^ 2

theorem hasDerivAt_fs (s : ℝ) {t : ℝ} (ht : 1 < t) : HasDerivAt (fs s) (fsDeriv s t) t := by
  have h0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h1 := Real.hasDerivAt_rpow_const (p := -s) (Or.inl h0)
  have h2 := Real.hasDerivAt_log h0
  exact h1.div h2 hlog

theorem fs_pos {s t : ℝ} (ht : 1 < t) : 0 < fs s t :=
  div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos ht)

theorem fsDeriv_neg {s t : ℝ} (hs : 0 ≤ s) (ht : 1 < t) : fsDeriv s t < 0 := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_pos ht
  unfold fsDeriv
  apply div_neg_of_neg_of_pos _ (by positivity)
  have h1 : 0 ≤ s * t ^ (-s - 1) * Real.log t := by positivity
  have h2 : 0 < t ^ (-s) * t⁻¹ := by positivity
  nlinarith

theorem continuousOn_fsDeriv (s : ℝ) {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fsDeriv s) (Set.Icc a b) := by
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
  have h0 : t ≠ 0 := by linarith
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  apply ContinuousAt.continuousWithinAt
  unfold fsDeriv
  refine ContinuousAt.div ?_ ?_ ?_
  · apply ContinuousAt.sub
    · exact (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl h0))).mul
        (Real.continuousAt_log h0)
    · exact (Real.continuousAt_rpow_const _ _ (Or.inl h0)).mul (continuousAt_inv₀ h0)
  · exact (Real.continuousAt_log h0).pow 2
  · exact pow_ne_zero 2 hlog

theorem continuousOn_fs (s : ℝ) {a b : ℝ} (ha : 1 < a) : ContinuousOn (fs s) (Set.Icc a b) :=
  fun _t ht => (hasDerivAt_fs s (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt

/-- `x f_s(x) = x^{1-s} / log x`. -/
theorem mul_fs {s t : ℝ} (ht : 0 < t) : t * fs s t = t ^ (1 - s) / Real.log t := by
  unfold fs
  rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_one, mul_div_assoc]

/-! ## One cell -/

/-- Abel summation on one cell `(a, b]`. -/
theorem cell_abel {s a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, fs s k * c3 k =
      fs s b * Target.theta4 b 3 - fs s a * Target.theta4 a 3 -
        ∫ t in a..b, fsDeriv s t * Target.theta4 t 3 := by
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fs s) t := fun t ht =>
    (hasDerivAt_fs s (lt_of_lt_of_le ha ht.1)).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc a b, deriv (fs s) t = fsDeriv s t := fun t ht =>
    (hasDerivAt_fs s (lt_of_lt_of_le ha ht.1)).deriv
  have hint : IntegrableOn (deriv (fs s)) (Set.Icc a b) :=
    ((continuousOn_fsDeriv s ha).integrableOn_Icc).congr_fun
      (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  rw [sum_mul_eq_sub_sub_integral_mul c3 (by linarith) hab hdiff hint, theta4_three_eq,
    theta4_three_eq, integral_of_le hab]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp only
  rw [hderiv t (Set.Ioc_subset_Icc_self ht), theta4_three_eq]

/-- Integration by parts: `∫_a^b t f_s'(t) dt = b f_s(b) - a f_s(a) - ∫_a^b f_s`. -/
theorem integral_mul_fsDeriv {s a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, t * fsDeriv s t = b * fs s b - a * fs s a - ∫ t in a..b, fs s t := by
  have hu : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => t) 1 t := fun t _ => hasDerivAt_id t
  have hv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fs s) (fsDeriv s t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_fs s (lt_of_lt_of_le ha ht.1)
  have h := integral_mul_deriv_eq_deriv_mul hu hv intervalIntegrable_const
    ((continuousOn_fsDeriv s ha).intervalIntegrable_of_Icc hab)
  simpa only [one_mul] using h

/-- **One cell, main term and error**: `∑_{p ∈ (a, b], p ≡ 3 (4)} f_s(p) log p
= ½ ∫_a^b f_s + f_s(b) η(b) - f_s(a) η(a) - ∫_a^b f_s' η`. -/
theorem cell_main_error {s a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, fs s k * c3 k =
      1 / 2 * (∫ t in a..b, fs s t) + (fs s b * eta3 b - fs s a * eta3 a) -
        ∫ t in a..b, fsDeriv s t * eta3 t := by
  have hcont := continuousOn_fsDeriv s (b := b) ha
  have hθint : IntervalIntegrable (fun t => fsDeriv s t * Target.theta4 t 3) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have h := integrableOn_mul_sum_Icc c3 (m := 0) (by linarith : (0 : ℝ) ≤ a)
      hcont.integrableOn_Icc
    refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
    simp only [theta4_three_eq]
  have hlin : IntervalIntegrable (fun t => fsDeriv s t * (t / 2)) volume a b :=
    (hcont.mul (continuousOn_id.div_const 2)).intervalIntegrable_of_Icc hab
  have heta : (fun t => fsDeriv s t * eta3 t) =
      fun t => fsDeriv s t * Target.theta4 t 3 - fsDeriv s t * (t / 2) := by
    funext t
    unfold eta3
    ring
  have hsplit : ∫ t in a..b, fsDeriv s t * Target.theta4 t 3 =
      (∫ t in a..b, fsDeriv s t * (t / 2)) + ∫ t in a..b, fsDeriv s t * eta3 t := by
    rw [heta, integral_sub hθint hlin]
    ring
  have hhalf : ∫ t in a..b, fsDeriv s t * (t / 2) = 1 / 2 * ∫ t in a..b, t * fsDeriv s t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  rw [cell_abel ha hab, hsplit, hhalf, integral_mul_fsDeriv ha hab]
  unfold eta3
  ring

/-- **One cell, the error bound**: if `|η| ≤ e t` on `[a, b]`, then
`|∫_a^b f_s' η| ≤ e (a f_s(a) - b f_s(b) + ∫_a^b f_s)`. -/
theorem cell_error_le {s a b e : ℝ} (hs : 0 ≤ s) (ha : 1 < a) (hab : a ≤ b)
    (hθ : ∀ t ∈ Set.Icc a b, |eta3 t| ≤ e * t) :
    |∫ t in a..b, fsDeriv s t * eta3 t| ≤ e * (a * fs s a - b * fs s b + ∫ t in a..b, fs s t) := by
  have hcont := continuousOn_fsDeriv s (b := b) ha
  have hg : IntervalIntegrable (fun t => e * (t * -fsDeriv s t)) volume a b :=
    (continuousOn_const.mul (continuousOn_id.mul hcont.neg)).intervalIntegrable_of_Icc hab
  have h := norm_integral_le_of_norm_le (f := fun t => fsDeriv s t * eta3 t) hab
    (Filter.Eventually.of_forall fun t ht => by
      have ht1 : 1 < t := lt_trans ha ht.1
      have hd := fsDeriv_neg hs ht1
      rw [Real.norm_eq_abs, abs_mul, abs_of_neg hd]
      have := hθ t (Set.Ioc_subset_Icc_self ht)
      have : -fsDeriv s t * |eta3 t| ≤ -fsDeriv s t * (e * t) :=
        mul_le_mul_of_nonneg_left this (by linarith)
      linarith) hg
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  have hint : ∫ t in a..b, e * (t * -fsDeriv s t) = -(e * ∫ t in a..b, t * fsDeriv s t) := by
    rw [intervalIntegral.integral_const_mul, ← mul_neg, ← intervalIntegral.integral_neg]
    congr 1
    congr 1
    funext t
    ring
  rw [hint, integral_mul_fsDeriv ha hab]
  ring

/-! ## Summation by parts and the telescoping over the cells -/

/-- Summation by parts: `∑_{j<𝗇} g_j (V_{j+1} - V_j)
= g_{𝗇-1} V_𝗇 - g_0 V_0 - ∑_{0<j<𝗇} (g_j - g_{j-1}) V_j`. -/
theorem sum_range_mul_sub (g V : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ range n, g j * (V (j + 1) - V j) =
      g (n - 1) * V n - g 0 * V 0 - ∑ j ∈ Ico 1 n, (g j - g (j - 1)) * V j := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [zero_add, range_one, sum_singleton, Nat.sub_self, Ico_self, sum_empty]
      ring
    · rw [sum_range_succ, ih hm, Finset.sum_Ico_succ_top hm]
      simp only [Nat.add_sub_cancel]
      ring

theorem abs_add_self_eq (d : ℝ) : |d| + d = 2 * max d 0 := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h, max_eq_left h]
    ring
  · rw [abs_of_nonpos h, max_eq_right h]
    ring

/-- A nondecreasing chain `x_0 ≤ x_1 ≤ … ≤ x_𝗇`: `x_i ≤ x_j` for `i ≤ j ≤ 𝗇`. -/
theorem chain_le {x : ℕ → ℝ} {n : ℕ} (hmono : ∀ j < n, x j ≤ x (j + 1)) {i j : ℕ} (hij : i ≤ j)
    (hjn : j ≤ n) : x i ≤ x j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (hmono k (by omega))
    · have : i = k + 1 := by omega
      subst this
      exact le_rfl

/-- **Partial summation over a sequence of cells** (`lem:record:block-charge`(i), the analytic step
of its proof; `lem:record:lower-start-sums`(i)). The sums are over `(x_j, x_{j+1}]`, weighted by
`c(k) f_s(k)`, which is `p^{-s}` at a prime `p ≡ 3 (mod 4)` (`sum_Ioc_fs_c3`). -/
theorem cells_partial_summation {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx0 : 1 < x 0)
    (hmono : ∀ j < n, x j ≤ x (j + 1)) (g : ℕ → ℝ) (hg : ∀ j < n, 0 ≤ g j) {s e : ℝ}
    (hs : 0 ≤ s) (hθ : ∀ t, x 0 ≤ t → t ≤ x n → |eta3 t| ≤ e * t) :
    |∑ j ∈ range n, g j * ∑ k ∈ Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊, fs s k * c3 k -
        1 / 2 * ∑ j ∈ range n, g j * ∫ t in x j..x (j + 1), fs s t| ≤
      e * (∑ j ∈ range n, g j * (∫ t in x j..x (j + 1), fs s t) + 2 * g 0 * (x 0 * fs s (x 0)) +
        2 * ∑ j ∈ Ico 1 n, max (g j - g (j - 1)) 0 * (x j * fs s (x j))) := by
  -- the points are increasing from `x 0`
  have hle0 : ∀ j ≤ n, x 0 ≤ x j := fun j hj => chain_le hmono (Nat.zero_le j) hj
  have hlen : ∀ j ≤ n, x j ≤ x n := fun j hj => chain_le hmono hj le_rfl
  have hx1 : ∀ j ≤ n, 1 < x j := fun j hj => lt_of_lt_of_le hx0 (hle0 j hj)
  set A : ℕ → ℝ := fun j => x j * fs s (x j) with hA
  set V : ℕ → ℝ := fun j => fs s (x j) * eta3 (x j) with hV
  set K : ℕ → ℝ := fun j => ∫ t in x j..x (j + 1), fsDeriv s t * eta3 t with hK
  set I : ℕ → ℝ := fun j => ∫ t in x j..x (j + 1), fs s t with hI
  -- per cell
  have hcell : ∀ j < n, ∑ k ∈ Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊, fs s k * c3 k =
      1 / 2 * I j + (V (j + 1) - V j) - K j := fun j hj =>
    cell_main_error (hx1 j hj.le) (hmono j hj)
  have hVle : ∀ j ≤ n, |V j| ≤ e * A j := by
    intro j hj
    simp only [hV, hA]
    rw [abs_mul, abs_of_pos (fs_pos (hx1 j hj))]
    have := hθ (x j) (hle0 j hj) (hlen j hj)
    have h' := mul_le_mul_of_nonneg_left this (fs_pos (s := s) (hx1 j hj)).le
    linarith
  have hKle : ∀ j < n, |K j| ≤ e * (A j - A (j + 1) + I j) := by
    intro j hj
    exact cell_error_le hs (hx1 j hj.le) (hmono j hj) fun t ht =>
      hθ t ((hle0 j hj.le).trans ht.1) (ht.2.trans (hlen (j + 1) hj))
  -- the difference
  have hD : ∑ j ∈ range n, g j * ∑ k ∈ Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊, fs s k * c3 k -
      1 / 2 * ∑ j ∈ range n, g j * I j =
      (g (n - 1) * V n - g 0 * V 0 - ∑ j ∈ Ico 1 n, (g j - g (j - 1)) * V j) -
        ∑ j ∈ range n, g j * K j := by
    rw [← sum_range_mul_sub g V hn, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcell j (mem_range.mp hj)]
    ring
  have hA' : ∑ j ∈ range n, g j * (A j - A (j + 1)) =
      g 0 * A 0 - g (n - 1) * A n + ∑ j ∈ Ico 1 n, (g j - g (j - 1)) * A j := by
    have h := sum_range_mul_sub g A hn
    have e1 : ∑ j ∈ range n, g j * (A j - A (j + 1)) = -∑ j ∈ range n, g j * (A (j + 1) - A j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e1, h]
    ring
  have hgn : 0 ≤ g (n - 1) := hg (n - 1) (by omega)
  have hg0 : 0 ≤ g 0 := hg 0 (by omega)
  -- bound the three pieces
  have hb1 : |∑ j ∈ Ico 1 n, (g j - g (j - 1)) * V j| ≤
      ∑ j ∈ Ico 1 n, |g j - g (j - 1)| * (e * A j) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hVle j (mem_Ico.mp hj).2.le) (abs_nonneg _)
  have hb2 : |∑ j ∈ range n, g j * K j| ≤ ∑ j ∈ range n, g j * (e * (A j - A (j + 1) + I j)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hj' := mem_range.mp hj
    rw [abs_mul, abs_of_nonneg (hg j hj')]
    exact mul_le_mul_of_nonneg_left (hKle j hj') (hg j hj')
  have hb3 : |g (n - 1) * V n| ≤ g (n - 1) * (e * A n) := by
    rw [abs_mul, abs_of_nonneg hgn]
    exact mul_le_mul_of_nonneg_left (hVle n le_rfl) hgn
  have hb4 : |g 0 * V 0| ≤ g 0 * (e * A 0) := by
    rw [abs_mul, abs_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_left (hVle 0 (by omega)) hg0
  -- the sum of the bounds
  have hsum2 : ∑ j ∈ range n, g j * (e * (A j - A (j + 1) + I j)) =
      e * (∑ j ∈ range n, g j * (A j - A (j + 1))) + e * ∑ j ∈ range n, g j * I j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsum1 : ∑ j ∈ Ico 1 n, |g j - g (j - 1)| * (e * A j) +
      e * ∑ j ∈ Ico 1 n, (g j - g (j - 1)) * A j =
      e * (2 * ∑ j ∈ Ico 1 n, max (g j - g (j - 1)) 0 * A j) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have := abs_add_self_eq (g j - g (j - 1))
    linear_combination (e * A j) * this
  rw [hD]
  have htri : |(g (n - 1) * V n - g 0 * V 0 - ∑ j ∈ Ico 1 n, (g j - g (j - 1)) * V j) -
      ∑ j ∈ range n, g j * K j| ≤ |g (n - 1) * V n| + |g 0 * V 0| +
        |∑ j ∈ Ico 1 n, (g j - g (j - 1)) * V j| + |∑ j ∈ range n, g j * K j| := by
    have h1 := abs_sub (g (n - 1) * V n - g 0 * V 0 - ∑ j ∈ Ico 1 n, (g j - g (j - 1)) * V j)
      (∑ j ∈ range n, g j * K j)
    have h2 := abs_sub (g (n - 1) * V n - g 0 * V 0) (∑ j ∈ Ico 1 n, (g j - g (j - 1)) * V j)
    have h3 := abs_sub (g (n - 1) * V n) (g 0 * V 0)
    linarith
  refine htri.trans ?_
  rw [hA'] at hsum2
  nlinarith [hb1, hb2, hb3, hb4, hsum1, hsum2]

/-! ## The cells `[x_j, x_{j+1})` and the statements of `eq:record:cell-charge` type -/

/-- The primes `p ≡ 3 (mod 4)` of the cell `[a, b)`. -/
noncomputable def cellPrimes (a b : ℝ) : Finset ℕ :=
  (range ⌈b⌉₊).filter fun p => p.Prime ∧ p % 4 = 3 ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b

theorem mem_cellPrimes {a b : ℝ} {p : ℕ} :
    p ∈ cellPrimes a b ↔ p.Prime ∧ p % 4 = 3 ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b := by
  unfold cellPrimes
  rw [mem_filter, mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro h
    exact ⟨Nat.lt_ceil.mpr h.2.2.2, h⟩

/-- `a` is not a prime `≡ 3 (mod 4)` (the paper ensures this for every cell endpoint by taking
`x`, `Y` even). -/
def NotPrime3 (a : ℝ) : Prop := ∀ p : ℕ, p.Prime → p % 4 = 3 → (p : ℝ) ≠ a

/-- An even number is not a prime `≡ 3 (mod 4)`. -/
theorem notPrime3_of_even {m : ℕ} (hm : Even m) : NotPrime3 (m : ℝ) := by
  intro p _ h3 hpm
  have hpm' : p = m := by exact_mod_cast hpm
  subst hpm'
  obtain ⟨r, hr⟩ := hm
  omega

/-- The weighted Abel sum of a cell is the sum of `p^{-s}` over its primes `p ≡ 3 (mod 4)`, when
the endpoints are not such primes. -/
theorem sum_Ioc_fs_c3 {s a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hna : NotPrime3 a)
    (hnb : NotPrime3 b) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, fs s k * c3 k = ∑ p ∈ cellPrimes a b, (p : ℝ) ^ (-s) := by
  have hterm : ∀ k : ℕ, fs s k * c3 k = if k.Prime ∧ k % 4 = 3 then (k : ℝ) ^ (-s) else 0 := by
    intro k
    unfold fs c3
    split_ifs with h
    · have hk : (1 : ℝ) < k := by exact_mod_cast h.1.one_lt
      exact div_mul_cancel₀ _ (Real.log_pos hk).ne'
    · ring
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  rw [mem_filter, mem_Ioc, mem_cellPrimes, Nat.floor_lt ha, Nat.le_floor_iff hb]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp, h3⟩
    exact ⟨hp, h3, h1.le, lt_of_le_of_ne h2 (hnb p hp h3)⟩
  · rintro ⟨hp, h3, h1, h2⟩
    exact ⟨⟨lt_of_le_of_ne h1 (Ne.symm (hna p hp h3)), h2.le⟩, hp, h3⟩

/-- `I_j(s) = ∫_{x_j}^{x_{j+1}} t^{-s}/log t dt`. -/
noncomputable def cellIntegral (s a b : ℝ) : ℝ := ∫ t in a..b, fs s t

/-- The error functional of `eq:record:cell-charge`, divided by `e`:
`2 g_0 x_0^{1-s}/log x_0 + 2 ∑_{0<j<𝗇} (g_j - g_{j-1})_+ x_j^{1-s}/log x_j`. -/
noncomputable def cellEdge (n : ℕ) (x g : ℕ → ℝ) (s : ℝ) : ℝ :=
  2 * g 0 * (x 0 ^ (1 - s) / Real.log (x 0)) +
    2 * ∑ j ∈ Ico 1 n, max (g j - g (j - 1)) 0 * (x j ^ (1 - s) / Real.log (x j))

/-- **The partial summation of `lem:record:block-charge`(i), in terms of the cells**: for cell
points `x_0 ≤ … ≤ x_𝗇` with `x_0 > 1`, none a prime `≡ 3 (mod 4)`, weights `g_j ≥ 0`, `s ≥ 0`, and
`|θ(t; 4, 3) - t/2| ≤ e t` on `[x_0, x_𝗇]`,
`|∑_j g_j ∑_{p ∈ [x_j, x_{j+1})} p^{-s} - ½ ∑_j g_j I_j(s)| ≤ e (∑_j g_j I_j(s) + edge terms)`. -/
theorem cells_prime_sum_abs {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx0 : 1 < x 0)
    (hmono : ∀ j < n, x j ≤ x (j + 1)) (hend : ∀ j ≤ n, NotPrime3 (x j)) (g : ℕ → ℝ)
    (hg : ∀ j < n, 0 ≤ g j) {s e : ℝ} (hs : 0 ≤ s)
    (hθ : ∀ t, x 0 ≤ t → t ≤ x n → |Target.theta4 t 3 - t / 2| ≤ e * t) :
    |∑ j ∈ range n, g j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-s) -
        1 / 2 * ∑ j ∈ range n, g j * cellIntegral s (x j) (x (j + 1))| ≤
      e * (∑ j ∈ range n, g j * cellIntegral s (x j) (x (j + 1)) + cellEdge n x g s) := by
  have hx1 : ∀ j ≤ n, 1 < x j := fun j hj => lt_of_lt_of_le hx0 (chain_le hmono (Nat.zero_le j) hj)
  have h := cells_partial_summation hn x hx0 hmono g hg hs hθ
  have hsum : ∀ j ∈ range n, g j * ∑ k ∈ Ioc ⌊x j⌋₊ ⌊x (j + 1)⌋₊, fs s k * c3 k =
      g j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-s) := by
    intro j hj
    have hj' := mem_range.mp hj
    rw [sum_Ioc_fs_c3 (by linarith [hx1 j hj'.le]) (by linarith [hx1 (j + 1) hj'])
      (hend j hj'.le) (hend (j + 1) hj')]
  rw [Finset.sum_congr rfl hsum] at h
  have hedge : 2 * g 0 * (x 0 * fs s (x 0)) +
      2 * ∑ j ∈ Ico 1 n, max (g j - g (j - 1)) 0 * (x j * fs s (x j)) = cellEdge n x g s := by
    unfold cellEdge
    rw [mul_fs (by linarith [hx1 0 (Nat.zero_le n)])]
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_fs (by linarith [hx1 j (mem_Ico.mp hj).2.le])]
  unfold cellIntegral
  rw [← hedge]
  linarith

/-- **Upper bound** (`eq:record:cell-charge` without the restart terms):
`∑_j g_j ∑_{p ∈ [x_j, x_{j+1})} p^{-s} ≤ (½ + e) ∑_j g_j I_j(s) + e · (edge terms)`. -/
theorem cells_sum_upper {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx0 : 1 < x 0)
    (hmono : ∀ j < n, x j ≤ x (j + 1)) (hend : ∀ j ≤ n, NotPrime3 (x j)) (g : ℕ → ℝ)
    (hg : ∀ j < n, 0 ≤ g j) {s e : ℝ} (hs : 0 ≤ s)
    (hθ : ∀ t, x 0 ≤ t → t ≤ x n → |Target.theta4 t 3 - t / 2| ≤ e * t) :
    ∑ j ∈ range n, g j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-s) ≤
      (1 / 2 + e) * ∑ j ∈ range n, g j * cellIntegral s (x j) (x (j + 1)) +
        e * cellEdge n x g s := by
  have h := cells_prime_sum_abs hn x hx0 hmono hend g hg hs hθ
  have := (abs_le.mp h).2
  linarith

/-- **Lower bound** (the step of `lem:record:lower-start-sums`(i)):
`∑_j g_j ∑_{p ∈ [x_j, x_{j+1})} p^{-s} ≥ (½ - e) ∑_j g_j I_j(s) - e · (edge terms)`. -/
theorem cells_sum_lower {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx0 : 1 < x 0)
    (hmono : ∀ j < n, x j ≤ x (j + 1)) (hend : ∀ j ≤ n, NotPrime3 (x j)) (g : ℕ → ℝ)
    (hg : ∀ j < n, 0 ≤ g j) {s e : ℝ} (hs : 0 ≤ s)
    (hθ : ∀ t, x 0 ≤ t → t ≤ x n → |Target.theta4 t 3 - t / 2| ≤ e * t) :
    (1 / 2 - e) * ∑ j ∈ range n, g j * cellIntegral s (x j) (x (j + 1)) - e * cellEdge n x g s ≤
      ∑ j ∈ range n, g j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-s) := by
  have h := cells_prime_sum_abs hn x hx0 hmono hend g hg hs hθ
  have := (abs_le.mp h).1
  linarith

/-- `I_j(1) = log(log x_{j+1} / log x_j)`: the antiderivative of `1/(t log t)` is `log log t`. -/
theorem cellIntegral_one {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    cellIntegral 1 a b = Real.log (Real.log b / Real.log a) := by
  unfold cellIntegral
  have hla := Real.log_pos ha
  have hlb := Real.log_pos (lt_of_lt_of_le ha hab)
  rw [Real.log_div hlb.ne' hla.ne']
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Real.log (Real.log t)) (fs 1 t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have h0 : t ≠ 0 := by linarith
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have h := (Real.hasDerivAt_log h0).log hl
    convert h using 1
    unfold fs
    rw [Real.rpow_neg_one]
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((continuousOn_fs 1 ha).intervalIntegrable_of_Icc hab)]

end Sarkozy.Misc
