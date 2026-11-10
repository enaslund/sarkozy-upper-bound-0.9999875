module

public import Sarkozy.Kernel.KernelEstimate

@[expose] public section

/-!
# Kernel rates for every admissible triple

This module contains the exponent bookkeeping for the kernel estimate at an arbitrary
admissible triple `(β, κ, η)` in the sense of the paper's `def:kernel-conditions`
(`prop:record:kernel20`, `cor:kernel20`, `rem:record:K20-range`).

* `KernelAdmissible β κ η`: the seven strict inequalities (E1)–(E4), (K0)–(K2) of
  `def:kernel-conditions`, for positive `β, κ, η`.
* `cor_kernel20_admissible`, `cor_kernel20_slacks`: the triple `(1/20, 1/20, 17/100)` of
  `cor:kernel20` is admissible, with the seven slacks stated there.
* `KernelWindow β κ`: `0 < β`, `0 < κ`, `4κ + 5β/2 < 1/2`, `5κ + 17β/6 < 1/2`; every
  admissible triple satisfies it (`kernelWindow_of_admissible`, from (E1) and (E4) only).

The proof of the kernel estimate does not use the paper's arcs. As in `RatesTwentieth.lean`,
it uses the upstream (OpenAI) circle-method scheme of `finite_kernel_uniform`, with an
internal major-arc exponent `θ` (major-arc threshold `N^θ`, Dirichlet parameter
`⌈N^(1-θ)⌉`). Its error exponents are `2κ + β + θ - 1/2` (actual kernel, major arcs),
`κ + β/2 - θ/2 + ε/2` (actual kernel, minor arcs, `ε > 0` absorbing the logarithm), and
`3κ + 3β/2 - θ` (model kernel), and they are all at most `-β/6` for
`θ = (a + b)/2`, `ε = (b - a)/2`, `a = max (2κ + 4β/3) (3κ + 5β/3)`, `b = 1/2 - 2κ - 7β/6`;
the window `a < b` is `KernelWindow β κ`. The internal exponents do not appear in any
statement.

The lemmas `adm_major`, `adm_sqrt`, `adm_minor`, `adm_model`, `adm_saving`, `adm_all` are
symbolic versions of the `twentieth_*` lemmas of `RatesTwentieth.lean` (which follow the
upstream `kernel_rate_*` lemmas of `UniformRates.lean`). New material for this paper.
-/

namespace Sarkozy

namespace Kernel

open Finset

/-! ## Admissible triples -/

/-- Admissible triples for the kernel (`def:kernel-conditions`): positive `β, κ, η` with
(E1) `κ + β/2 - η/2 < -β/6`, (E2) `κ + β - η < -β/6`, (E3) `η + 2κ + 3β/2 - 1 < -β/6`,
(E4) `2η + 2κ + β - 1/2 < -β/6`, (K0) `3η < 1`, (K1) `κ + β/2 < η`,
(K2) `2η + κ + β/2 < 1`. -/
def KernelAdmissible (β κ η : ℝ) : Prop :=
  0 < β ∧ 0 < κ ∧ 0 < η ∧
  κ + β / 2 - η / 2 < -(β / 6) ∧
  κ + β - η < -(β / 6) ∧
  η + 2 * κ + 3 * β / 2 - 1 < -(β / 6) ∧
  2 * η + 2 * κ + β - 1 / 2 < -(β / 6) ∧
  3 * η < 1 ∧
  κ + β / 2 < η ∧
  2 * η + κ + β / 2 < 1

/-- `cor:kernel20`: the triple `(β, κ, η) = (1/20, 1/20, 17/100)` is admissible. -/
theorem cor_kernel20_admissible : KernelAdmissible (1 / 20) (1 / 20) (17 / 100) := by
  unfold KernelAdmissible
  norm_num

/-- The slacks of (E1), (E2), (E3), (E4), (K0), (K1), (K2): right-hand side minus left-hand
side (`cor:kernel20`). A triple of positive numbers is admissible exactly when all seven
slacks are positive. -/
noncomputable def kernelSlacks (β κ η : ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  (-(β / 6) - (κ + β / 2 - η / 2), -(β / 6) - (κ + β - η),
    -(β / 6) - (η + 2 * κ + 3 * β / 2 - 1), -(β / 6) - (2 * η + 2 * κ + β - 1 / 2),
    1 - 3 * η, η - (κ + β / 2), 1 - (2 * η + κ + β / 2))

/-- `cor:kernel20`: at `(1/20, 1/20, 17/100)` the seven slacks are
`1/600, 37/600, 97/150, 1/600, 49/100, 19/200, 117/200`. -/
theorem cor_kernel20_slacks :
    kernelSlacks (1 / 20) (1 / 20) (17 / 100) =
      (1 / 600, 37 / 600, 97 / 150, 1 / 600, 49 / 100, 19 / 200, 117 / 200) := by
  unfold kernelSlacks
  norm_num

lemma kernelAdmissible_iff_slacks (β κ η : ℝ) :
    KernelAdmissible β κ η ↔ 0 < β ∧ 0 < κ ∧ 0 < η ∧
      0 < (kernelSlacks β κ η).1 ∧ 0 < (kernelSlacks β κ η).2.1 ∧
      0 < (kernelSlacks β κ η).2.2.1 ∧ 0 < (kernelSlacks β κ η).2.2.2.1 ∧
      0 < (kernelSlacks β κ η).2.2.2.2.1 ∧ 0 < (kernelSlacks β κ η).2.2.2.2.2.1 ∧
      0 < (kernelSlacks β κ η).2.2.2.2.2.2 := by
  unfold KernelAdmissible kernelSlacks
  simp only
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩

/-- The exponent window of the circle-method scheme used here. -/
def KernelWindow (β κ : ℝ) : Prop :=
  0 < β ∧ 0 < κ ∧ 4 * κ + 5 * β / 2 < 1 / 2 ∧ 5 * κ + 17 * β / 6 < 1 / 2

/-- Every admissible triple lies in the window (only (E1), (E4) and positivity are used). -/
lemma kernelWindow_of_admissible {β κ η : ℝ} (h : KernelAdmissible β κ η) :
    KernelWindow β κ := by
  obtain ⟨hβ, hκ, _, e1, _, _, e4, _, _, _⟩ := h
  refine ⟨hβ, hκ, ?_, ?_⟩ <;> linarith

/-- The lower end `max (2κ + 4β/3) (3κ + 5β/3)` of the internal arc window. -/
noncomputable def windowLow (β κ : ℝ) : ℝ := max (2 * κ + 4 * β / 3) (3 * κ + 5 * β / 3)

/-- The upper end `1/2 - 2κ - 7β/6` of the internal arc window. -/
noncomputable def windowHigh (β κ : ℝ) : ℝ := 1 / 2 - 2 * κ - 7 * β / 6

/-- The internal major-arc exponent. -/
noncomputable def arcExp (β κ : ℝ) : ℝ := (windowLow β κ + windowHigh β κ) / 2

/-- The internal room for the logarithm. -/
noncomputable def logExp (β κ : ℝ) : ℝ := (windowHigh β κ - windowLow β κ) / 2

lemma window_facts {β κ : ℝ} (h : KernelWindow β κ) :
    0 < logExp β κ ∧ 0 < arcExp β κ ∧ arcExp β κ ≤ 1 / 2 ∧
    κ + β / 2 < arcExp β κ ∧ κ + β / 2 < 1 - arcExp β κ ∧
    2 * κ + β + arcExp β κ - 1 / 2 ≤ -(β / 6) ∧
    κ + β / 2 - arcExp β κ / 2 + logExp β κ / 2 ≤ -(β / 6) ∧
    3 * κ + 3 * β / 2 - arcExp β κ ≤ -(β / 6) := by
  obtain ⟨hβ, hκ, h1, h2⟩ := h
  have hl1 : 2 * κ + 4 * β / 3 ≤ windowLow β κ := le_max_left _ _
  have hl2 : 3 * κ + 5 * β / 3 ≤ windowLow β κ := le_max_right _ _
  have hlh : windowLow β κ < windowHigh β κ := by
    unfold windowLow windowHigh
    apply max_lt <;> linarith
  unfold arcExp logExp
  unfold windowHigh at hlh ⊢
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-! ## The error terms -/

lemma adm_rpow_mono {n : ℝ} (hn : 1 ≤ n) {a b : ℝ} (h : a ≤ b) : n ^ a ≤ n ^ b :=
  Real.rpow_le_rpow_of_exponent_le hn h

lemma adm_rpow_sq (n e : ℝ) (hn : 0 < n) : (n ^ e) ^ 2 = n ^ (2 * e) := by
  rw [← Real.rpow_natCast (n ^ e) 2, ← Real.rpow_mul hn.le]
  congr 1
  push_cast
  ring

lemma adm_rpow_cube (n e : ℝ) (hn : 0 < n) : (n ^ e) ^ 3 = n ^ (3 * e) := by
  rw [← Real.rpow_natCast (n ^ e) 3, ← Real.rpow_mul hn.le]
  congr 1
  push_cast
  ring

/-- The major-arc error of the actual kernel. -/
lemma adm_major (n P D H T M CD CH κ β θ : ℝ) (hn : 1 ≤ n)
    (hP0 : 0 ≤ P) (hPD : P ≤ D) (hD1 : 1 ≤ D) (hDn : D ≤ CD * n ^ κ)
    (hH1 : 1 ≤ H) (hHn : H ≤ CH * n ^ (β / 2))
    (hT : n ^ (1 - θ) ≤ T + 1) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    H * (2 * P * H + 1) * P * (4 * n ^ θ + 8 * Real.pi * n / (T + 1)) * M / n ≤
      3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 * n ^ (2 * κ + β + θ - 1 / 2) := by
  have hn0 : 0 < n := by linarith
  have hp : 0 < n ^ (1 - θ) := Real.rpow_pos_of_pos hn0 _
  have hT0 : 0 < T + 1 := hp.trans_le hT
  have hH0 : 0 ≤ H := by linarith
  have hDH : 1 ≤ D * H := by nlinarith
  have hD0 : 0 ≤ D := by linarith
  have hCDn : 0 ≤ CD * n ^ κ := hD0.trans hDn
  have hCHn : 0 ≤ CH * n ^ (β / 2) := hH0.trans hHn
  have hcost : H * (2 * P * H + 1) * P ≤ 3 * CD ^ 2 * CH ^ 2 * n ^ (2 * κ + β) := by
    calc
      H * (2 * P * H + 1) * P ≤ H * (2 * D * H + 1) * D := by gcongr
      _ ≤ H * (3 * D * H) * D := by gcongr; nlinarith
      _ = 3 * D ^ 2 * H ^ 2 := by ring
      _ ≤ 3 * (CD * n ^ κ) ^ 2 * (CH * n ^ (β / 2)) ^ 2 := by gcongr
      _ = 3 * CD ^ 2 * CH ^ 2 * ((n ^ κ) ^ 2 * (n ^ (β / 2)) ^ 2) := by ring
      _ = 3 * CD ^ 2 * CH ^ 2 * n ^ (2 * κ + β) := by
        rw [adm_rpow_sq n κ hn0, adm_rpow_sq n (β / 2) hn0, ← Real.rpow_add hn0]
        congr 2
        ring
  have hdiv : n / (T + 1) ≤ n ^ θ := by
    calc
      n / (T + 1) ≤ n / n ^ (1 - θ) := div_le_div_of_nonneg_left hn0.le hp hT
      _ = n ^ (1 : ℝ) / n ^ (1 - θ) := by rw [Real.rpow_one]
      _ = n ^ θ := by rw [← Real.rpow_sub hn0]; congr 1; ring
  have hfreq : 4 * n ^ θ + 8 * Real.pi * n / (T + 1) ≤ (4 + 8 * Real.pi) * n ^ θ := by
    have he : 8 * Real.pi * n / (T + 1) = 8 * Real.pi * (n / (T + 1)) := by ring
    rw [he]
    have hpi := Real.pi_pos
    nlinarith
  have hfreq0 : 0 ≤ 4 * n ^ θ + 8 * Real.pi * n / (T + 1) := by
    have hpi := Real.pi_pos
    have h1 : 0 ≤ n ^ θ := by positivity
    have h2 : 0 ≤ 8 * Real.pi * n / (T + 1) := div_nonneg (by positivity) hT0.le
    linarith
  have hcost0 : 0 ≤ 3 * CD ^ 2 * CH ^ 2 * n ^ (2 * κ + β) := by positivity
  calc
    H * (2 * P * H + 1) * P * (4 * n ^ θ + 8 * Real.pi * n / (T + 1)) * M / n ≤
        (3 * CD ^ 2 * CH ^ 2 * n ^ (2 * κ + β)) * ((4 + 8 * Real.pi) * n ^ θ) *
          n ^ ((1 : ℝ) / 2) / n := by
      apply div_le_div_of_nonneg_right _ hn0.le
      exact mul_le_mul (mul_le_mul hcost hfreq hfreq0 hcost0) hM hM0
        (mul_nonneg hcost0 (by positivity))
    _ = 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 *
        (n ^ (2 * κ + β) * n ^ θ * n ^ ((1 : ℝ) / 2) / n ^ (1 : ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 * n ^ (2 * κ + β + θ - 1 / 2) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_sub hn0]
      congr 2
      ring

/-- The logarithm of the Dirichlet parameter is absorbed by a small power. -/
lemma adm_log (n T θ ε : ℝ) (hn : 1 ≤ n) (hθ0 : 0 ≤ θ) (hε : 0 < ε) (hT1 : 1 ≤ T)
    (hTn : T ≤ 2 * n ^ (1 - θ)) : 1 + Real.log T ≤ (2 + 1 / ε) * n ^ ε := by
  have hn0 : 0 < n := by linarith
  have hT0 : 0 < T := by linarith
  have hnθ : n ^ (1 - θ) ≤ n := by
    have := adm_rpow_mono hn (show 1 - θ ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have h2n : T ≤ 2 * n := hTn.trans (by linarith)
  have hlog1 : Real.log T ≤ Real.log (2 * n) := Real.log_le_log hT0 h2n
  have hlog2 : Real.log (2 * n) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) hn0.ne'
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogn : Real.log n ≤ n ^ ε / ε := Real.log_le_rpow_div hn0.le hε
  have hnε : 1 ≤ n ^ ε := Real.one_le_rpow hn hε.le
  have hε' : 0 < 1 / ε := by positivity
  have h3 : n ^ ε / ε = (1 / ε) * n ^ ε := by ring
  nlinarith

/-- The square root in the minor-arc (Weyl) error. -/
lemma adm_sqrt (n T M θ ε : ℝ) (hn : 1 ≤ n) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hε : 0 < ε)
    (hT1 : 1 ≤ T) (hTn : T ≤ 2 * n ^ (1 - θ)) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    Real.sqrt (5 * M + 32 * M ^ 2 / n ^ θ + (64 * M + 8 * T) * (1 + Real.log T)) ≤
      Real.sqrt (37 + 80 * (2 + 1 / ε)) * n ^ ((1 - θ + ε) / 2) := by
  have hn0 : 0 < n := by linarith
  have hxθ : 0 < n ^ θ := Real.rpow_pos_of_pos hn0 _
  have h12 : n ^ ((1 : ℝ) / 2) ≤ n ^ (1 - θ) := adm_rpow_mono hn (by linarith)
  have h1ε : n ^ (1 - θ) ≤ n ^ (1 - θ + ε) := adm_rpow_mono hn (by linarith)
  have hs : M ^ 2 / n ^ θ ≤ n ^ (1 - θ) := by
    calc
      M ^ 2 / n ^ θ ≤ (n ^ ((1 : ℝ) / 2)) ^ 2 / n ^ θ := by gcongr
      _ = n ^ (1 - θ) := by
        rw [adm_rpow_sq n _ hn0, ← Real.rpow_sub hn0]
        congr 1
        ring
  have hlin : 64 * M + 8 * T ≤ 80 * n ^ (1 - θ) := by nlinarith [hM.trans h12]
  have hlog := adm_log n T θ ε hn hθ0 hε hT1 hTn
  have hlog0 : 0 ≤ 1 + Real.log T := by
    have := Real.log_nonneg hT1
    linarith
  have hprod : (64 * M + 8 * T) * (1 + Real.log T) ≤ 80 * (2 + 1 / ε) * n ^ (1 - θ + ε) := by
    calc
      (64 * M + 8 * T) * (1 + Real.log T) ≤ (80 * n ^ (1 - θ)) * ((2 + 1 / ε) * n ^ ε) := by
        apply mul_le_mul hlin hlog hlog0 (by positivity)
      _ = 80 * (2 + 1 / ε) * (n ^ (1 - θ) * n ^ ε) := by ring
      _ = 80 * (2 + 1 / ε) * n ^ (1 - θ + ε) := by rw [← Real.rpow_add hn0]
  have hinside : 5 * M + 32 * M ^ 2 / n ^ θ + (64 * M + 8 * T) * (1 + Real.log T) ≤
      (37 + 80 * (2 + 1 / ε)) * n ^ (1 - θ + ε) := by
    rw [show 32 * M ^ 2 / n ^ θ = 32 * (M ^ 2 / n ^ θ) by ring]
    have hM' : M ≤ n ^ (1 - θ + ε) := hM.trans (h12.trans h1ε)
    have hs' : M ^ 2 / n ^ θ ≤ n ^ (1 - θ + ε) := hs.trans h1ε
    nlinarith
  have hK : 0 ≤ 37 + 80 * (2 + 1 / ε) := by positivity
  calc
    Real.sqrt (5 * M + 32 * M ^ 2 / n ^ θ + (64 * M + 8 * T) * (1 + Real.log T)) ≤
        Real.sqrt ((37 + 80 * (2 + 1 / ε)) * n ^ (1 - θ + ε)) := Real.sqrt_le_sqrt hinside
    _ = Real.sqrt (37 + 80 * (2 + 1 / ε)) * Real.sqrt (n ^ (1 - θ + ε)) := Real.sqrt_mul hK _
    _ = Real.sqrt (37 + 80 * (2 + 1 / ε)) * n ^ ((1 - θ + ε) / 2) := by
      rw [Real.sqrt_eq_rpow (n ^ (1 - θ + ε)), ← Real.rpow_mul hn0.le]
      congr 2
      ring

/-- The minor-arc (Weyl) error of the actual kernel. -/
lemma adm_minor (n P D H T M CD CH κ β θ ε : ℝ) (hn : 1 ≤ n)
    (hPD : P ≤ D) (hDn : D ≤ CD * n ^ κ) (hP0 : 0 ≤ P)
    (hH0 : 0 ≤ H) (hHn : H ≤ CH * n ^ (β / 2))
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) (hε : 0 < ε)
    (hT1 : 1 ≤ T) (hTn : T ≤ 2 * n ^ (1 - θ)) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    (P * H) * (4 * M / n) *
        Real.sqrt (5 * M + 32 * M ^ 2 / n ^ θ + (64 * M + 8 * T) * (1 + Real.log T)) ≤
      4 * Real.sqrt (37 + 80 * (2 + 1 / ε)) * CD * CH * n ^ (κ + β / 2 - θ / 2 + ε / 2) := by
  have hn0 : 0 < n := by linarith
  have hs := adm_sqrt n T M θ ε hn hθ0 hθ hε hT1 hTn hM0 hM
  have hD0 : 0 ≤ D := hP0.trans hPD
  have hPH : P * H ≤ CD * CH * n ^ (κ + β / 2) := by
    calc
      P * H ≤ D * H := by gcongr
      _ ≤ (CD * n ^ κ) * (CH * n ^ (β / 2)) := by
        apply mul_le_mul hDn hHn hH0 (hD0.trans hDn)
      _ = CD * CH * (n ^ κ * n ^ (β / 2)) := by ring
      _ = CD * CH * n ^ (κ + β / 2) := by rw [← Real.rpow_add hn0]
  have hPH0 : 0 ≤ P * H := mul_nonneg hP0 hH0
  have hM4 : 4 * M / n ≤ 4 * n ^ ((1 : ℝ) / 2) / n := by gcongr
  calc
    (P * H) * (4 * M / n) *
        Real.sqrt (5 * M + 32 * M ^ 2 / n ^ θ + (64 * M + 8 * T) * (1 + Real.log T)) ≤
        (CD * CH * n ^ (κ + β / 2)) * (4 * n ^ ((1 : ℝ) / 2) / n) *
          (Real.sqrt (37 + 80 * (2 + 1 / ε)) * n ^ ((1 - θ + ε) / 2)) := by
      apply mul_le_mul (mul_le_mul hPH hM4 (by positivity) (hPH0.trans hPH)) hs
        (Real.sqrt_nonneg _) (by positivity [hPH0.trans hPH])
    _ = 4 * Real.sqrt (37 + 80 * (2 + 1 / ε)) * CD * CH *
        (n ^ (κ + β / 2) * n ^ ((1 : ℝ) / 2) * n ^ ((1 - θ + ε) / 2) / n ^ (1 : ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = 4 * Real.sqrt (37 + 80 * (2 + 1 / ε)) * CD * CH * n ^ (κ + β / 2 - θ / 2 + ε / 2) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_sub hn0]
      congr 2
      ring

/-- The model-kernel error. -/
lemma adm_model (n D H T L CD CH κ β θ : ℝ) (hn : 1 ≤ n)
    (hD0 : 0 ≤ D) (hDn : D ≤ CD * n ^ κ)
    (hH0 : 0 ≤ H) (hHn : H ≤ CH * n ^ (β / 2))
    (hT0 : 0 ≤ T) (hTn : T ≤ 2 * n ^ (1 - θ)) (hL0 : 0 ≤ L) (hLD : L ≤ 2 * D * H) :
    L ^ 2 * (T * L / n) ≤ 16 * CD ^ 3 * CH ^ 3 * n ^ (3 * κ + 3 * β / 2 - θ) := by
  have hn0 : 0 < n := by linarith
  have hLn : L ≤ 2 * CD * CH * n ^ (κ + β / 2) := by
    calc
      L ≤ 2 * D * H := hLD
      _ ≤ 2 * (CD * n ^ κ) * (CH * n ^ (β / 2)) := by
        have := mul_le_mul hDn hHn hH0 (hD0.trans hDn)
        nlinarith
      _ = 2 * CD * CH * (n ^ κ * n ^ (β / 2)) := by ring
      _ = 2 * CD * CH * n ^ (κ + β / 2) := by rw [← Real.rpow_add hn0]
  calc
    L ^ 2 * (T * L / n) ≤ (2 * CD * CH * n ^ (κ + β / 2)) ^ 2 *
        ((2 * n ^ (1 - θ)) * (2 * CD * CH * n ^ (κ + β / 2)) / n) := by gcongr
    _ = 16 * CD ^ 3 * CH ^ 3 * ((n ^ (κ + β / 2)) ^ 3 * n ^ (1 - θ) / n ^ (1 : ℝ)) := by
      rw [Real.rpow_one]; ring
    _ = 16 * CD ^ 3 * CH ^ 3 * n ^ (3 * κ + 3 * β / 2 - θ) := by
      rw [adm_rpow_cube n _ hn0, ← Real.rpow_add hn0, ← Real.rpow_sub hn0]
      congr 2
      ring

/-- `n^(-β/6) ≤ C_H^(1/3) H^(-1/3)` when `H ≤ C_H n^(β/2)`. -/
lemma adm_saving (n H CH β : ℝ) (hn : 1 ≤ n) (hH0 : 0 < H) (hCH0 : 0 < CH)
    (hHn : H ≤ CH * n ^ (β / 2)) :
    n ^ (-(β / 6)) ≤ CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3) := by
  have hn0 : 0 < n := by linarith
  have hb : (CH * n ^ (β / 2)) ^ (-(1 : ℝ) / 3) ≤ H ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hH0 hHn (by norm_num)
  have hsplit : (CH * n ^ (β / 2)) ^ (-(1 : ℝ) / 3) =
      CH ^ (-(1 : ℝ) / 3) * n ^ (-(β / 6)) := by
    rw [Real.mul_rpow hCH0.le (by positivity), ← Real.rpow_mul hn0.le]
    congr 2
    ring
  have hcancel : CH ^ ((1 : ℝ) / 3) * CH ^ (-(1 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add hCH0]
    norm_num
  calc
    n ^ (-(β / 6)) = CH ^ ((1 : ℝ) / 3) * (CH ^ (-(1 : ℝ) / 3) * n ^ (-(β / 6))) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3) := by
      rw [← hsplit]
      exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- `H^(-1/3) ≤ C_H^(1/3) n^(-β/6)` when `C_H⁻¹ n^(β/2) ≤ H`. -/
lemma adm_cutoff_saving (n H CH β : ℝ) (hn : 1 ≤ n) (hCH : 0 < CH)
    (hH : CH⁻¹ * n ^ (β / 2) ≤ H) :
    H ^ (-(1 : ℝ) / 3) ≤ CH ^ ((1 : ℝ) / 3) * n ^ (-(β / 6)) := by
  have hn0 : 0 < n := by linarith
  have hlow : 0 < CH⁻¹ * n ^ (β / 2) := by positivity
  have hb : H ^ (-(1 : ℝ) / 3) ≤ (CH⁻¹ * n ^ (β / 2)) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hlow hH (by norm_num)
  have hsplit : (CH⁻¹ * n ^ (β / 2)) ^ (-(1 : ℝ) / 3) =
      CH ^ ((1 : ℝ) / 3) * n ^ (-(β / 6)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le,
      Real.inv_rpow hCH.le, ← Real.rpow_neg hCH.le]
    congr 2
    · norm_num
    · ring
  rw [hsplit] at hb
  exact hb

/-- The constant of the uniform approximation at an admissible triple. -/
noncomputable def admRateConstant (β κ CD CH : ℝ) : ℝ :=
  2 ^ 64 + (3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 +
    4 * Real.sqrt (37 + 80 * (2 + 1 / logExp β κ)) * CD * CH + 16 * CD ^ 3 * CH ^ 3) *
    CH ^ ((1 : ℝ) / 3)

lemma admRateConstant_pos (β κ CD CH : ℝ) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    0 < admRateConstant β κ CD CH := by
  unfold admRateConstant
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 ≤ CH := by linarith
  have hpi := Real.pi_pos
  have h1 : 0 ≤ 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 +
      4 * Real.sqrt (37 + 80 * (2 + 1 / logExp β κ)) * CD * CH + 16 * CD ^ 3 * CH ^ 3 := by
    have := Real.sqrt_nonneg (37 + 80 * (2 + 1 / logExp β κ))
    positivity
  have h2 : 0 ≤ CH ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hCH0 _
  have h3 : (0 : ℝ) < 2 ^ 64 := by norm_num
  nlinarith [mul_nonneg h1 h2]

/-- The four error terms of `finite_kernel_uniform`, with the internal major-arc threshold
`X = n^θ`, `θ = arcExp β κ`, are at most `admRateConstant β κ C_D C_H · H^(-1/3)`. -/
lemma adm_all (β κ : ℝ) (hw : KernelWindow β κ) (n P D H T M L CD CH : ℝ) (hn : 1 ≤ n)
    (hP0 : 0 ≤ P) (hPD : P ≤ D) (hD1 : 1 ≤ D) (hDn : D ≤ CD * n ^ κ)
    (hH1 : 1 ≤ H) (hHn : H ≤ CH * n ^ (β / 2)) (hCD : 1 ≤ CD) (hCH : 1 ≤ CH)
    (hT1 : 1 ≤ T) (hTlo : n ^ (1 - arcExp β κ) ≤ T + 1) (hTn : T ≤ 2 * n ^ (1 - arcExp β κ))
    (hL0 : 0 ≤ L) (hLD : L ≤ 2 * D * H) (hM0 : 0 ≤ M) (hM : M ≤ n ^ ((1 : ℝ) / 2)) :
    2 ^ 64 * H ^ (-(1 : ℝ) / 3) +
      (H * (2 * P * H + 1) * P) * (4 * n ^ arcExp β κ + 8 * Real.pi * n / (T + 1)) * M / n +
      (P * H) * (4 * M / n) *
        Real.sqrt (5 * M + 32 * M ^ 2 / n ^ arcExp β κ + (64 * M + 8 * T) * (1 + Real.log T)) +
      L ^ 2 * (T * L / n) ≤
      admRateConstant β κ CD CH * H ^ (-(1 : ℝ) / 3) := by
  obtain ⟨hε, hθ0, hθ, _, _, e1, e2, e3⟩ := window_facts hw
  have hCD0 : 0 ≤ CD := by linarith
  have hCH0 : 0 ≤ CH := by linarith
  have h1 := adm_major n P D H T M CD CH κ β (arcExp β κ) hn hP0 hPD hD1 hDn hH1 hHn hTlo hM0 hM
  have h2 := adm_minor n P D H T M CD CH κ β (arcExp β κ) (logExp β κ) hn hPD hDn hP0
    (by linarith) hHn hθ0.le hθ hε hT1 hTn hM0 hM
  have h3 := adm_model n D H T L CD CH κ β (arcExp β κ) hn (by linarith) hDn (by linarith) hHn
    (by linarith) hTn hL0 hLD
  have hsv := adm_saving n H CH β hn (by linarith) (by linarith) hHn
  have k1 : n ^ (2 * κ + β + arcExp β κ - 1 / 2) ≤ n ^ (-(β / 6)) := adm_rpow_mono hn e1
  have k2 : n ^ (κ + β / 2 - arcExp β κ / 2 + logExp β κ / 2) ≤ n ^ (-(β / 6)) :=
    adm_rpow_mono hn e2
  have k3 : n ^ (3 * κ + 3 * β / 2 - arcExp β κ) ≤ n ^ (-(β / 6)) := adm_rpow_mono hn e3
  have hpi := Real.pi_pos
  have hA1 : 0 ≤ 3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 := by positivity
  have hA2 : 0 ≤ 4 * Real.sqrt (37 + 80 * (2 + 1 / logExp β κ)) * CD * CH := by
    have := Real.sqrt_nonneg (37 + 80 * (2 + 1 / logExp β κ))
    positivity
  have hA3 : 0 ≤ 16 * CD ^ 3 * CH ^ 3 := by positivity
  have m1 := mul_le_mul_of_nonneg_left (k1.trans hsv) hA1
  have m2 := mul_le_mul_of_nonneg_left (k2.trans hsv) hA2
  have m3 := mul_le_mul_of_nonneg_left (k3.trans hsv) hA3
  have hfinal : admRateConstant β κ CD CH * H ^ (-(1 : ℝ) / 3) =
      2 ^ 64 * H ^ (-(1 : ℝ) / 3) +
        3 * (4 + 8 * Real.pi) * CD ^ 2 * CH ^ 2 * (CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3)) +
        4 * Real.sqrt (37 + 80 * (2 + 1 / logExp β κ)) * CD * CH *
          (CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3)) +
        16 * CD ^ 3 * CH ^ 3 * (CH ^ ((1 : ℝ) / 3) * H ^ (-(1 : ℝ) / 3)) := by
    unfold admRateConstant
    ring
  rw [hfinal]
  linarith

end Kernel

end Sarkozy
