module

public import Sarkozy.Extraction.MergedCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# Log-convex nonstar coefficients (`lem:logconvex-coefficients`)

`paper/sections/16_extraction.tex`, `lem:logconvex-coefficients`: for a fixed partition `𝔓` with
fixed records and one error pair, the nonstar coefficients `C_k(P)` of `cor:extraction-leaf`(b)
factor as `C_k = M D_k`, `M(P) = R_full(P)² (1 - ê(P))^{-n}`, with `D_k` a positive sum of products
of square roots of the numerators of the leaf factors; `M`, `D_k`, `C_k` are nonincreasing in `P`
and log-convex in `log P`; hence for `P₀ ≤ Q ≤ P₁`, `θ = log(Q/P₀)/log(P₁/P₀)` and `c_i ≥ C_k(P_i)`,
`C_k(Q) ≤ M(Q) (c₀/M(P₀))^{1-θ} (c₁/M(P₁))^θ ≤ c₀^{1-θ} c₁^θ`.

## Formal setting

* Everything is a function of `u = log P`, so `r = P^{-1/2} = e^{-u/2}`. A count error is
  `lcPoly a b u = a r + b r²` with `a, b ≥ 0`: `lc_coarseError_exp` writes the coarse error
  `e_t(e^u, n') = 2^t (h_t r + n' r²)` in this form (`lc_coarseH_nonneg`: `h_t ≥ 0`, Bernoulli),
  and `lc_numerator_exp` the numerator `1 + e_s(P, n') + r² 2^s 𝖲(s)` of a leaf factor of
  `eq:leaf-factors`. (The graded error `e^-_t(n') = a_t r + (b_t + 2^t n') r²` has the same form,
  so both error pairs are covered.)
* `LcData` holds the data of the coefficients (classes, `ex*`, witness sizes, the numerators of the
  non-witness vertices, the errors `e_{d⁰_i}` of `R_full`, `ê`, `n`); `LcData.Valid`: nonnegative
  coefficients and `2(n - k)` non-witness vertices in a class of witness size `k ≤ n`
  (`lcData_valid_example`: a non-vacuous instance). `LcData.Ck` is `C_k` exactly as in
  `cor:extraction-leaf`(b), `LcData.M` and `LcData.Dk` as in the lemma.
* Log-convexity is used in multiplicative form (`LcLogConvex I g`:
  `g((1-θ)u₀ + θu₁) ≤ g(u₀)^{1-θ} g(u₁)^θ`), which for positive `g` is convexity of `log g`.

## Results

* Closure (`lc_const`, `lc_exp`, `lc_add` (Hölder `lc_holder_two`), `lc_mul`, `lc_rpow`, `lc_sum`,
  `lc_prod`, `lc_inv_one_sub`) and monotonicity (`lc_anti_*`) lemmas.
* `LcData.Ck_eq`: `C_k = M D_k`. `LcData.logConvex_M`, `logConvex_Dk`, `logConvex_Ck`: log-convexity
  on any convex range where all errors are below one; `anti_M`, `anti_Dk`, `anti_Ck`,
  `Ck_antitone_P`: monotonicity.
* `LcData.Ck_interp` (in `u`) and **`LcData.logconvex_coefficients`** (in `P`): the interpolation.

## Deviation from the paper

The log-convexity of `(1 - ε)^{-1}` is proved without derivatives: `ε` is log-convex, and
Hölder's inequality `(1 - ε₀)^{1-θ}(1 - ε₁)^θ + ε₀^{1-θ}ε₁^θ ≤ 1` gives
`(1 - ε(u_θ))^{-1} ≤ (1 - ε₀)^{-(1-θ)} (1 - ε₁)^{-θ}` (`lc_inv_one_sub`). The paper's second
derivative argument is replaced by this; nothing else changes.
-/

open Finset

namespace Sarkozy.ExtractionK

/-! ## Log-convexity in multiplicative form -/

/-- `g` is log-convex on `I` in the variable `u`:
`g((1 - θ) u₀ + θ u₁) ≤ g(u₀)^{1-θ} g(u₁)^θ` for `u₀, u₁ ∈ I`, `θ ∈ [0, 1]`. For a positive `g`
this is the convexity of `log g` on `I`. -/
def LcLogConvex (I : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ u₀ ∈ I, ∀ u₁ ∈ I, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    g ((1 - θ) * u₀ + θ * u₁) ≤ g u₀ ^ (1 - θ) * g u₁ ^ θ

/-- Hölder's inequality for two terms: `a^{1-θ} b^θ + c^{1-θ} d^θ ≤ (a + c)^{1-θ} (b + d)^θ`
for `a, b, c, d ≥ 0` and `θ ∈ [0, 1]`. -/
theorem lc_holder_two {a b c d θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    a ^ (1 - θ) * b ^ θ + c ^ (1 - θ) * d ^ θ ≤ (a + c) ^ (1 - θ) * (b + d) ^ θ := by
  have h1θ : 0 ≤ 1 - θ := by linarith
  rcases eq_or_lt_of_le (add_nonneg ha hc) with hA | hA
  · -- `a = c = 0`
    have ha0 : a = 0 := by linarith
    have hc0 : c = 0 := by linarith
    subst ha0 hc0
    rcases eq_or_lt_of_le h1θ with h | h
    · have hθ : θ = 1 := by linarith
      subst hθ
      simp
    · rw [Real.zero_rpow h.ne', zero_mul, zero_mul, add_zero]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (add_nonneg hb hd) _)
  rcases eq_or_lt_of_le (add_nonneg hb hd) with hB | hB
  · have hb0 : b = 0 := by linarith
    have hd0 : d = 0 := by linarith
    subst hb0 hd0
    rcases eq_or_lt_of_le hθ0 with h | h
    · subst h
      simp
    · rw [Real.zero_rpow h.ne', mul_zero, mul_zero, add_zero]
      exact mul_nonneg (Real.rpow_nonneg (add_nonneg ha hc) _) (Real.rpow_nonneg (by norm_num) _)
  have hAB : 0 < (a + c) ^ (1 - θ) * (b + d) ^ θ := mul_pos (Real.rpow_pos_of_pos hA _)
    (Real.rpow_pos_of_pos hB _)
  have key : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ (1 - θ) * y ^ θ ≤
      (a + c) ^ (1 - θ) * (b + d) ^ θ * ((1 - θ) * (x / (a + c)) + θ * (y / (b + d))) := by
    intro x y hx hy
    have hg := Real.geom_mean_le_arith_mean2_weighted h1θ hθ0 (div_nonneg hx hA.le)
      (div_nonneg hy hB.le) (by ring : 1 - θ + θ = 1)
    rw [Real.div_rpow hx hA.le, Real.div_rpow hy hB.le] at hg
    have e : x ^ (1 - θ) * y ^ θ = (a + c) ^ (1 - θ) * (b + d) ^ θ *
        (x ^ (1 - θ) / (a + c) ^ (1 - θ) * (y ^ θ / (b + d) ^ θ)) := by
      have h1 : (a + c) ^ (1 - θ) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
      have h2 : (b + d) ^ θ ≠ 0 := (Real.rpow_pos_of_pos hB _).ne'
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hg hAB.le
  have h1 := key a b ha hb
  have h2 := key c d hc hd
  have hsum : (1 - θ) * (a / (a + c)) + θ * (b / (b + d)) +
      ((1 - θ) * (c / (a + c)) + θ * (d / (b + d))) = 1 := by
    field_simp
    ring
  calc a ^ (1 - θ) * b ^ θ + c ^ (1 - θ) * d ^ θ
      ≤ (a + c) ^ (1 - θ) * (b + d) ^ θ * ((1 - θ) * (a / (a + c)) + θ * (b / (b + d))) +
          (a + c) ^ (1 - θ) * (b + d) ^ θ * ((1 - θ) * (c / (a + c)) + θ * (d / (b + d))) :=
        add_le_add h1 h2
    _ = (a + c) ^ (1 - θ) * (b + d) ^ θ := by rw [← mul_add, hsum, mul_one]

/-- Positive constants are log-convex. -/
theorem lc_const (I : Set ℝ) {c : ℝ} (hc : 0 ≤ c) : LcLogConvex I (fun _ => c) := by
  intro u₀ _ u₁ _ θ _ _
  rw [← Real.rpow_add' hc (by rw [sub_add_cancel]; exact one_ne_zero)]
  simp

/-- `e^{k u}` is log-convex (with equality). -/
theorem lc_exp (I : Set ℝ) (k : ℝ) : LcLogConvex I (fun u => Real.exp (k * u)) := by
  intro u₀ _ u₁ _ θ _ _
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  exact le_of_eq (congrArg Real.exp (by ring))

/-- Sums of nonnegative log-convex functions are log-convex (Hölder). -/
theorem lc_add {I : Set ℝ} {f g : ℝ → ℝ} (hf : LcLogConvex I f) (hg : LcLogConvex I g)
    (hf0 : ∀ u ∈ I, 0 ≤ f u) (hg0 : ∀ u ∈ I, 0 ≤ g u) :
    LcLogConvex I (fun u => f u + g u) := by
  intro u₀ h₀ u₁ h₁ θ hθ0 hθ1
  exact (add_le_add (hf u₀ h₀ u₁ h₁ θ hθ0 hθ1) (hg u₀ h₀ u₁ h₁ θ hθ0 hθ1)).trans
    (lc_holder_two (hf0 u₀ h₀) (hf0 u₁ h₁) (hg0 u₀ h₀) (hg0 u₁ h₁) hθ0 hθ1)

theorem lc_mem {I : Set ℝ} (hI : Convex ℝ I) {u₀ u₁ θ : ℝ} (h₀ : u₀ ∈ I) (h₁ : u₁ ∈ I)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : (1 - θ) * u₀ + θ * u₁ ∈ I := by
  have := hI h₀ h₁ (by linarith : 0 ≤ 1 - θ) hθ0 (by ring)
  simpa [smul_eq_mul] using this

/-- Products of nonnegative log-convex functions are log-convex. -/
theorem lc_mul {I : Set ℝ} (hI : Convex ℝ I) {f g : ℝ → ℝ} (hf : LcLogConvex I f)
    (hg : LcLogConvex I g) (hf0 : ∀ u ∈ I, 0 ≤ f u) (hg0 : ∀ u ∈ I, 0 ≤ g u) :
    LcLogConvex I (fun u => f u * g u) := by
  intro u₀ h₀ u₁ h₁ θ hθ0 hθ1
  have hm := lc_mem hI h₀ h₁ hθ0 hθ1
  calc f ((1 - θ) * u₀ + θ * u₁) * g ((1 - θ) * u₀ + θ * u₁)
      ≤ (f u₀ ^ (1 - θ) * f u₁ ^ θ) * (g u₀ ^ (1 - θ) * g u₁ ^ θ) :=
        mul_le_mul (hf u₀ h₀ u₁ h₁ θ hθ0 hθ1) (hg u₀ h₀ u₁ h₁ θ hθ0 hθ1) (hg0 _ hm)
          (mul_nonneg (Real.rpow_nonneg (hf0 u₀ h₀) _) (Real.rpow_nonneg (hf0 u₁ h₁) _))
    _ = (f u₀ * g u₀) ^ (1 - θ) * (f u₁ * g u₁) ^ θ := by
        rw [Real.mul_rpow (hf0 u₀ h₀) (hg0 u₀ h₀), Real.mul_rpow (hf0 u₁ h₁) (hg0 u₁ h₁)]
        ring

/-- Nonnegative real powers of nonnegative log-convex functions are log-convex. -/
theorem lc_rpow {I : Set ℝ} (hI : Convex ℝ I) {f : ℝ → ℝ} (hf : LcLogConvex I f)
    (hf0 : ∀ u ∈ I, 0 ≤ f u) {a : ℝ} (ha : 0 ≤ a) : LcLogConvex I (fun u => f u ^ a) := by
  intro u₀ h₀ u₁ h₁ θ hθ0 hθ1
  have hm := lc_mem hI h₀ h₁ hθ0 hθ1
  calc f ((1 - θ) * u₀ + θ * u₁) ^ a ≤ (f u₀ ^ (1 - θ) * f u₁ ^ θ) ^ a :=
        Real.rpow_le_rpow (hf0 _ hm) (hf u₀ h₀ u₁ h₁ θ hθ0 hθ1) ha
    _ = (f u₀ ^ a) ^ (1 - θ) * (f u₁ ^ a) ^ θ := by
        rw [Real.mul_rpow (Real.rpow_nonneg (hf0 u₀ h₀) _) (Real.rpow_nonneg (hf0 u₁ h₁) _),
          ← Real.rpow_mul (hf0 u₀ h₀), ← Real.rpow_mul (hf0 u₁ h₁),
          ← Real.rpow_mul (hf0 u₀ h₀), ← Real.rpow_mul (hf0 u₁ h₁), mul_comm (1 - θ) a,
          mul_comm θ a]

/-- `(1 - ε)^{-1}` is log-convex if `ε ∈ [0, 1)` is log-convex (Hölder:
`(1 - ε₀)^{1-θ} (1 - ε₁)^θ + ε₀^{1-θ} ε₁^θ ≤ 1`). This replaces the second-derivative argument of
the paper. -/
theorem lc_inv_one_sub {I : Set ℝ} (hI : Convex ℝ I) {ε : ℝ → ℝ} (hε : LcLogConvex I ε)
    (hε0 : ∀ u ∈ I, 0 ≤ ε u) (hε1 : ∀ u ∈ I, ε u < 1) :
    LcLogConvex I (fun u => (1 - ε u)⁻¹) := by
  intro u₀ h₀ u₁ h₁ θ hθ0 hθ1
  have hm := lc_mem hI h₀ h₁ hθ0 hθ1
  have hx0 : 0 < 1 - ε u₀ := by linarith [hε1 u₀ h₀]
  have hx1 : 0 < 1 - ε u₁ := by linarith [hε1 u₁ h₁]
  have hH := lc_holder_two hx0.le hx1.le (hε0 u₀ h₀) (hε0 u₁ h₁) hθ0 hθ1
  simp only [sub_add_cancel, Real.one_rpow, mul_one] at hH
  have hεθ := hε u₀ h₀ u₁ h₁ θ hθ0 hθ1
  have hpos : 0 < (1 - ε u₀) ^ (1 - θ) * (1 - ε u₁) ^ θ :=
    mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.rpow_pos_of_pos hx1 _)
  have hle : (1 - ε u₀) ^ (1 - θ) * (1 - ε u₁) ^ θ ≤ 1 - ε ((1 - θ) * u₀ + θ * u₁) := by
    linarith
  calc (1 - ε ((1 - θ) * u₀ + θ * u₁))⁻¹ ≤ ((1 - ε u₀) ^ (1 - θ) * (1 - ε u₁) ^ θ)⁻¹ :=
        inv_anti₀ hpos hle
    _ = (1 - ε u₀)⁻¹ ^ (1 - θ) * (1 - ε u₁)⁻¹ ^ θ := by
        rw [Real.inv_rpow hx0.le, Real.inv_rpow hx1.le, mul_inv]

theorem lc_congr {I : Set ℝ} (hI : Convex ℝ I) {f g : ℝ → ℝ} (hf : LcLogConvex I f)
    (h : ∀ u ∈ I, f u = g u) : LcLogConvex I g := by
  intro u₀ h₀ u₁ h₁ θ hθ0 hθ1
  rw [← h u₀ h₀, ← h u₁ h₁, ← h _ (lc_mem hI h₀ h₁ hθ0 hθ1)]
  exact hf u₀ h₀ u₁ h₁ θ hθ0 hθ1

/-- Finite products of nonnegative log-convex functions. -/
theorem lc_prod {ι : Type*} {I : Set ℝ} (hI : Convex ℝ I) (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, LcLogConvex I (f i)) (hf0 : ∀ i ∈ s, ∀ u ∈ I, 0 ≤ f i u) :
    LcLogConvex I (fun u => ∏ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact lc_const I zero_le_one
  | insert a s ha ih =>
    have h1 := ih (fun i hi => hf i (mem_insert_of_mem hi))
      (fun i hi => hf0 i (mem_insert_of_mem hi))
    have h2 := lc_mul hI (hf a (mem_insert_self a s)) h1 (hf0 a (mem_insert_self a s))
      (fun u hu => prod_nonneg fun i hi => hf0 i (mem_insert_of_mem hi) u hu)
    refine lc_congr hI h2 fun u _ => ?_
    rw [prod_insert ha]

/-- Finite sums of nonnegative log-convex functions. -/
theorem lc_sum {ι : Type*} {I : Set ℝ} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, LcLogConvex I (f i)) (hf0 : ∀ i ∈ s, ∀ u ∈ I, 0 ≤ f i u) :
    LcLogConvex I (fun u => ∑ i ∈ s, f i u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact lc_const I le_rfl
  | insert a s ha ih =>
    have h1 := ih (fun i hi => hf i (mem_insert_of_mem hi))
      (fun i hi => hf0 i (mem_insert_of_mem hi))
    have h2 := lc_add (hf a (mem_insert_self a s)) h1 (hf0 a (mem_insert_self a s))
      (fun u hu => sum_nonneg fun i hi => hf0 i (mem_insert_of_mem hi) u hu)
    intro u₀ h₀ u₁ h₁ θ hθ0 hθ1
    have := h2 u₀ h₀ u₁ h₁ θ hθ0 hθ1
    simpa only [sum_insert ha] using this

/-! ## Nonincreasing functions -/

theorem lc_anti_exp (I : Set ℝ) {k : ℝ} (hk : k ≤ 0) :
    AntitoneOn (fun u => Real.exp (k * u)) I := by
  intro _ _ _ _ huv
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem lc_anti_add {I : Set ℝ} {f g : ℝ → ℝ} (hf : AntitoneOn f I) (hg : AntitoneOn g I) :
    AntitoneOn (fun u => f u + g u) I :=
  fun _ hu _ hv huv => add_le_add (hf hu hv huv) (hg hu hv huv)

theorem lc_anti_mul {I : Set ℝ} {f g : ℝ → ℝ} (hf : AntitoneOn f I) (hg : AntitoneOn g I)
    (hf0 : ∀ u ∈ I, 0 ≤ f u) (hg0 : ∀ u ∈ I, 0 ≤ g u) :
    AntitoneOn (fun u => f u * g u) I :=
  fun u hu v hv huv => mul_le_mul (hf hu hv huv) (hg hu hv huv) (hg0 v hv) (hf0 u hu)

theorem lc_anti_const (I : Set ℝ) (c : ℝ) : AntitoneOn (fun _ => c) I :=
  fun _ _ _ _ _ => le_rfl

theorem lc_anti_rpow {I : Set ℝ} {f : ℝ → ℝ} (hf : AntitoneOn f I) (hf0 : ∀ u ∈ I, 0 ≤ f u)
    {a : ℝ} (ha : 0 ≤ a) : AntitoneOn (fun u => f u ^ a) I :=
  fun _ hu v hv huv => Real.rpow_le_rpow (hf0 v hv) (hf hu hv huv) ha

theorem lc_anti_inv_one_sub {I : Set ℝ} {ε : ℝ → ℝ} (hε : AntitoneOn ε I)
    (hε1 : ∀ u ∈ I, ε u < 1) : AntitoneOn (fun u => (1 - ε u)⁻¹) I := by
  intro u hu v hv huv
  have h1 := hε hu hv huv
  have h2 := hε1 u hu
  exact inv_anti₀ (by linarith) (by linarith)

theorem lc_anti_prod {ι : Type*} {I : Set ℝ} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, AntitoneOn (f i) I) (hf0 : ∀ i ∈ s, ∀ u ∈ I, 0 ≤ f i u) :
    AntitoneOn (fun u => ∏ i ∈ s, f i u) I := by
  intro u hu v hv huv
  exact prod_le_prod₀ (fun i hi => hf0 i hi v hv) (fun i hi => hf i hi hu hv huv)

theorem lc_anti_sum {ι : Type*} {I : Set ℝ} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, AntitoneOn (f i) I) : AntitoneOn (fun u => ∑ i ∈ s, f i u) I := by
  intro u hu v hv huv
  exact sum_le_sum fun i hi => hf i hi hu hv huv

/-! ## Count errors as functions of `u = log P` -/

/-- `a r + b r²` with `r = P^{-1/2} = e^{-u/2}`: the form of every count error `e_t(P, n')` of
`eq:graphs:et` (and of every `e_s + r² 2^s S`). -/
noncomputable def lcPoly (a b u : ℝ) : ℝ :=
  a * Real.exp ((-1 / 2) * u) + b * Real.exp ((-1) * u)

theorem lcPoly_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u : ℝ) : 0 ≤ lcPoly a b u :=
  add_nonneg (mul_nonneg ha (Real.exp_pos _).le) (mul_nonneg hb (Real.exp_pos _).le)

theorem lcPoly_logConvex {I : Set ℝ} (hI : Convex ℝ I) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    LcLogConvex I (lcPoly a b) := by
  have h1 := lc_mul hI (lc_const I ha) (lc_exp I (-1 / 2)) (fun _ _ => ha)
    (fun _ _ => (Real.exp_pos _).le)
  have h2 := lc_mul hI (lc_const I hb) (lc_exp I (-1)) (fun _ _ => hb)
    (fun _ _ => (Real.exp_pos _).le)
  exact lc_add h1 h2 (fun _ _ => mul_nonneg ha (Real.exp_pos _).le)
    (fun _ _ => mul_nonneg hb (Real.exp_pos _).le)

theorem lcPoly_anti (I : Set ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    AntitoneOn (lcPoly a b) I := by
  have h1 := lc_anti_mul (lc_anti_const I a) (lc_anti_exp I (by norm_num : (-1 / 2 : ℝ) ≤ 0))
    (fun _ _ => ha) (fun _ _ => (Real.exp_pos _).le)
  have h2 := lc_anti_mul (lc_anti_const I b) (lc_anti_exp I (by norm_num : (-1 : ℝ) ≤ 0))
    (fun _ _ => hb) (fun _ _ => (Real.exp_pos _).le)
  exact lc_anti_add h1 h2

/-- `1 + ε` with `ε = a r + b r²`. -/
theorem lcPoly_one_add_logConvex {I : Set ℝ} (hI : Convex ℝ I) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) : LcLogConvex I (fun u => 1 + lcPoly a b u) :=
  lc_add (lc_const I zero_le_one) (lcPoly_logConvex hI ha hb) (fun _ _ => zero_le_one)
    (fun u _ => lcPoly_nonneg ha hb u)

/-- `h_t = t/2 - 1 + 2^{-t} ≥ 0` (Bernoulli's inequality). -/
theorem lc_coarseH_nonneg (t : ℕ) : 0 ≤ Sarkozy.Extraction.coarseH t := by
  unfold Sarkozy.Extraction.coarseH
  have h := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ -1 / 2) t
  have e : (1 : ℝ) + -1 / 2 = 2⁻¹ := by norm_num
  rw [e] at h
  linarith

/-- The coarse count error `e_t(P, n') = 2^t (h_t r + n' r²)` at `P = e^u` is
`lcPoly (2^t h_t) (2^t n') u`, with nonnegative coefficients. -/
theorem lc_coarseError_exp (t : ℕ) (n' u : ℝ) :
    Sarkozy.Extraction.coarseError t (Real.exp u) n' =
      lcPoly (2 ^ t * Sarkozy.Extraction.coarseH t) (2 ^ t * n') u := by
  unfold Sarkozy.Extraction.coarseError lcPoly
  have h1 : (Real.sqrt (Real.exp u))⁻¹ = Real.exp ((-1 / 2) * u) := by
    rw [← Real.exp_half, ← Real.exp_neg]
    congr 1
    ring
  have h2 : (Real.sqrt (Real.exp u))⁻¹ ^ 2 = Real.exp ((-1) * u) := by
    rw [h1, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h2, h1]
  ring

/-- `r² = P^{-1} = e^{-u}`. -/
theorem lc_rsq_exp (u : ℝ) : (Real.sqrt (Real.exp u))⁻¹ ^ 2 = Real.exp ((-1) * u) := by
  rw [← Real.exp_half, ← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A numerator `1 + e_s(P, n') + r² 2^s S` of a leaf factor (`eq:leaf-factors`) at `P = e^u` is
`1 + lcPoly (2^s h_s) (2^s n' + 2^s S) u`. -/
theorem lc_numerator_exp (s : ℕ) (n' S u : ℝ) :
    1 + Sarkozy.Extraction.coarseError s (Real.exp u) n' +
        (Real.sqrt (Real.exp u))⁻¹ ^ 2 * 2 ^ s * S =
      1 + lcPoly (2 ^ s * Sarkozy.Extraction.coarseH s) (2 ^ s * n' + 2 ^ s * S) u := by
  rw [lc_coarseError_exp, lc_rsq_exp]
  unfold lcPoly
  ring

/-! ## The coefficients `C_k` of a fixed partition with fixed records -/

/-- The data of the nonstar coefficients `C_k` of `cor:extraction-leaf`(b) for a fixed partition
`𝔓` with fixed records and one error pair, as functions of `u = log P`:
* the classes `cls`, with `ex*(𝒞)` (`ex`), the witness size (`wk`) and the non-witness vertices
  (`verts`), each vertex `v` with the numerator `1 + numA r + numB r²` of its leaf factor
  `𝖿_m(s_v)` or `𝖿_ϱ(s_v)` (`lc_numerator_exp`: this is the form of
  `1 + e_s(P, n') + r² 2^s 𝖲(s)`);
* the vertices `degs` of `U⁺`, with `e_{d⁰_i}(P, n) = errA r + errB r²` (for `R_full`);
* `ê(P) = e_{Δ⁺}(P, n) = hatA r + hatB r²`, and `n = |U⁺|`. -/
structure LcData (ι κ δ : Type*) where
  cls : Finset ι
  ex : ι → ℕ
  wk : ι → ℕ
  verts : ι → Finset κ
  numA : ι → κ → ℝ
  numB : ι → κ → ℝ
  degs : Finset δ
  errA : δ → ℝ
  errB : δ → ℝ
  hatA : ℝ
  hatB : ℝ
  n : ℕ

namespace LcData

variable {ι κ δ : Type*} (D : LcData ι κ δ)

/-- The conditions on the data: nonnegative coefficients (`it:et:poly`), and `2(n - k)`
non-witness vertices in a class of witness size `k ≤ n` (`def:extraction:records`). -/
structure Valid : Prop where
  numA_nonneg : ∀ c v, 0 ≤ D.numA c v
  numB_nonneg : ∀ c v, 0 ≤ D.numB c v
  errA_nonneg : ∀ i, 0 ≤ D.errA i
  errB_nonneg : ∀ i, 0 ≤ D.errB i
  hatA_nonneg : 0 ≤ D.hatA
  hatB_nonneg : 0 ≤ D.hatB
  wk_le : ∀ c ∈ D.cls, D.wk c ≤ D.n
  card_verts : ∀ c ∈ D.cls, (D.verts c).card = 2 * (D.n - D.wk c)

/-- The numerator of the leaf factor of the vertex `v` of the class `c`. -/
noncomputable def num (c : ι) (v : κ) (u : ℝ) : ℝ := 1 + lcPoly (D.numA c v) (D.numB c v) u

/-- `e_{d⁰_i}(P, n)`. -/
noncomputable def err (i : δ) (u : ℝ) : ℝ := lcPoly (D.errA i) (D.errB i) u

/-- `ê(P)`. -/
noncomputable def ehat (u : ℝ) : ℝ := lcPoly D.hatA D.hatB u

/-- `R_full(P) = ∏_i (1 + e_{d⁰_i})/(1 - e_{d⁰_i})`. -/
noncomputable def Rfull (u : ℝ) : ℝ := ∏ i ∈ D.degs, (1 + D.err i u) / (1 - D.err i u)

/-- `M(P) = R_full(P)² (1 - ê(P))^{-n}`. -/
noncomputable def M (u : ℝ) : ℝ := D.Rfull u ^ 2 * ((1 - D.ehat u) ^ D.n)⁻¹

/-- `D_k = ∑_{𝒞 ∈ 𝔓, k_𝒞 = k} 2^{ex*/2} ∏_v (numerator_v)^{1/2}`. -/
noncomputable def Dk [DecidableEq ι] (k : ℕ) (u : ℝ) : ℝ :=
  ∑ c ∈ D.cls.filter (fun c => D.wk c = k),
    (2 : ℝ) ^ ((D.ex c : ℝ) / 2) * ∏ v ∈ D.verts c, Real.sqrt (D.num c v u)

/-- The coefficient `C_k(P)` of `cor:extraction-leaf`(b):
`∑_{𝒞, k_𝒞 = k} 2^{ex*/2} R_full² (1 - ê)^{-k} ∏_v 𝖿(s_v)^{1/2}`, `𝖿 = numerator/(1 - ê)`. -/
noncomputable def Ck [DecidableEq ι] (k : ℕ) (u : ℝ) : ℝ :=
  ∑ c ∈ D.cls.filter (fun c => D.wk c = k),
    (2 : ℝ) ^ ((D.ex c : ℝ) / 2) * D.Rfull u ^ 2 * ((1 - D.ehat u) ^ k)⁻¹ *
      ∏ v ∈ D.verts c, Real.sqrt (D.num c v u / (1 - D.ehat u))

/-- The range: all errors below one (`(S1)` at `P`). -/
def InRange (u : ℝ) : Prop := D.ehat u < 1 ∧ ∀ i ∈ D.degs, D.err i u < 1

variable {D}

theorem err_lt_one {I : Set ℝ} (hR : ∀ u ∈ I, D.InRange u) {u : ℝ} (hu : u ∈ I) {i : δ}
    (hi : i ∈ D.degs) : lcPoly (D.errA i) (D.errB i) u < 1 := (hR u hu).2 i hi

theorem ehat_lt_one {I : Set ℝ} (hR : ∀ u ∈ I, D.InRange u) {u : ℝ} (hu : u ∈ I) :
    lcPoly D.hatA D.hatB u < 1 := (hR u hu).1

theorem num_pos (hD : D.Valid) (c : ι) (v : κ) (u : ℝ) : 0 < D.num c v u := by
  unfold num
  have := lcPoly_nonneg (hD.numA_nonneg c v) (hD.numB_nonneg c v) u
  linarith

theorem Rfull_pos (hD : D.Valid) {u : ℝ} (hu : D.InRange u) : 0 < D.Rfull u := by
  unfold Rfull
  refine prod_pos fun i hi => div_pos ?_ ?_
  · have := lcPoly_nonneg (hD.errA_nonneg i) (hD.errB_nonneg i) u
    unfold err
    linarith
  · have := hu.2 i hi
    linarith

theorem M_pos (hD : D.Valid) {u : ℝ} (hu : D.InRange u) : 0 < D.M u := by
  unfold M
  have h1 : 0 < 1 - D.ehat u := by linarith [hu.1]
  exact mul_pos (pow_pos (Rfull_pos hD hu) 2) (inv_pos.mpr (pow_pos h1 _))

theorem Dk_nonneg [DecidableEq ι] (k : ℕ) (u : ℝ) : 0 ≤ D.Dk k u :=
  sum_nonneg fun c _ => mul_nonneg (by positivity) (prod_nonneg fun v _ => Real.sqrt_nonneg _)

/-- **`lem:logconvex-coefficients`, the factorization**: `C_k = M D_k` (the powers of `1 - ê`
add up to `-k - (n - k) = -n`). -/
theorem Ck_eq [DecidableEq ι] (hD : D.Valid) (k : ℕ) {u : ℝ} (hu : D.ehat u < 1) :
    D.Ck k u = D.M u * D.Dk k u := by
  unfold Ck M Dk
  rw [mul_sum]
  refine sum_congr rfl fun c hc => ?_
  obtain ⟨hc, hck⟩ := mem_filter.mp hc
  have h1 : 0 < 1 - D.ehat u := by linarith
  have hsq : ∏ v ∈ D.verts c, Real.sqrt (D.num c v u / (1 - D.ehat u)) =
      (∏ v ∈ D.verts c, Real.sqrt (D.num c v u)) / (1 - D.ehat u) ^ (D.n - k) := by
    rw [prod_congr rfl fun v _ => Real.sqrt_div (num_pos hD c v u).le (1 - D.ehat u),
      prod_div_distrib, prod_const, hD.card_verts c hc, hck, pow_mul, Real.sq_sqrt h1.le]
  rw [hsq]
  have hk : D.wk c ≤ D.n := hD.wk_le c hc
  rw [hck] at hk
  have hn : (1 - D.ehat u) ^ D.n = (1 - D.ehat u) ^ k * (1 - D.ehat u) ^ (D.n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hn]
  have h2 : (1 - D.ehat u) ^ k ≠ 0 := by positivity
  have h3 : (1 - D.ehat u) ^ (D.n - k) ≠ 0 := by positivity
  field_simp

/-! ### Log-convexity and monotonicity -/

variable {I : Set ℝ}

theorem logConvex_Rfull (hD : D.Valid) (hI : Convex ℝ I) (hR : ∀ u ∈ I, D.InRange u) :
    LcLogConvex I D.Rfull := by
  have h : ∀ i ∈ D.degs, LcLogConvex I (fun u => (1 + D.err i u) / (1 - D.err i u)) := by
    intro i hi
    have h1 := lcPoly_one_add_logConvex hI (hD.errA_nonneg i) (hD.errB_nonneg i)
    have h2 := lc_inv_one_sub hI (lcPoly_logConvex hI (hD.errA_nonneg i) (hD.errB_nonneg i))
      (fun u _ => lcPoly_nonneg (hD.errA_nonneg i) (hD.errB_nonneg i) u)
      (fun u hu => (hR u hu).2 i hi)
    have h3 := lc_mul hI h1 h2
      (fun u _ => by linarith [lcPoly_nonneg (hD.errA_nonneg i) (hD.errB_nonneg i) u])
      (fun u hu => inv_nonneg.mpr (by linarith [err_lt_one hR hu hi]))
    exact lc_congr hI h3 fun u _ => by simp [err, div_eq_mul_inv]
  exact lc_prod hI D.degs h fun i hi u hu => div_nonneg
    (by unfold err; linarith [lcPoly_nonneg (hD.errA_nonneg i) (hD.errB_nonneg i) u])
    (by unfold err; linarith [err_lt_one hR hu hi])

theorem logConvex_M (hD : D.Valid) (hI : Convex ℝ I) (hR : ∀ u ∈ I, D.InRange u) :
    LcLogConvex I D.M := by
  have hRf := logConvex_Rfull hD hI hR
  have hR0 : ∀ u ∈ I, 0 ≤ D.Rfull u := fun u hu => (Rfull_pos hD (hR u hu)).le
  have h1 := lc_mul hI hRf hRf hR0 hR0
  have h2 := lc_inv_one_sub hI (lcPoly_logConvex hI hD.hatA_nonneg hD.hatB_nonneg)
    (fun u _ => lcPoly_nonneg hD.hatA_nonneg hD.hatB_nonneg u) (fun u hu => (hR u hu).1)
  have h2' := lc_rpow hI h2 (fun u hu => inv_nonneg.mpr (by linarith [ehat_lt_one hR hu]))
    (Nat.cast_nonneg D.n)
  have h3 := lc_mul hI h1 h2' (fun u hu => mul_nonneg (hR0 u hu) (hR0 u hu))
    (fun u hu => Real.rpow_nonneg (inv_nonneg.mpr (by linarith [ehat_lt_one hR hu])) _)
  refine lc_congr hI h3 fun u _ => ?_
  unfold M ehat
  rw [Real.rpow_natCast, inv_pow, pow_two]

theorem logConvex_Dk [DecidableEq ι] (hD : D.Valid) (hI : Convex ℝ I) (k : ℕ) :
    LcLogConvex I (D.Dk k) := by
  unfold Dk
  refine lc_sum _ (fun c _ => ?_) (fun c _ u _ =>
    mul_nonneg (by positivity) (prod_nonneg fun v _ => Real.sqrt_nonneg _))
  refine lc_mul hI (lc_const I (by positivity)) ?_ (fun _ _ => by positivity)
    (fun u _ => prod_nonneg fun v _ => Real.sqrt_nonneg _)
  refine lc_prod hI _ (fun v _ => ?_) (fun v _ u _ => Real.sqrt_nonneg _)
  have h := lc_rpow hI (lcPoly_one_add_logConvex hI (hD.numA_nonneg c v) (hD.numB_nonneg c v))
    (fun u _ => (num_pos hD c v u).le) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact lc_congr hI h fun u _ => by rw [Real.sqrt_eq_rpow]; rfl

/-- **`lem:logconvex-coefficients`**: `C_k` is log-convex in `u = log P` on a convex range. -/
theorem logConvex_Ck [DecidableEq ι] (hD : D.Valid) (hI : Convex ℝ I)
    (hR : ∀ u ∈ I, D.InRange u) (k : ℕ) : LcLogConvex I (D.Ck k) := by
  have h := lc_mul hI (logConvex_M hD hI hR) (logConvex_Dk hD hI k)
    (fun u hu => (M_pos hD (hR u hu)).le) (fun u _ => Dk_nonneg k u)
  exact lc_congr hI h fun u hu => (Ck_eq hD k (hR u hu).1).symm

theorem anti_Rfull (hD : D.Valid) (hR : ∀ u ∈ I, D.InRange u) : AntitoneOn D.Rfull I := by
  unfold Rfull
  refine lc_anti_prod _ (fun i hi => ?_) (fun i hi u hu => div_nonneg
    (by unfold err; linarith [lcPoly_nonneg (hD.errA_nonneg i) (hD.errB_nonneg i) u])
    (by unfold err; linarith [err_lt_one hR hu hi]))
  have ha := lcPoly_anti I (hD.errA_nonneg i) (hD.errB_nonneg i)
  have h1 := lc_anti_add (lc_anti_const I 1) ha
  have h2 := lc_anti_inv_one_sub ha (fun u hu => (hR u hu).2 i hi)
  have h3 := lc_anti_mul h1 h2
    (fun u _ => by linarith [lcPoly_nonneg (hD.errA_nonneg i) (hD.errB_nonneg i) u])
    (fun u hu => inv_nonneg.mpr (by linarith [err_lt_one hR hu hi]))
  intro u hu v hv huv
  have := h3 hu hv huv
  simpa [err, div_eq_mul_inv] using this

theorem anti_M (hD : D.Valid) (hR : ∀ u ∈ I, D.InRange u) : AntitoneOn D.M I := by
  have hR0 : ∀ u ∈ I, 0 ≤ D.Rfull u := fun u hu => (Rfull_pos hD (hR u hu)).le
  have hRa := anti_Rfull hD hR
  have h1 := lc_anti_mul hRa hRa hR0 hR0
  have h2 := lc_anti_inv_one_sub (lcPoly_anti I hD.hatA_nonneg hD.hatB_nonneg)
    (fun u hu => (hR u hu).1)
  have h2' := lc_anti_rpow h2 (fun u hu => inv_nonneg.mpr (by linarith [ehat_lt_one hR hu]))
    (Nat.cast_nonneg D.n)
  have h3 := lc_anti_mul h1 h2' (fun u hu => mul_nonneg (hR0 u hu) (hR0 u hu))
    (fun u hu => Real.rpow_nonneg (inv_nonneg.mpr (by linarith [ehat_lt_one hR hu])) _)
  intro u hu v hv huv
  have := h3 hu hv huv
  simp only [Real.rpow_natCast, inv_pow, ← pow_two] at this
  exact this

theorem anti_Dk [DecidableEq ι] (hD : D.Valid) (k : ℕ) : AntitoneOn (D.Dk k) I := by
  unfold Dk
  refine lc_anti_sum _ fun c _ => ?_
  refine lc_anti_mul (lc_anti_const I _) ?_ (fun _ _ => by positivity)
    (fun u _ => prod_nonneg fun v _ => Real.sqrt_nonneg _)
  refine lc_anti_prod _ (fun v _ => ?_) (fun v _ u _ => Real.sqrt_nonneg _)
  intro u _ w _ huw
  exact Real.sqrt_le_sqrt (by
    unfold num
    linarith [lcPoly_anti I (hD.numA_nonneg c v) (hD.numB_nonneg c v) (by assumption)
      (by assumption) huw])

/-- **`lem:logconvex-coefficients`**: `C_k` is nonincreasing in `P` (in `u = log P`). -/
theorem anti_Ck [DecidableEq ι] (hD : D.Valid) (hR : ∀ u ∈ I, D.InRange u) (k : ℕ) :
    AntitoneOn (D.Ck k) I := by
  intro u hu v hv huv
  rw [Ck_eq hD k (hR u hu).1, Ck_eq hD k (hR v hv).1]
  exact mul_le_mul (anti_M hD hR hu hv huv) (anti_Dk hD k hu hv huv) (Dk_nonneg k v)
    (M_pos hD (hR u hu)).le

/-! ### The interpolation -/

/-- **`lem:logconvex-coefficients`, the consequence, in `u = log P`**: if `c_i ≥ C_k(u_i)`, then
`C_k(u_θ) ≤ M(u_θ) (c₀/M(u₀))^{1-θ} (c₁/M(u₁))^θ ≤ c₀^{1-θ} c₁^θ`, `u_θ = (1 - θ) u₀ + θ u₁`. -/
theorem Ck_interp [DecidableEq ι] (hD : D.Valid) (hI : Convex ℝ I) (hR : ∀ u ∈ I, D.InRange u)
    (k : ℕ) {u₀ u₁ θ c₀ c₁ : ℝ} (h₀ : u₀ ∈ I) (h₁ : u₁ ∈ I) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc₀ : D.Ck k u₀ ≤ c₀) (hc₁ : D.Ck k u₁ ≤ c₁) :
    D.Ck k ((1 - θ) * u₀ + θ * u₁) ≤
        D.M ((1 - θ) * u₀ + θ * u₁) * (c₀ / D.M u₀) ^ (1 - θ) * (c₁ / D.M u₁) ^ θ ∧
      D.M ((1 - θ) * u₀ + θ * u₁) * (c₀ / D.M u₀) ^ (1 - θ) * (c₁ / D.M u₁) ^ θ ≤
        c₀ ^ (1 - θ) * c₁ ^ θ := by
  have hm := lc_mem hI h₀ h₁ hθ0 hθ1
  set uθ := (1 - θ) * u₀ + θ * u₁
  have hM0 := M_pos hD (hR u₀ h₀)
  have hM1 := M_pos hD (hR u₁ h₁)
  have hMθ := M_pos hD (hR uθ hm)
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hD0 : D.Dk k u₀ ≤ c₀ / D.M u₀ := by
    rw [le_div_iff₀ hM0, mul_comm, ← Ck_eq hD k (hR u₀ h₀).1]
    exact hc₀
  have hD1 : D.Dk k u₁ ≤ c₁ / D.M u₁ := by
    rw [le_div_iff₀ hM1, mul_comm, ← Ck_eq hD k (hR u₁ h₁).1]
    exact hc₁
  have hc₀0 : 0 ≤ c₀ := le_trans (by
    rw [Ck_eq hD k (hR u₀ h₀).1]
    exact mul_nonneg hM0.le (Dk_nonneg k u₀)) hc₀
  have hc₁0 : 0 ≤ c₁ := le_trans (by
    rw [Ck_eq hD k (hR u₁ h₁).1]
    exact mul_nonneg hM1.le (Dk_nonneg k u₁)) hc₁
  have hX0 : 0 ≤ (c₀ / D.M u₀) ^ (1 - θ) * (c₁ / D.M u₁) ^ θ :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg hc₀0 hM0.le) _)
      (Real.rpow_nonneg (div_nonneg hc₁0 hM1.le) _)
  constructor
  · rw [Ck_eq hD k (hR uθ hm).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hMθ.le
    calc D.Dk k uθ ≤ D.Dk k u₀ ^ (1 - θ) * D.Dk k u₁ ^ θ :=
          logConvex_Dk hD hI k u₀ h₀ u₁ h₁ θ hθ0 hθ1
      _ ≤ (c₀ / D.M u₀) ^ (1 - θ) * (c₁ / D.M u₁) ^ θ :=
          mul_le_mul (Real.rpow_le_rpow (Dk_nonneg k u₀) hD0 h1θ)
            (Real.rpow_le_rpow (Dk_nonneg k u₁) hD1 hθ0)
            (Real.rpow_nonneg (Dk_nonneg k u₁) _)
            (Real.rpow_nonneg (div_nonneg hc₀0 hM0.le) _)
  · have hMc := logConvex_M hD hI hR u₀ h₀ u₁ h₁ θ hθ0 hθ1
    calc D.M uθ * (c₀ / D.M u₀) ^ (1 - θ) * (c₁ / D.M u₁) ^ θ
        = D.M uθ * ((c₀ / D.M u₀) ^ (1 - θ) * (c₁ / D.M u₁) ^ θ) := by ring
      _ ≤ (D.M u₀ ^ (1 - θ) * D.M u₁ ^ θ) * ((c₀ / D.M u₀) ^ (1 - θ) * (c₁ / D.M u₁) ^ θ) :=
          mul_le_mul_of_nonneg_right hMc hX0
      _ = (D.M u₀ * (c₀ / D.M u₀)) ^ (1 - θ) * (D.M u₁ * (c₁ / D.M u₁)) ^ θ := by
          rw [Real.mul_rpow hM0.le (div_nonneg hc₀0 hM0.le),
            Real.mul_rpow hM1.le (div_nonneg hc₁0 hM1.le)]
          ring
      _ = c₀ ^ (1 - θ) * c₁ ^ θ := by
          rw [mul_div_cancel₀ _ hM0.ne', mul_div_cancel₀ _ hM1.ne']

/-- The range is an up-set: the errors are nonincreasing in `P`, so (S1) at `P₀` gives (S1) at
every `P ≥ P₀` (`def:spec:data`). -/
theorem inRange_of_le (hD : D.Valid) {u₀ u : ℝ} (h : D.InRange u₀) (hu : u₀ ≤ u) :
    D.InRange u := by
  refine ⟨lt_of_le_of_lt ?_ h.1, fun i hi => lt_of_le_of_lt ?_ (h.2 i hi)⟩
  · exact lcPoly_anti Set.univ hD.hatA_nonneg hD.hatB_nonneg (Set.mem_univ _) (Set.mem_univ _) hu
  · exact lcPoly_anti Set.univ (hD.errA_nonneg i) (hD.errB_nonneg i) (Set.mem_univ _)
      (Set.mem_univ _) hu

/-- **`lem:logconvex-coefficients`** (`16_extraction.tex`). Fix the partition, its records and
one error pair (`LcData`, `Valid`), and let (S1) hold at `P₀ > 0` (`InRange (log P₀)`). For
`P₀ ≤ Q ≤ P₁`, `P₀ < P₁`, `θ = log(Q/P₀)/log(P₁/P₀)` and `c_i ≥ C_k(P_i)`:
`C_k(Q) ≤ M(Q) (c₀/M(P₀))^{1-θ} (c₁/M(P₁))^θ ≤ c₀^{1-θ} c₁^θ`. The functions of `P` are those of
`u = log P` (`D.Ck k (log P)` is `C_k(P)`). The factorization `C_k = M D_k` is `Ck_eq`; the
log-convexity in `log P` is `logConvex_M`, `logConvex_Dk`, `logConvex_Ck`, and the monotonicity
in `P` is `Ck_antitone_P` (and `anti_M`, `anti_Dk`, `anti_Ck` in `u`). -/
theorem logconvex_coefficients [DecidableEq ι] (hD : D.Valid) (k : ℕ) {P₀ P₁ Q θ c₀ c₁ : ℝ}
    (hP₀ : 0 < P₀) (hP01 : P₀ < P₁) (hQ0 : P₀ ≤ Q) (hQ1 : Q ≤ P₁)
    (hθ : θ = Real.log (Q / P₀) / Real.log (P₁ / P₀)) (hS1 : D.InRange (Real.log P₀))
    (hc₀ : D.Ck k (Real.log P₀) ≤ c₀) (hc₁ : D.Ck k (Real.log P₁) ≤ c₁) :
    D.Ck k (Real.log Q) ≤
        D.M (Real.log Q) * (c₀ / D.M (Real.log P₀)) ^ (1 - θ) *
          (c₁ / D.M (Real.log P₁)) ^ θ ∧
      D.M (Real.log Q) * (c₀ / D.M (Real.log P₀)) ^ (1 - θ) * (c₁ / D.M (Real.log P₁)) ^ θ ≤
        c₀ ^ (1 - θ) * c₁ ^ θ := by
  have hQ : 0 < Q := lt_of_lt_of_le hP₀ hQ0
  have hP₁ : 0 < P₁ := lt_trans hP₀ hP01
  have hlog01 : Real.log P₀ < Real.log P₁ := Real.log_lt_log hP₀ hP01
  have hd : 0 < Real.log P₁ - Real.log P₀ := by linarith
  rw [Real.log_div hQ.ne' hP₀.ne', Real.log_div hP₁.ne' hP₀.ne'] at hθ
  have hQl0 : Real.log P₀ ≤ Real.log Q := Real.log_le_log hP₀ hQ0
  have hQl1 : Real.log Q ≤ Real.log P₁ := Real.log_le_log hQ hQ1
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith) hd.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hd]; linarith
  have hu : (1 - θ) * Real.log P₀ + θ * Real.log P₁ = Real.log Q := by
    rw [hθ]
    field_simp
    ring
  set I := Set.Ici (Real.log P₀)
  have hI : Convex ℝ I := convex_Ici _
  have hR : ∀ u ∈ I, D.InRange u := fun u hu => inRange_of_le hD hS1 hu
  have h := Ck_interp hD hI hR k (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hlog01.le) hθ0 hθ1
    hc₀ hc₁
  rw [hu] at h
  exact h

/-- **`lem:logconvex-coefficients`, monotonicity**: `C_k` is nonincreasing in `P` where (S1)
holds. -/
theorem Ck_antitone_P [DecidableEq ι] (hD : D.Valid) (k : ℕ) {P₀ P P' : ℝ} (hP₀ : 0 < P₀)
    (hS1 : D.InRange (Real.log P₀)) (h0 : P₀ ≤ P) (h1 : P ≤ P') :
    D.Ck k (Real.log P') ≤ D.Ck k (Real.log P) := by
  have hP : 0 < P := lt_of_lt_of_le hP₀ h0
  have hR : ∀ u ∈ Set.Ici (Real.log P₀), D.InRange u := fun u hu => inRange_of_le hD hS1 hu
  exact anti_Ck hD hR k (Set.mem_Ici.mpr (Real.log_le_log hP₀ h0))
    (Set.mem_Ici.mpr ((Real.log_le_log hP₀ h0).trans (Real.log_le_log hP h1)))
    (Real.log_le_log hP h1)

end LcData

/-- Non-vacuity of `LcData.Valid`: one class of witness size `1` with `2 = 2(n - 1)`
non-witness vertices (`n = 2`), all coefficients `1`. -/
theorem lcData_valid_example :
    (⟨{()}, fun _ => 0, fun _ => 1, fun _ => (univ : Finset (Fin 2)), fun _ _ => 1,
      fun _ _ => 1, {()}, fun _ => 1, fun _ => 1, 1, 1, 2⟩ : LcData Unit (Fin 2) Unit).Valid where
  numA_nonneg _ _ := zero_le_one
  numB_nonneg _ _ := zero_le_one
  errA_nonneg _ := zero_le_one
  errB_nonneg _ := zero_le_one
  hatA_nonneg := zero_le_one
  hatB_nonneg := zero_le_one
  wk_le _ _ := by norm_num
  card_verts _ _ := by simp

end Sarkozy.ExtractionK
