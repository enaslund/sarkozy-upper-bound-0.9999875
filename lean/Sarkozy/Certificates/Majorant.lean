module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Admissible majorants (`def:majorant`, `lem:majorant`)

`paper/sections/04_notation.tex`. Every local constant of Part V is a function of `r = p^{-1/2}`,
`q = 1/p` and a few further nonnegative parameters, built from operations that preserve
monotonicity; it is evaluated once, at the endpoint of a box, and the bound then holds at every
larger prime. This file records that calculus.

A box is modelled by any preordered type `Δ` with a greatest element `x⁺`; *admissible* is
`Monotone φ` with `φ ≥ 0`. Then:

* `endpoint_le` is (a): `φ x ≤ φ x⁺`.
* `admissible_add`, `admissible_mul`, `admissible_max`, `admissible_min`, `admissible_sqrt`,
  `admissible_exp`, `admissible_exp_sub_one`, `admissible_log_one_add`,
  `admissible_one_div_one_sub`, `admissible_one_add_div_one_sub`, `admissible_neg_log_one_sub`,
  `admissible_rpow` are the closure rules of (ii); `admissible_comp` is the general rule.
* `monotone_poly` is (i) for polynomials in one nonnegative variable with nonnegative
  coefficients (e.g. the count errors of `lem:extension` as functions of `r`).
* `Small`, `small_admissible`, `small_add`, `small_mul_admissible`, `small_prod_one_add_sub_one`
  are (iii) (`φ/r` admissible, with `r` a positive monotone coordinate).
* `piece_start` is (b); `block_inflation_card`, `block_inflation_sum`, `block_inflation_prod`
  and `antitone_block_inflation` are (c); `matrix_test` is (d); `several_thresholds` is (e).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Majorant

section Admissible

variable {Δ : Type*} [Preorder Δ]

/-- `def:majorant`: a nonnegative nondecreasing function on the box. -/
def Admissible (φ : Δ → ℝ) : Prop := Monotone φ ∧ ∀ x, 0 ≤ φ x

/-- **(a) Endpoint.** An admissible function is bounded by its value at the endpoint. -/
theorem endpoint_le {φ : Δ → ℝ} (h : Admissible φ) {x xp : Δ} (hx : x ≤ xp) : φ x ≤ φ xp :=
  h.1 hx

theorem admissible_const {c : ℝ} (hc : 0 ≤ c) : Admissible (fun _ : Δ => c) :=
  ⟨monotone_const, fun _ => hc⟩

/-- **(ii), general rule.** A monotone map of admissible functions is admissible. -/
theorem admissible_comp {ι : Type*} {D : Set (ι → ℝ)} {F : (ι → ℝ) → ℝ}
    (hF : ∀ y ∈ D, ∀ y' ∈ D, y ≤ y' → F y ≤ F y') (hF0 : ∀ y ∈ D, 0 ≤ F y)
    {φ : ι → Δ → ℝ} (hφ : ∀ i, Monotone (φ i)) (hD : ∀ x, (fun i => φ i x) ∈ D) :
    Admissible (fun x => F (fun i => φ i x)) :=
  ⟨fun _ _ hxy => hF _ (hD _) _ (hD _) fun i => hφ i hxy, fun x => hF0 _ (hD x)⟩

variable {φ ψ : Δ → ℝ}

theorem admissible_add (hφ : Admissible φ) (hψ : Admissible ψ) : Admissible (φ + ψ) :=
  ⟨hφ.1.add hψ.1, fun x => add_nonneg (hφ.2 x) (hψ.2 x)⟩

theorem admissible_mul (hφ : Admissible φ) (hψ : Admissible ψ) : Admissible (φ * ψ) :=
  ⟨fun _ _ hxy => mul_le_mul (hφ.1 hxy) (hψ.1 hxy) (hψ.2 _) (hφ.2 _),
    fun x => mul_nonneg (hφ.2 x) (hψ.2 x)⟩

theorem admissible_max (hφ : Admissible φ) (hψ : Admissible ψ) :
    Admissible (fun x => max (φ x) (ψ x)) :=
  ⟨hφ.1.max hψ.1, fun x => le_max_of_le_left (hφ.2 x)⟩

theorem admissible_min (hφ : Admissible φ) (hψ : Admissible ψ) :
    Admissible (fun x => min (φ x) (ψ x)) :=
  ⟨hφ.1.min hψ.1, fun x => le_min (hφ.2 x) (hψ.2 x)⟩

theorem admissible_sqrt (hφ : Admissible φ) : Admissible (fun x => Real.sqrt (φ x)) :=
  ⟨fun _ _ hxy => Real.sqrt_le_sqrt (hφ.1 hxy), fun _ => Real.sqrt_nonneg _⟩

theorem admissible_exp (hφ : Admissible φ) : Admissible (fun x => Real.exp (φ x)) :=
  ⟨fun _ _ hxy => Real.exp_le_exp.mpr (hφ.1 hxy), fun _ => (Real.exp_pos _).le⟩

theorem admissible_exp_sub_one (hφ : Admissible φ) :
    Admissible (fun x => Real.exp (φ x) - 1) :=
  ⟨fun _ _ hxy => by simp only; linarith [Real.exp_le_exp.mpr (hφ.1 hxy)],
    fun x => by simp only; linarith [Real.add_one_le_exp (φ x), hφ.2 x]⟩

theorem admissible_log_one_add (hφ : Admissible φ) :
    Admissible (fun x => Real.log (1 + φ x)) :=
  ⟨fun a b hab => Real.log_le_log (by linarith [hφ.2 a]) (by linarith [hφ.1 hab]),
    fun x => Real.log_nonneg (by linarith [hφ.2 x])⟩

theorem admissible_one_div_one_sub (hφ : Admissible φ) (h1 : ∀ x, φ x < 1) :
    Admissible (fun x => 1 / (1 - φ x)) :=
  ⟨fun a b hab => one_div_le_one_div_of_le (by linarith [h1 b]) (by linarith [hφ.1 hab]),
    fun x => (one_div_pos.mpr (by linarith [h1 x])).le⟩

theorem admissible_one_add_div_one_sub (hφ : Admissible φ) (h1 : ∀ x, φ x < 1) :
    Admissible (fun x => (1 + φ x) / (1 - φ x)) := by
  have h := admissible_mul (admissible_add (admissible_const (Δ := Δ) zero_le_one) hφ)
    (admissible_one_div_one_sub hφ h1)
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have := h.1 hab
    simp only [Pi.mul_apply, Pi.add_apply] at this
    rwa [mul_one_div, mul_one_div] at this
  · exact div_nonneg (by linarith [hφ.2 x]) (by linarith [h1 x])

theorem admissible_neg_log_one_sub (hφ : Admissible φ) (h1 : ∀ x, φ x < 1) :
    Admissible (fun x => -Real.log (1 - φ x)) :=
  ⟨fun a b hab => by
      simp only [neg_le_neg_iff]
      exact Real.log_le_log (by linarith [h1 b]) (by linarith [hφ.1 hab]),
    fun x => by
      simp only [neg_nonneg]
      exact Real.log_nonpos (by linarith [h1 x]) (by linarith [hφ.2 x])⟩

/-- Powers `φ^ψ` with `φ ≥ 1` and `ψ` admissible. -/
theorem admissible_rpow (hφ : Admissible φ) (h1 : ∀ x, 1 ≤ φ x) (hψ : Admissible ψ) :
    Admissible (fun x => φ x ^ ψ x) :=
  ⟨fun a b hab => (Real.rpow_le_rpow_of_exponent_le (h1 a) (hψ.1 hab)).trans
      (Real.rpow_le_rpow (by linarith [h1 a]) (hφ.1 hab) (hψ.2 b)),
    fun x => Real.rpow_nonneg (by linarith [h1 x]) _⟩

omit [Preorder Δ] in
/-- **(iv).** A function dominated by an admissible one does not change a maximum. -/
theorem max_of_le {φ ψ : Δ → ℝ} (h : ∀ x, ψ x ≤ φ x) : (fun x => max (φ x) (ψ x)) = φ :=
  funext fun x => max_eq_left (h x)

end Admissible

/-- **(i), one variable.** A polynomial with nonnegative coefficients is nondecreasing and
nonnegative on `[0, ∞)`. -/
theorem monotone_poly (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (n : ℕ) {r r' : ℝ} (hr : 0 ≤ r)
    (hrr : r ≤ r') : ∑ k ∈ range n, c k * r ^ k ≤ ∑ k ∈ range n, c k * r' ^ k :=
  sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrr k) (hc k)

/-! ## Small functions -/

section Small

variable {Δ : Type*} [Preorder Δ] (r : Δ → ℝ)

/-- `def:majorant`: `φ` is *small* if `φ / r` is admissible (`r` a positive coordinate). -/
def Small (φ : Δ → ℝ) : Prop := Admissible (fun x => φ x / r x)

variable {r}

/-- **(iii).** With `r` admissible and positive, every small function is admissible. -/
theorem small_admissible (hr : Admissible r) (hr0 : ∀ x, 0 < r x) {φ : Δ → ℝ}
    (hφ : Small r φ) : Admissible φ := by
  have h := admissible_mul hφ hr
  have he : (fun x => φ x / r x) * r = φ := funext fun x => by
    simp only [Pi.mul_apply]; field_simp [(hr0 x).ne']
  rwa [he] at h

theorem small_add {φ ψ : Δ → ℝ} (hφ : Small r φ) (hψ : Small r ψ) : Small r (φ + ψ) := by
  have h := admissible_add hφ hψ
  unfold Small
  convert h using 1
  funext x
  simp only [Pi.add_apply, add_div]

theorem small_mul_admissible {φ h : Δ → ℝ} (hφ : Small r φ) (hh : Admissible h) :
    Small r (h * φ) := by
  have hm := admissible_mul hh hφ
  unfold Small
  convert hm using 1
  funext x
  simp only [Pi.mul_apply, mul_div_assoc]

/-- **(iii), products.** If `φ_i` are small then `∏(1 + φ_i) - 1` is small. -/
theorem small_prod_one_add_sub_one (hr : Admissible r) (hr0 : ∀ x, 0 < r x) {ι : Type*}
    (s : Finset ι) {φ : ι → Δ → ℝ} (hφ : ∀ i ∈ s, Small r (φ i)) :
    Small r (fun x => ∏ i ∈ s, (1 + φ i x) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Small] using admissible_const (Δ := Δ) le_rfl
  | insert a s ha ih =>
    have hs : Small r (fun x => ∏ i ∈ s, (1 + φ i x) - 1) :=
      ih fun i hi => hφ i (mem_insert_of_mem hi)
    have hφa : Small r (φ a) := hφ a (mem_insert_self a s)
    have hP : Admissible (fun x => ∏ i ∈ s, (1 + φ i x)) := by
      have := admissible_add (admissible_const (Δ := Δ) zero_le_one) (small_admissible hr hr0 hs)
      convert this using 1
      funext x; simp
    -- ∏_{insert}(1+φ) - 1 = φ_a * ∏_s(1+φ) + (∏_s(1+φ) - 1)
    have hdecomp : (fun x => ∏ i ∈ insert a s, (1 + φ i x) - 1) =
        (fun x => ∏ i ∈ s, (1 + φ i x)) * φ a + (fun x => ∏ i ∈ s, (1 + φ i x) - 1) := by
      funext x
      simp only [prod_insert ha, Pi.add_apply, Pi.mul_apply]
      ring
    rw [hdecomp]
    exact small_add (small_mul_admissible hφa hP) hs

end Small

/-! ## (b) Piece start, (c) block inflation, (d) matrix tests, (e) several thresholds -/

/-- **(b) Piece start.** If a quantity at the prime `p` is `r^d φ(q, r, l)` with `φ` admissible
on the box `(0, q_X] × (0, r_X] × [0, n_X]` (here: monotone in each argument), then for every
prime `p ≥ X` (so `q ≤ q_X`, `r ≤ r_X`) and `l ≤ n_X` it is at most `p^{-d/2} φ(q_X, r_X, n_X)`. -/
theorem piece_start (φ : ℝ → ℝ → ℝ → ℝ)
    (hmono : ∀ q q' r r' l l', q ≤ q' → r ≤ r' → l ≤ l' → φ q r l ≤ φ q' r' l')
    {X p d qX rX nX l : ℝ} (hX : 1 < X) (hp : X ≤ p) (hqX : 1 / X ≤ qX) (hrX : X ^ (-(1 : ℝ) / 2) ≤ rX)
    (hl : l ≤ nX) :
    (p ^ (-(1 : ℝ) / 2)) ^ d * φ (1 / p) (p ^ (-(1 : ℝ) / 2)) l ≤
      p ^ (-d / 2) * φ qX rX nX := by
  have hp0 : 0 < p := by linarith
  have hX0 : 0 < X := by linarith
  have hq : 1 / p ≤ qX := (one_div_le_one_div_of_le hX0 hp).trans hqX
  have hr : p ^ (-(1 : ℝ) / 2) ≤ rX :=
    (Real.rpow_le_rpow_of_nonpos hX0 hp (by norm_num)).trans hrX
  have hpow : (p ^ (-(1 : ℝ) / 2)) ^ d = p ^ (-d / 2) := by
    rw [← Real.rpow_mul hp0.le]; congr 1; ring
  rw [hpow]
  exact mul_le_mul_of_nonneg_left (hmono _ _ _ _ _ _ hq hr hl) (Real.rpow_nonneg hp0.le _)

/-- **(c) Block inflation, count.** A set of numbers `≥ X > 1` with product at most `e^L` has at
most `L / log X` elements. -/
theorem block_inflation_card {s : Finset ℝ} {X L : ℝ} (hX : 1 < X) (hs : ∀ p ∈ s, X ≤ p)
    (hprod : ∏ p ∈ s, p ≤ Real.exp L) : (s.card : ℝ) ≤ L / Real.log X := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  rw [le_div_iff₀ hlogX]
  have hpos : ∀ p ∈ s, 0 < p := fun p hp => by linarith [hs p hp]
  have hlog : Real.log (∏ p ∈ s, p) = ∑ p ∈ s, Real.log p :=
    Real.log_prod (fun p hp => (hpos p hp).ne')
  have hle : ∑ p ∈ s, Real.log p ≤ L := by
    rw [← hlog]
    calc Real.log (∏ p ∈ s, p) ≤ Real.log (Real.exp L) :=
          Real.log_le_log (prod_pos hpos) hprod
      _ = L := Real.log_exp L
  calc (s.card : ℝ) * Real.log X = ∑ _p ∈ s, Real.log X := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ s, Real.log p :=
        sum_le_sum fun p hp => Real.log_le_log (by linarith) (hs p hp)
    _ ≤ L := hle

/-- **(c) Block inflation, reciprocal sum.** `∑_{p∈B} 1/p ≤ L / (X log X)`. -/
theorem block_inflation_sum {s : Finset ℝ} {X L : ℝ} (hX : 1 < X) (hs : ∀ p ∈ s, X ≤ p)
    (hprod : ∏ p ∈ s, p ≤ Real.exp L) : ∑ p ∈ s, 1 / p ≤ L / (X * Real.log X) := by
  have hX0 : 0 < X := by linarith
  have hcard := block_inflation_card hX hs hprod
  calc ∑ p ∈ s, 1 / p ≤ ∑ _p ∈ s, 1 / X :=
        sum_le_sum fun p hp => one_div_le_one_div_of_le hX0 (hs p hp)
    _ = (s.card : ℝ) / X := by rw [sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ (L / Real.log X) / X := div_le_div_of_nonneg_right hcard hX0.le
    _ = L / (X * Real.log X) := by rw [div_div, mul_comm]

/-- **(c) Block inflation, product.** `∏_{p∈B} (1 + c/p) ≤ exp(cL / (X log X))` for `c ≥ 0`. -/
theorem block_inflation_prod {s : Finset ℝ} {X L c : ℝ} (hX : 1 < X) (hs : ∀ p ∈ s, X ≤ p)
    (hprod : ∏ p ∈ s, p ≤ Real.exp L) (hc : 0 ≤ c) :
    ∏ p ∈ s, (1 + c / p) ≤ Real.exp (c * L / (X * Real.log X)) := by
  have hpos : ∀ p ∈ s, 0 < p := fun p hp => by linarith [hs p hp]
  calc ∏ p ∈ s, (1 + c / p) ≤ ∏ p ∈ s, Real.exp (c / p) :=
        prod_le_prod₀ (fun p hp => by have := div_nonneg hc (hpos p hp).le; linarith)
          (fun p _ => by linarith [Real.add_one_le_exp (c / p)])
    _ = Real.exp (∑ p ∈ s, c / p) := (Real.exp_sum s _).symm
    _ ≤ Real.exp (c * L / (X * Real.log X)) := by
        apply Real.exp_le_exp.mpr
        have h := block_inflation_sum hX hs hprod
        calc ∑ p ∈ s, c / p = c * ∑ p ∈ s, 1 / p := by
              rw [mul_sum]; exact sum_congr rfl fun p _ => by ring
          _ ≤ c * (L / (X * Real.log X)) := mul_le_mul_of_nonneg_left h hc
          _ = c * L / (X * Real.log X) := by ring

/-- **(c)** `X ↦ exp(cL/(X log X))` is nonincreasing on `(1, ∞)` for `cL ≥ 0`. -/
theorem antitone_block_inflation {c L : ℝ} (hcL : 0 ≤ c * L) {X X' : ℝ} (hX : 1 < X)
    (hXX : X ≤ X') : Real.exp (c * L / (X' * Real.log X')) ≤ Real.exp (c * L / (X * Real.log X)) := by
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hden : 0 < X * Real.log X := mul_pos (by linarith) hlog
  have hden' : X * Real.log X ≤ X' * Real.log X' :=
    mul_le_mul hXX (Real.log_le_log (by linarith) hXX) hlog.le (by linarith)
  exact div_le_div_of_nonneg_left hcL hden hden'

/-- **(d) Matrix tests.** If `M₀ + ∑ c_i(x⁺) E_i ⪰ 0` with `E_i ⪰ 0` and `c_i(x) ≥ c_i(x⁺)`, then
`M₀ + ∑ c_i(x) E_i ⪰ 0`. -/
theorem matrix_test {n ι : Type*} [Fintype n] [DecidableEq n] (s : Finset ι)
    (M₀ : Matrix n n ℝ) (E : ι → Matrix n n ℝ) (hE : ∀ i ∈ s, (E i).PosSemidef)
    (c cp : ι → ℝ) (hc : ∀ i ∈ s, cp i ≤ c i) (hp : (M₀ + ∑ i ∈ s, cp i • E i).PosSemidef) :
    (M₀ + ∑ i ∈ s, c i • E i).PosSemidef := by
  have hsplit : M₀ + ∑ i ∈ s, c i • E i =
      (M₀ + ∑ i ∈ s, cp i • E i) + ∑ i ∈ s, (c i - cp i) • E i := by
    rw [add_assoc, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun i _ => by rw [← add_smul]; congr 1; ring
  rw [hsplit]
  refine hp.add ?_
  exact Matrix.posSemidef_sum s fun i hi => (hE i hi).smul (by linarith [hc i hi])

/-- **(e) Several thresholds.** If a statement holds with `g_s` at every prime `p ≥ y_s`, then it
holds with `min {g_s : y_s ≤ y}` at every `p ≥ y`. (The minimum is attained, so the paper's
monotonicity of the statement in `g` is not needed in this form.) -/
theorem several_thresholds {σ : Type*} (s : Finset σ) (A : ℕ → ℝ → Prop) (y g : σ → ℝ)
    (hs : ∀ t ∈ s, ∀ p : ℕ, y t ≤ p → A p (g t)) (Y : ℝ) (t₀ : σ) (ht₀ : t₀ ∈ s)
    (hY : y t₀ ≤ Y) :
    ∀ p : ℕ, Y ≤ p → A p ((s.filter fun t => y t ≤ Y).inf' ⟨t₀, mem_filter.mpr ⟨ht₀, hY⟩⟩ g) := by
  intro p hp
  obtain ⟨t, ht, hmin⟩ := (s.filter fun t => y t ≤ Y).exists_mem_eq_inf'
    ⟨t₀, mem_filter.mpr ⟨ht₀, hY⟩⟩ g
  rw [hmin]
  have ht' := mem_filter.mp ht
  exact hs t ht'.1 p (ht'.2.trans hp)

end Sarkozy.Majorant
