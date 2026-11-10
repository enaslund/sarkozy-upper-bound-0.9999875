module

public import Sarkozy.OpsFeature.Edge03
public import Sarkozy.MiddleRecords.ActualFeaturesNorms

@[expose] public section

/-!
# The exact conditional expectation `E[f(x₀) | x₁, x₂]` and the one-prime edge `03`
(`lem:oct24:feature-block`(a), proof Step 3, first part)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`, proof Step 3: for a mean-zero `f`
and distinct `y, z`, with `s = χ(z - y)`,
`E_{m₀}[f(x₀) | x₁ = y, x₂ = z] = N_f(y, z)/((p - 3)(p - 4 - 2s))`,
`N_f = (p - 5 - s) Σ_z - Σ_y - Ω - (p - 6)(1 + s) f(y) - (p - 5) f(z)`
(`four_sum_oldW_f`, `condT_explicit`), with `Σ_z = ∑_u χ(z - u) f(u)` (`= -p P f(z)`) and
`Ω(y, z) = ∑_u χ(z - u) χ(y - u) f(u)` (`= p W f(y, z)`, `-p` times MiddleRecords' `A3op`). This is
the paper's formula.

Using `s² = 1`, `T f = A(y) + B(z) + R(y, z)` (`condT_decomp`) with a function `A` of `y` alone, a
function `B` of `z` alone, and the remainder
`R = sΣ_z/((p-3)(p-2)) - 2sΣ_y c - (p-4+2s)Ω c - s f(y)/(p-3) - 2(p-5) s f(z) c`,
`c = 1/((p-3)(p-6)(p-2))`, whose norm in `L²(m₁₂)` is at most
`1/(p-3) + 2(p-5)c + 2√p/((p-6)(p-2)) ≤ ϱ₀₃(p)` times the uniform norm of `f`
(`norm_remainder_le`: `‖s f(y)‖ = ‖f‖`, `‖Σ_z‖ = √p ‖f‖` by the Paley identity, `‖Ω‖ ≤ √p ‖f‖` by
`norm_A3_sq_le`). A function in the one-prime `𝒦₁₂` annihilates `A` and `B`, so
**`hprime_proved`**: the field `hprime` of `Edge03Inputs` is a theorem.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.MiddleRecords Sarkozy.Mixing Sarkozy.TraceMixing Sarkozy.EnvelopeSteps
  Sarkozy.Envelopes


/-! ## Numerical bounds for `p ≥ 2²⁴` (`s = √p`) -/

theorem num_s_le {x s : ℝ} (hs : (2 : ℝ) ^ 12 ≤ s) (hx : s * s = x) : s ≤ x / 4096 := by
  rw [le_div_iff₀ (by norm_num)]; nlinarith

theorem num_k1 {x s : ℝ} (hx : (2 : ℝ) ^ 24 ≤ x) (hsx : s ≤ x / 4096) :
    (x - 4) * (1 / ((x - 3) * (x - 6) * (x - 2))) * s ≤ 1 / (10 * x) := by
  have h3 : 0 < x - 3 := by linarith
  have h6 : 0 < x - 6 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h4 : 0 ≤ x - 4 := by linarith
  have hx0 : 0 < x := by linarith
  have e : (x - 4) * (1 / ((x - 3) * (x - 6) * (x - 2))) * s =
      (x - 4) * s / ((x - 3) * (x - 6) * (x - 2)) := by ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have hm : (x - 4) * s * (10 * x) ≤ (x - 4) * (x / 4096) * (10 * x) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsx h4
  have hp : (x - 4) * (x / 4096) * (10 * x) ≤ 1 * ((x - 3) * (x - 6) * (x - 2)) := by
    nlinarith [mul_nonneg (mul_nonneg hx0.le hx0.le) (sub_nonneg.2 hx)]
  linarith

theorem num_k2 {x : ℝ} (hx : (2 : ℝ) ^ 24 ≤ x) : 1 / (x - 3) ≤ 3 / (2 * x) := by
  have h3 : 0 < x - 3 := by linarith
  rw [div_le_div_iff₀ h3 (by linarith)]; nlinarith

theorem num_k3 {x s : ℝ} (hx : (2 : ℝ) ^ 24 ≤ x) (hsx : s ≤ x / 4096) :
    1 / ((x - 1) * (x - 2)) * s ≤ 1 / (10 * x) := by
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have hx0 : 0 < x := by linarith
  rw [show 1 / ((x - 1) * (x - 2)) * s = s / ((x - 1) * (x - 2)) by ring,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have hm : s * (10 * x) ≤ (x / 4096) * (10 * x) := mul_le_mul_of_nonneg_right hsx (by positivity)
  nlinarith

theorem num_k4 {x : ℝ} (hx : (2 : ℝ) ^ 24 ≤ x) :
    |1 / (x - 1) - (x - 5) * (x - 4) * (1 / ((x - 3) * (x - 6) * (x - 2)))| ≤ 1 / (10 * x) := by
  have h1 : 0 < x - 1 := by linarith
  have h3 : 0 < x - 3 := by linarith
  have h6 : 0 < x - 6 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have hx0 : 0 < x := by linarith
  have e : 1 / (x - 1) - (x - 5) * (x - 4) * (1 / ((x - 3) * (x - 6) * (x - 2))) =
      (-x ^ 2 + 7 * x - 16) / ((x - 1) * (x - 3) * (x - 6) * (x - 2)) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (x - 1) * (x - 3) * (x - 6) * (x - 2)),
    abs_of_neg (by nlinarith), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hx0.le hx0.le) (sub_nonneg.2 hx),
    mul_nonneg (mul_nonneg (mul_nonneg hx0.le hx0.le) hx0.le) (sub_nonneg.2 hx)]

theorem num_k5 {x s : ℝ} (hx : (2 : ℝ) ^ 24 ≤ x) (hsx : s ≤ x / 4096) :
    1 / (x - 3) + 2 / ((x - 3) * (x - 6)) + 2 * s / ((x - 6) * (x - 2)) ≤ 17 / (10 * x) := by
  have h3 : 0 < x - 3 := by linarith
  have h6 : 0 < x - 6 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have hx0 : 0 < x := by linarith
  have b1 : 1 / (x - 3) ≤ 3 / (2 * x) := num_k2 hx
  have b2 : 2 / ((x - 3) * (x - 6)) ≤ 1 / (10 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have b3 : 2 * s / ((x - 6) * (x - 2)) ≤ 1 / (10 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm : 2 * s * (10 * x) ≤ 2 * (x / 4096) * (10 * x) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    nlinarith
  have : 3 / (2 * x) + 1 / (10 * x) + 1 / (10 * x) = 17 / (10 * x) := by field_simp; ring
  linarith

section Prime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-- `Σ_z = ∑_u χ(z - u) f(u)` (`= -p P f(z)`). -/
noncomputable def sigZ (f : F → ℝ) (z : F) : ℝ := ∑ u, (χ (z - u) : ℝ) * f u

/-- `Ω(y, z) = ∑_u χ(z - u) χ(y - u) f(u)` (`= p W f(y, z)`). -/
noncomputable def omg (f : F → ℝ) (y z : F) : ℝ := ∑ u, (χ (z - u) : ℝ) * (χ (y - u) : ℝ) * f u

theorem chi_sq_of_ne {y z : F} (h : y ≠ z) : (χ (z - y) : ℝ) ^ 2 = 1 := chi_sq_one h

/-- **The numerator `N_f`** (`4 ∑_u oldW(u, y, z) f(u)`) for mean-zero `f`, `y ≠ z`. -/
theorem four_sum_oldW_f (h3 : Fintype.card F % 4 = 3) (f : F → ℝ) (hf : ∑ u, f u = 0)
    {y z : F} (hyz : y ≠ z) :
    4 * ∑ u, oldW u y z * f u =
      (qF - 5 - (χ (z - y) : ℝ)) * sigZ f z - sigZ f y - omg f y z -
        (qF - 6) * (1 + (χ (z - y) : ℝ)) * f y - (qF - 5) * f z := by
  set s : ℝ := (χ (z - y) : ℝ) with hs
  set G : F → ℝ := fun u =>
    (1 + (χ (z - u) : ℝ)) * (qF - 5 - (χ (y - u) : ℝ) - s) / 4 * f u with hG
  have e : ∀ u, oldW u y z * f u = if u ≠ y ∧ u ≠ z then G u else 0 := by
    intro u
    unfold oldW
    by_cases h : u ≠ y ∧ u ≠ z
    · rw [ite_eq_left (show u ≠ y ∧ u ≠ z ∧ y ≠ z from ⟨h.1, h.2, hyz⟩), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩), ite_eq_right h, zero_mul]
  simp only [e]
  rw [sum_ne_ne hyz G]
  have hsum : ∑ u, G u = ((qF - 5 - s) * sigZ f z - sigZ f y - omg f y z) / 4 := by
    have e2 : ∀ u, G u = ((qF - 5 - s) * f u + (qF - 5 - s) * ((χ (z - u) : ℝ) * f u) -
        (χ (y - u) : ℝ) * f u - (χ (z - u) : ℝ) * (χ (y - u) : ℝ) * f u) / 4 := by
      intro u; simp only [hG]; ring
    simp only [e2, ← sum_div, sum_sub_distrib, sum_add_distrib, ← mul_sum, hf, mul_zero,
      zero_add, sigZ, omg]
  have hGy : G y = (1 + s) * (qF - 5 - s) / 4 * f y := by
    simp only [hG, sub_self, quadraticChar_zero, Int.cast_zero, sub_zero, ← hs]
  have hGz : G z = (qF - 5) / 4 * f z := by
    simp only [hG, sub_self, quadraticChar_zero, Int.cast_zero, add_zero]
    rw [chi_swap h3 y z, Int.cast_neg, ← hs]
    ring
  rw [hsum, hGy, hGz]
  have hs2 : s ^ 2 = 1 := chi_sq_of_ne hyz
  linear_combination f y * hs2

/-- The total conditional weight of the pair `(y, z)`. -/
theorem sum_oldW_pair (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {y z : F}
    (hyz : y ≠ z) :
    ∑ u, oldW u y z = (qF - 3) * (qF - 4 - 2 * (χ (z - y) : ℝ)) / 4 :=
  sum_oldW_x0 hF h3 hyz

/-- **The exact conditional expectation** `T f(y, z) = N_f/((p - 3)(p - 4 - 2s))`. -/
theorem condT_explicit (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) {y z : F} (hyz : y ≠ z) :
    (condT *ᵥ f) (y, z) = (4 * ∑ u, oldW u y z * f u) /
      ((qF - 3) * (qF - 4 - 2 * (χ (z - y) : ℝ))) := by
  have hS := sum_oldW_pair hF h3 hyz
  have hb := (aY_bounds z y)
  have hpos : 0 < (qF - 3) * (qF - 4 - 2 * (χ (z - y) : ℝ)) := by
    have : (χ (z - y) : ℝ) ≤ 1 := by
      have := chi_sq_le_one (z - y); nlinarith
    have : 0 < qF - 3 := by linarith
    have : 0 < qF - 4 - 2 * (χ (z - y) : ℝ) := by linarith
    positivity
  have hS0 : ∑ u, oldW u y z ≠ 0 := by rw [hS]; positivity
  simp only [mulVec, dotProduct, condT, hS0, ↓reduceIte, div_mul_eq_mul_div]
  rw [← sum_div, hS]
  field_simp

/-- `c = 1/((p - 3)(p - 6)(p - 2))`. -/
noncomputable def cT : ℝ := 1 / ((qF - 3) * (qF - 6) * (qF - 2))

/-- The part of `T f` depending on `y` alone. -/
noncomputable def partA (f : F → ℝ) (y : F) : ℝ :=
  -(qF - 4) * cT (F := F) * sigZ f y - f y / (qF - 3)

/-- The part of `T f` depending on `z` alone. -/
noncomputable def partB (f : F → ℝ) (z : F) : ℝ :=
  sigZ f z / (qF - 2) - (qF - 5) * (qF - 4) * cT (F := F) * f z

/-- **The remainder `R`** of `T f` after the functions of `y` and of `z`. -/
noncomputable def partR (f : F → ℝ) (c : F × F) : ℝ :=
  (χ (c.2 - c.1) : ℝ) * sigZ f c.2 / ((qF - 3) * (qF - 2)) -
    2 * cT (F := F) * ((χ (c.2 - c.1) : ℝ) * sigZ f c.1) -
    (qF - 4 + 2 * (χ (c.2 - c.1) : ℝ)) * cT (F := F) * omg f c.1 c.2 -
    (χ (c.2 - c.1) : ℝ) * f c.1 / (qF - 3) -
    2 * (qF - 5) * cT (F := F) * ((χ (c.2 - c.1) : ℝ) * f c.2)

/-- **`T f = A(y) + B(z) + R(y, z)`** off the diagonal. -/
theorem condT_decomp (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ u, f u = 0) {y z : F} (hyz : y ≠ z) :
    (condT *ᵥ f) (y, z) = partA f y + partB f z + partR f (y, z) := by
  rw [condT_explicit hF h3 h7 f hyz, four_sum_oldW_f h3 f hf hyz]
  simp only [partA, partB, partR, cT]
  have h3' : qF - 3 ≠ 0 := by intro h; linarith
  have h6 : qF - 6 ≠ 0 := by intro h; linarith
  have h2 : qF - 2 ≠ 0 := by intro h; linarith
  have h4 : qF - 4 - 2 * 1 ≠ 0 := by intro h; linarith
  have h4' : qF - 4 - 2 * (-1) ≠ 0 := by intro h; linarith
  set X := qF with hX
  set S1 := sigZ f z
  set S2 := sigZ f y
  set Om := omg f y z
  have e6 : X - 4 - 2 * 1 = X - 6 := by ring
  have e2 : X - 4 - 2 * (-1) = X - 2 := by ring
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr hyz.symm) with hs | hs
  · rw [hs]
    push_cast
    rw [e6]
    field_simp
    ring
  · rw [hs]
    push_cast
    rw [e2]
    field_simp
    ring

/-! ## The norms of the pieces in `L²(m₁₂)` -/

/-- A pointwise-bounded multiplier: `‖κ G‖ ≤ M ‖G‖`. -/
theorem wNorm_mul_le {B : Type*} [Fintype B] {β : B → ℝ} (hβ : ∀ b, 0 ≤ β b) {κ G : B → ℝ}
    {M : ℝ} (hM : 0 ≤ M) (hκ : ∀ b, |κ b| ≤ M) :
    wNorm β (fun b => κ b * G b) ≤ M * wNorm β G := by
  apply wNorm_le_of_sq_le hM _ (wNorm_nonneg _ _)
  rw [wNorm_sq hβ, mul_sum]
  refine sum_le_sum fun b _ => ?_
  have h1 : κ b ^ 2 ≤ M ^ 2 := by
    have := hκ b
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have := mul_le_mul_of_nonneg_right h1 (mul_nonneg (hβ b) (sq_nonneg (G b)))
  nlinarith [this]

theorem wNorm_neg {B : Type*} [Fintype B] (β : B → ℝ) (G : B → ℝ) :
    wNorm β (fun b => -G b) = wNorm β G := by
  unfold wNorm; simp only [neg_sq]

theorem wNorm_sub_le {B : Type*} [Fintype B] {β : B → ℝ} (hβ : ∀ b, 0 ≤ β b) (G H : B → ℝ) :
    wNorm β (fun b => G b - H b) ≤ wNorm β G + wNorm β H := by
  have := wNorm_add_le hβ G (fun b => -H b)
  rw [wNorm_neg] at this
  have e : (fun b => G b - H b) = G + fun b => -H b := by
    funext b; simp [sub_eq_add_neg]
  rw [e]
  exact this

/-- `χ(z - y)²` is invisible in `L²(m₁₂)` (the diagonal has no mass). -/
theorem sum_pairLaw_chi_sq (G : F × F → ℝ) :
    ∑ c : F × F, pairLaw c * ((χ (c.2 - c.1) : ℝ) * G c) ^ 2 = ∑ c, pairLaw c * G c ^ 2 := by
  refine sum_congr rfl fun c _ => ?_
  by_cases h : c.1 = c.2
  · have : pairLaw c = 0 := by
      unfold pairLaw; rw [h]; exact (m_diag c.2).1
    rw [this, zero_mul, zero_mul]
  · rw [mul_pow, chi_sq_one h, one_mul]

theorem sum_pairLaw_fst (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (H : F → ℝ) : ∑ c : F × F, pairLaw c * H c.1 ^ 2 = (1 / qF) * ∑ y, H y ^ 2 := by
  simp only [pairLaw, Fintype.sum_prod_type]
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_mul, sum_m12_right hF h3 h7]

theorem sum_pairLaw_snd (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (H : F → ℝ) : ∑ c : F × F, pairLaw c * H c.2 ^ 2 = (1 / qF) * ∑ z, H z ^ 2 := by
  rw [Fintype.sum_prod_type, sum_comm, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  simp only [pairLaw]
  rw [← sum_mul, sum_m12_left hF h3 h7]

/-- **The Paley identity** `∑_z Σ_z² = p ∑ f²` for mean-zero `f`. -/
theorem sum_sigZ_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (f : F → ℝ)
    (hf : ∑ u, f u = 0) : ∑ z, sigZ f z ^ 2 = qF * ∑ u, f u ^ 2 := by
  have e3 : ∀ z, sigZ f z ^ 2 = ∑ u, ∑ u', f u * f u' * ((χ (u - z) : ℝ) * (χ (u' - z) : ℝ)) := by
    intro z
    simp only [sigZ, sq, sum_mul_sum]
    refine sum_congr rfl fun u _ => sum_congr rfl fun u' _ => ?_
    rw [chi_swap h3 z u, chi_swap h3 z u']
    push_cast
    ring
  simp only [e3]
  rw [sum_comm]
  have e4 : ∀ u, ∑ z, ∑ u', f u * f u' * ((χ (u - z) : ℝ) * (χ (u' - z) : ℝ)) =
      ∑ u', f u * f u' * ((if u = u' then qF else 0) - 1) := by
    intro u
    rw [sum_comm]
    refine sum_congr rfl fun u' _ => ?_
    rw [← mul_sum, sum_chi_mul_chi_R hF h3]
  have e5 : ∀ u, ∑ u', f u * f u' * ((if u = u' then qF else 0) - 1) = qF * f u ^ 2 := by
    intro u
    have h1 : ∑ u', f u * f u' * ((if u = u' then qF else 0) - 1) =
        ∑ u', (if u = u' then qF * f u * f u' else 0) - f u * ∑ u', f u' := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun u' _ => by split_ifs <;> ring
    rw [h1, sum_ite_eq, hf]
    simp only [mem_univ, ↓reduceIte]
    ring
  rw [sum_congr rfl fun u _ => (e4 u).trans (e5 u), ← mul_sum]

/-- `Ω = -p A₃` for mean-zero `f`, and `‖Ω‖² ≤ ∑ f²` in `L²(m₁₂)` (`norm_A3_sq_le`). -/
theorem sum_pairLaw_omg_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ u, f u = 0) :
    ∑ c : F × F, pairLaw c * omg f c.1 c.2 ^ 2 ≤ ∑ u, f u ^ 2 := by
  have hq : 0 < qF := by linarith
  have e : ∀ y z, omg f y z = -qF * A3op f y z := by
    intro y z
    rw [A3op_meanZero f hf]
    have e1 : omg f y z = ∑ s, (χ (s - y) : ℝ) * (χ (s - z) : ℝ) * f s := by
      simp only [omg]
      refine sum_congr rfl fun u _ => ?_
      rw [chi_swap h3 z u, chi_swap h3 y u]
      push_cast
      ring
    rw [e1, mul_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  have h := norm_A3_sq_le hF h3 h7 f hf
  have e2 : ∑ c : F × F, pairLaw c * omg f c.1 c.2 ^ 2 =
      qF ^ 2 * ∑ a, ∑ b, m12 a b * A3op f a b ^ 2 := by
    simp only [pairLaw, e, Fintype.sum_prod_type, mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [e2]
  unfold unifNormSq at h
  calc qF ^ 2 * ∑ a, ∑ b, m12 a b * A3op f a b ^ 2 ≤ qF ^ 2 * (qF⁻¹ * (qF⁻¹ * ∑ z, f z ^ 2)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = ∑ u, f u ^ 2 := by field_simp

/-- **`ϱ₀₃` at a prime**: `ϱ₀₃(1/p, p^{-1/2}) = 1/(p-3) + 2/((p-3)(p-6)) + 2√p/((p-6)(p-2))`. -/
theorem rho03_prime_eq {x : ℝ} (hx : 7 ≤ x) :
    rho03 (1 / x) (1 / Real.sqrt x) =
      1 / (x - 3) + 2 / ((x - 3) * (x - 6)) + 2 * Real.sqrt x / ((x - 6) * (x - 2)) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = s ^ 2 :=
    ⟨Real.sqrt x, Real.sqrt_pos.2 hx0, (Real.sq_sqrt hx0.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  have h3 : s ^ 2 - 3 ≠ 0 := by intro h; linarith
  have h6 : s ^ 2 - 6 ≠ 0 := by intro h; linarith
  have h2 : s ^ 2 - 2 ≠ 0 := by intro h; linarith
  have h3' : 1 - 3 * (1 / s ^ 2) ≠ 0 := by
    rw [show 1 - 3 * (1 / s ^ 2) = (s ^ 2 - 3) / s ^ 2 by field_simp]
    exact div_ne_zero h3 (by positivity)
  have h6' : 1 - 6 * (1 / s ^ 2) ≠ 0 := by
    rw [show 1 - 6 * (1 / s ^ 2) = (s ^ 2 - 6) / s ^ 2 by field_simp]
    exact div_ne_zero h6 (by positivity)
  have h2' : 1 - 2 * (1 / s ^ 2) ≠ 0 := by
    rw [show 1 - 2 * (1 / s ^ 2) = (s ^ 2 - 2) / s ^ 2 by field_simp]
    exact div_ne_zero h2 (by positivity)
  unfold rho03
  field_simp

/-- **The norm of the remainder**: `‖R‖ ≤ ϱ₀₃(p) ‖f‖` in `L²(m₁₂)`, `‖f‖` uniform. -/
theorem norm_remainder_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ u, f u = 0) :
    wNorm pairLaw (partR f) ≤
      rho03 (1 / qF) (1 / Real.sqrt qF) * Real.sqrt ((1 / qF) * ∑ u, f u ^ 2) := by
  have hβ : ∀ c : F × F, 0 ≤ pairLaw c := pairLaw_nonneg hF h3 h7
  have hq : 0 < qF := by linarith
  have h3p : 0 < qF - 3 := by linarith
  have h6p : 0 < qF - 6 := by linarith
  have h2p : 0 < qF - 2 := by linarith
  have hc0 : 0 ≤ cT (F := F) := by unfold cT; positivity
  set N := Real.sqrt ((1 / qF) * ∑ u, f u ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hsq : Real.sqrt (∑ u, f u ^ 2) = Real.sqrt qF * N := by
    rw [hN, ← Real.sqrt_mul hq.le]
    congr 1
    field_simp
  have hchi : ∀ c : F × F, |(χ (c.2 - c.1) : ℝ)| ≤ 1 := fun c => by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_one.mpr (chi_sq_le_one _)
  -- the five pieces
  have n1 : wNorm pairLaw (fun c : F × F => (χ (c.2 - c.1) : ℝ) * sigZ f c.2) =
      Real.sqrt qF * N := by
    unfold wNorm
    rw [sum_pairLaw_chi_sq (fun c => sigZ f c.2), sum_pairLaw_snd hF h3 h7 (sigZ f),
      sum_sigZ_sq hF h3 f hf, ← hsq]
    congr 1; field_simp
  have n2 : wNorm pairLaw (fun c : F × F => (χ (c.2 - c.1) : ℝ) * sigZ f c.1) =
      Real.sqrt qF * N := by
    unfold wNorm
    rw [sum_pairLaw_chi_sq (fun c => sigZ f c.1), sum_pairLaw_fst hF h3 h7 (sigZ f),
      sum_sigZ_sq hF h3 f hf, ← hsq]
    congr 1; field_simp
  have n3 : wNorm pairLaw (fun c : F × F => omg f c.1 c.2) ≤ Real.sqrt qF * N := by
    rw [← hsq]
    exact Real.sqrt_le_sqrt (sum_pairLaw_omg_sq hF h3 h7 f hf)
  have n4 : wNorm pairLaw (fun c : F × F => (χ (c.2 - c.1) : ℝ) * f c.1) = N := by
    unfold wNorm
    rw [sum_pairLaw_chi_sq (fun c => f c.1), sum_pairLaw_fst hF h3 h7 f]
  have n5 : wNorm pairLaw (fun c : F × F => (χ (c.2 - c.1) : ℝ) * f c.2) = N := by
    unfold wNorm
    rw [sum_pairLaw_chi_sq (fun c => f c.2), sum_pairLaw_snd hF h3 h7 f]
  -- Minkowski
  set g1 : F × F → ℝ := fun c => (χ (c.2 - c.1) : ℝ) * sigZ f c.2 / ((qF - 3) * (qF - 2))
  set g2 : F × F → ℝ := fun c => 2 * cT (F := F) * ((χ (c.2 - c.1) : ℝ) * sigZ f c.1)
  set g3 : F × F → ℝ := fun c => (qF - 4 + 2 * (χ (c.2 - c.1) : ℝ)) * cT (F := F) * omg f c.1 c.2
  set g4 : F × F → ℝ := fun c => (χ (c.2 - c.1) : ℝ) * f c.1 / (qF - 3)
  set g5 : F × F → ℝ := fun c => 2 * (qF - 5) * cT (F := F) * ((χ (c.2 - c.1) : ℝ) * f c.2)
  have hR : partR f = fun c => (((g1 c - g2 c) - g3 c) - g4 c) - g5 c := rfl
  have m1 : wNorm pairLaw g1 ≤ 1 / ((qF - 3) * (qF - 2)) * (Real.sqrt qF * N) := by
    rw [← n1]
    have := wNorm_mul_le hβ (G := fun c : F × F => (χ (c.2 - c.1) : ℝ) * sigZ f c.2)
      (κ := fun _ => 1 / ((qF - 3) * (qF - 2))) (M := 1 / ((qF - 3) * (qF - 2)))
      (by positivity) (fun c => by rw [abs_of_nonneg (by positivity)])
    refine le_of_eq_of_le ?_ this
    congr 1; funext c; simp only [g1]; ring
  have m2 : wNorm pairLaw g2 ≤ 2 * cT (F := F) * (Real.sqrt qF * N) := by
    rw [← n2]
    exact wNorm_mul_le hβ (G := fun c : F × F => (χ (c.2 - c.1) : ℝ) * sigZ f c.1)
      (κ := fun _ => 2 * cT (F := F)) (M := 2 * cT (F := F)) (by positivity)
      (fun c => by rw [abs_of_nonneg (by positivity)])
  have m3 : wNorm pairLaw g3 ≤ (qF - 2) * cT (F := F) * (Real.sqrt qF * N) := by
    have h := wNorm_mul_le hβ (G := fun c : F × F => omg f c.1 c.2)
      (κ := fun c => (qF - 4 + 2 * (χ (c.2 - c.1) : ℝ)) * cT (F := F))
      (M := (qF - 2) * cT (F := F)) (by positivity) (fun c => by
        rw [abs_mul, abs_of_nonneg hc0]
        apply mul_le_mul_of_nonneg_right _ hc0
        have := abs_le.mp (hchi c)
        rw [abs_le]; constructor <;> linarith)
    exact h.trans (mul_le_mul_of_nonneg_left n3 (by positivity))
  have m4 : wNorm pairLaw g4 ≤ 1 / (qF - 3) * N := by
    rw [← n4]
    have := wNorm_mul_le hβ (G := fun c : F × F => (χ (c.2 - c.1) : ℝ) * f c.1)
      (κ := fun _ => 1 / (qF - 3)) (M := 1 / (qF - 3)) (by positivity) (fun c => by
        rw [abs_of_nonneg (by positivity)])
    refine le_of_eq_of_le ?_ this
    congr 1; funext c; simp only [g4]; ring
  have m5 : wNorm pairLaw g5 ≤ 2 * (qF - 5) * cT (F := F) * N := by
    rw [← n5]
    have h5 : 0 ≤ 2 * (qF - 5) * cT (F := F) := by
      have : 0 ≤ qF - 5 := by linarith
      positivity
    exact wNorm_mul_le hβ (G := fun c : F × F => (χ (c.2 - c.1) : ℝ) * f c.2)
      (κ := fun _ => 2 * (qF - 5) * cT (F := F)) h5 (fun c => by rw [abs_of_nonneg h5])
  have hsum : wNorm pairLaw (partR f) ≤ wNorm pairLaw g1 + wNorm pairLaw g2 + wNorm pairLaw g3 +
      wNorm pairLaw g4 + wNorm pairLaw g5 := by
    rw [hR]
    refine (wNorm_sub_le hβ _ g5).trans (add_le_add ?_ le_rfl)
    refine (wNorm_sub_le hβ _ g4).trans (add_le_add ?_ le_rfl)
    refine (wNorm_sub_le hβ _ g3).trans (add_le_add ?_ le_rfl)
    exact wNorm_sub_le hβ g1 g2
  -- the constant
  rw [rho03_prime_eq h7]
  have hcT : cT (F := F) = 1 / ((qF - 3) * (qF - 6) * (qF - 2)) := rfl
  have hk : 1 / ((qF - 3) * (qF - 2)) * (Real.sqrt qF * N) + 2 * cT (F := F) * (Real.sqrt qF * N) +
      (qF - 2) * cT (F := F) * (Real.sqrt qF * N) + 1 / (qF - 3) * N +
      2 * (qF - 5) * cT (F := F) * N ≤
      (1 / (qF - 3) + 2 / ((qF - 3) * (qF - 6)) +
        2 * Real.sqrt qF / ((qF - 6) * (qF - 2))) * N := by
    have e1 : 1 / ((qF - 3) * (qF - 2)) * (Real.sqrt qF * N) +
        2 * cT (F := F) * (Real.sqrt qF * N) + (qF - 2) * cT (F := F) * (Real.sqrt qF * N) =
        2 * Real.sqrt qF / ((qF - 6) * (qF - 2)) * N := by
      rw [hcT]; field_simp; ring
    have e2 : 2 * (qF - 5) * cT (F := F) * N ≤ 2 / ((qF - 3) * (qF - 6)) * N := by
      apply mul_le_mul_of_nonneg_right _ hN0
      rw [hcT, show 2 * (qF - 5) * (1 / ((qF - 3) * (qF - 6) * (qF - 2))) =
        2 / ((qF - 3) * (qF - 6)) * ((qF - 5) / (qF - 2)) by field_simp]
      have : (qF - 5) / (qF - 2) ≤ 1 := by rw [div_le_one h2p]; linarith
      have : 0 ≤ 2 / ((qF - 3) * (qF - 6)) := by positivity
      nlinarith
    nlinarith [e1, e2]
  linarith [m1, m2, m3, m4, m5, hsum, hk]

/-- **`lem:oct24:feature-block`(a), proof Step 3, the one-prime bound**: the correlation of `𝓗₀`
and the one-prime `𝒦₁₂` is at most `ϱ₀₃(p)`. -/
theorem hprime_one (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (g : F → ℝ) (κ : F × F → ℝ) (hg : ∑ a, g a = 0)
    (hη : ∀ h : F → ℝ, ∑ c : F × F, pairLaw c * κ c * h c.1 = 0)
    (hζ : ∀ h : F → ℝ, ∑ c : F × F, pairLaw c * κ c * h c.2 = 0) :
    |∑ c : F × F, pairLaw c * (condT *ᵥ g) c * κ c| ≤
      rho03 (1 / qF) (1 / Real.sqrt qF) *
        (Real.sqrt ((1 / qF) * ∑ a, g a ^ 2) * Real.sqrt (∑ c : F × F, pairLaw c * κ c ^ 2)) := by
  have hβ : ∀ c : F × F, 0 ≤ pairLaw c := pairLaw_nonneg hF h3 h7
  have hsplit : ∑ c : F × F, pairLaw c * (condT *ᵥ g) c * κ c =
      ∑ c : F × F, pairLaw c * κ c * partA g c.1 + ∑ c : F × F, pairLaw c * κ c * partB g c.2 +
        ∑ c : F × F, pairLaw c * partR g c * κ c := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    by_cases h : c.1 = c.2
    · have : pairLaw c = 0 := by unfold pairLaw; rw [h]; exact (m_diag c.2).1
      rw [this]; ring
    · have hd := condT_decomp hF h3 h7 g hg h
      rw [show c = (c.1, c.2) from rfl, hd]
      ring
  rw [hsplit, hη, hζ, zero_add, zero_add]
  have hcs := abs_wsum_le univ pairLaw (partR g) κ (fun c _ => hβ c)
  refine hcs.trans ?_
  have hR := norm_remainder_le hF h3 h7 g hg
  unfold wNorm at hR
  calc Real.sqrt (∑ c, pairLaw c * partR g c ^ 2) * Real.sqrt (∑ c, pairLaw c * κ c ^ 2)
      ≤ (rho03 (1 / qF) (1 / Real.sqrt qF) * Real.sqrt ((1 / qF) * ∑ u, g u ^ 2)) *
          Real.sqrt (∑ c, pairLaw c * κ c ^ 2) :=
        mul_le_mul_of_nonneg_right hR (Real.sqrt_nonneg _)
    _ = _ := by ring

/-! ## The coarse estimates of Step 3 from the exact formula -/

/-- `T₂ f(y, z) = (Σ_z - f(z))/(p - 1)` for mean-zero `f`. -/
theorem condT2_explicit (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ u, f u = 0) (y z : F) :
    (condT2 *ᵥ f) (y, z) = (sigZ f z - f z) / (qF - 1) := by
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  simp only [mulVec, dotProduct, condT2, m02_eq' hF h3 h7]
  have e : ∀ u, qF * ((1 + (χ (z - u) : ℝ) - if u = z then 1 else 0) / (qF * (qF - 1))) * f u =
      (f u + (χ (z - u) : ℝ) * f u - if u = z then f u else 0) / (qF - 1) := by
    intro u
    split_ifs
    · field_simp
    · field_simp; ring
  simp only [e, ← sum_div, sum_sub_distrib, sum_add_distrib, hf, zero_add, sum_ite_eq',
    mem_univ, ↓reduceIte, sigZ]

/-- The part of `T f - T₂ f` depending on `z` alone. -/
noncomputable def partD (f : F → ℝ) (z : F) : ℝ :=
  sigZ f z / ((qF - 1) * (qF - 2)) + (1 / (qF - 1) - (qF - 5) * (qF - 4) * cT (F := F)) * f z

theorem condT_sub_decomp (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ u, f u = 0) {y z : F} (hyz : y ≠ z) :
    (condT *ᵥ f) (y, z) - (condT2 *ᵥ f) (y, z) = partA f y + partD f z + partR f (y, z) := by
  rw [condT_decomp hF h3 h7 f hf hyz, condT2_explicit hF h3 h7 f hf]
  simp only [partB, partD, cT]
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h2 : qF - 2 ≠ 0 := by intro h; linarith
  have h3' : qF - 3 ≠ 0 := by intro h; linarith
  have h6 : qF - 6 ≠ 0 := by intro h; linarith
  field_simp
  ring

theorem wNorm_fst (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (H : F → ℝ) : wNorm pairLaw (fun c : F × F => H c.1) = Real.sqrt ((1 / qF) * ∑ y, H y ^ 2) := by
  unfold wNorm; rw [sum_pairLaw_fst hF h3 h7 H]

theorem wNorm_snd (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (H : F → ℝ) : wNorm pairLaw (fun c : F × F => H c.2) = Real.sqrt ((1 / qF) * ∑ y, H y ^ 2) := by
  unfold wNorm; rw [sum_pairLaw_snd hF h3 h7 H]

omit [Field F] [DecidableEq F] in
theorem wNorm_congr_supp {β G G' : F × F → ℝ} (h : ∀ c, β c ≠ 0 → G c = G' c) :
    wNorm β G = wNorm β G' := by
  unfold wNorm
  congr 1
  refine sum_congr rfl fun c _ => ?_
  by_cases hc : β c = 0
  · rw [hc, zero_mul, zero_mul]
  · rw [h c hc]

/-- **The coarse bound** `‖T f - T₂ f‖ ≤ (4/p) ‖f‖` in `L²(m₁₂)`, for `p ≥ 2²⁴`. -/
theorem norm_condT_sub_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hbig : (2 : ℝ) ^ 24 ≤ qF) (f : F → ℝ) (hf : ∑ u, f u = 0) :
    wNorm pairLaw (fun c => (condT *ᵥ f) c - (condT2 *ᵥ f) c) ≤
      4 / qF * Real.sqrt ((1 / qF) * ∑ u, f u ^ 2) := by
  have h7 : 7 ≤ qF := le_trans (by norm_num) hbig
  have hβ : ∀ c : F × F, 0 ≤ pairLaw c := pairLaw_nonneg hF h3 h7
  have hq : 0 < qF := by linarith
  set N := Real.sqrt ((1 / qF) * ∑ u, f u ^ 2) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hsq : Real.sqrt (∑ u, f u ^ 2) = Real.sqrt qF * N := by
    rw [hN, ← Real.sqrt_mul hq.le]
    congr 1
    field_simp
  have hsupp : ∀ c : F × F, pairLaw c ≠ 0 →
      (condT *ᵥ f) c - (condT2 *ᵥ f) c = partA f c.1 + partD f c.2 + partR f c := by
    intro c hc
    have hne : c.1 ≠ c.2 := by
      intro h; apply hc; unfold pairLaw; rw [h]; exact (m_diag c.2).1
    exact condT_sub_decomp hF h3 h7 f hf hne
  rw [wNorm_congr_supp hsupp]
  have hc0 : 0 ≤ cT (F := F) := by
    unfold cT
    have : 0 < qF - 3 := by linarith
    have : 0 < qF - 6 := by linarith
    have : 0 < qF - 2 := by linarith
    positivity
  -- the norms of `A` and `D`
  have nsig1 : wNorm pairLaw (fun c : F × F => sigZ f c.1) = Real.sqrt qF * N := by
    rw [wNorm_fst hF h3 h7, sum_sigZ_sq hF h3 f hf, ← hsq]; congr 1; field_simp
  have nsig2 : wNorm pairLaw (fun c : F × F => sigZ f c.2) = Real.sqrt qF * N := by
    rw [wNorm_snd hF h3 h7, sum_sigZ_sq hF h3 f hf, ← hsq]; congr 1; field_simp
  have nf1 : wNorm pairLaw (fun c : F × F => f c.1) = N := wNorm_fst hF h3 h7 f
  have nf2 : wNorm pairLaw (fun c : F × F => f c.2) = N := wNorm_snd hF h3 h7 f
  set a1 := (qF - 4) * cT (F := F)
  set a2 := 1 / (qF - 3)
  set a3 := 1 / ((qF - 1) * (qF - 2))
  set a4 := 1 / (qF - 1) - (qF - 5) * (qF - 4) * cT (F := F)
  have ha1 : 0 ≤ a1 := mul_nonneg (by linarith) hc0
  have ha2 : 0 ≤ a2 := by have : 0 < qF - 3 := by linarith
                          positivity
  have ha3 : 0 ≤ a3 := by
    have : 0 < qF - 1 := by linarith
    have : 0 < qF - 2 := by linarith
    positivity
  have nA : wNorm pairLaw (fun c : F × F => partA f c.1) ≤ a1 * (Real.sqrt qF * N) + a2 * N := by
    have e : (fun c : F × F => partA f c.1) =
        fun c => (fun c : F × F => -a1 * sigZ f c.1) c - (fun c : F × F => a2 * f c.1) c := by
      funext c; simp only [partA, a1, a2]; ring
    rw [e]
    refine (wNorm_sub_le hβ _ _).trans (add_le_add ?_ ?_)
    · rw [← nsig1]
      exact wNorm_mul_le hβ (G := fun c : F × F => sigZ f c.1) (κ := fun _ => -a1) ha1
        (fun c => by rw [abs_neg, abs_of_nonneg ha1])
    · rw [← nf1]
      exact wNorm_mul_le hβ (G := fun c : F × F => f c.1) (κ := fun _ => a2) ha2
        (fun c => by rw [abs_of_nonneg ha2])
  have nD : wNorm pairLaw (fun c : F × F => partD f c.2) ≤ a3 * (Real.sqrt qF * N) + |a4| * N := by
    have e : (fun c : F × F => partD f c.2) =
        fun c => (fun c : F × F => a3 * sigZ f c.2) c + (fun c : F × F => a4 * f c.2) c := by
      funext c; simp only [partD, a3, a4]; ring
    rw [e]
    refine (wNorm_add_le hβ _ _).trans (add_le_add ?_ ?_)
    · rw [← nsig2]
      exact wNorm_mul_le hβ (G := fun c : F × F => sigZ f c.2) (κ := fun _ => a3) ha3
        (fun c => by rw [abs_of_nonneg ha3])
    · rw [← nf2]
      exact wNorm_mul_le hβ (G := fun c : F × F => f c.2) (κ := fun _ => a4) (abs_nonneg _)
        (fun c => le_rfl)
  have nR := norm_remainder_le hF h3 h7 f hf
  have htot : wNorm pairLaw (fun c => partA f c.1 + partD f c.2 + partR f c) ≤
      wNorm pairLaw (fun c : F × F => partA f c.1) + wNorm pairLaw (fun c : F × F => partD f c.2) +
        wNorm pairLaw (partR f) := by
    have e : (fun c : F × F => partA f c.1 + partD f c.2 + partR f c) =
        ((fun c : F × F => partA f c.1) + fun c => partD f c.2) + partR f := by
      funext c; simp
    rw [e]
    exact (wNorm_add_le hβ _ _).trans (add_le_add (wNorm_add_le hβ _ _) le_rfl)
  -- the numbers, with `s = √p ≥ 2¹²`
  rw [rho03_prime_eq h7] at nR
  have hs12 : (2 : ℝ) ^ 12 ≤ Real.sqrt qF := by
    rw [show (2 : ℝ) ^ 12 = Real.sqrt (2 ^ 24) by
      rw [show (2 : ℝ) ^ 24 = (2 ^ 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hbig
  have hsx := num_s_le hs12 (Real.mul_self_sqrt hq.le)
  have k1 : a1 * Real.sqrt qF ≤ 1 / (10 * qF) := num_k1 hbig hsx
  have k2 : a2 ≤ 3 / (2 * qF) := num_k2 hbig
  have k3 : a3 * Real.sqrt qF ≤ 1 / (10 * qF) := num_k3 hbig hsx
  have k4 : |a4| ≤ 1 / (10 * qF) := num_k4 hbig
  have k5 : 1 / (qF - 3) + 2 / ((qF - 3) * (qF - 6)) + 2 * Real.sqrt qF / ((qF - 6) * (qF - 2)) ≤
      17 / (10 * qF) := num_k5 hbig hsx
  have hfin : (a1 * (Real.sqrt qF * N) + a2 * N) + (a3 * (Real.sqrt qF * N) + |a4| * N) +
      (1 / (qF - 3) + 2 / ((qF - 3) * (qF - 6)) + 2 * Real.sqrt qF / ((qF - 6) * (qF - 2))) * N ≤
      4 / qF * N := by
    have e : (a1 * (Real.sqrt qF * N) + a2 * N) + (a3 * (Real.sqrt qF * N) + |a4| * N) +
        (1 / (qF - 3) + 2 / ((qF - 3) * (qF - 6)) + 2 * Real.sqrt qF / ((qF - 6) * (qF - 2))) * N =
        (a1 * Real.sqrt qF + a2 + a3 * Real.sqrt qF + |a4| +
          (1 / (qF - 3) + 2 / ((qF - 3) * (qF - 6)) +
            2 * Real.sqrt qF / ((qF - 6) * (qF - 2)))) * N := by
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hN0
    have h35 : 1 / (10 * qF) + 3 / (2 * qF) + 1 / (10 * qF) + 1 / (10 * qF) + 17 / (10 * qF) =
        7 / (2 * qF) := by
      field_simp; ring
    have h74 : 7 / (2 * qF) ≤ 4 / qF := by
      rw [div_le_div_iff₀ (by positivity) hq]; nlinarith
    linarith
  linarith [htot, nA, nD, nR, hfin]

end Prime

end Sarkozy.OpsFeature

namespace Sarkozy.OpsFeature

open Sarkozy.MiddleRecords Sarkozy.Mixing Sarkozy.EnvelopeSteps Sarkozy.Envelopes
open Finset Matrix

/-! ## The prime inputs of Step 3 at a block, proved -/

theorem rho0bar12_ge {q r : ℝ} (hq : 0 ≤ q) (hq8 : q ≤ 1 / 8) (hr : 0 ≤ r) :
    rho02 q r + 4 * q ≤ rho0bar12 q r := by
  unfold rho02 rho0bar12
  have h1 : 0 < 1 - q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h4 : 0 < 1 - 4 * q := by linarith
  have he0 : 2 * q ≤ e0 q := by
    unfold e0
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg hq hq, mul_nonneg (mul_nonneg hq hq) hq]
  have he1 : e0 q < 1 := by
    unfold e0
    rw [div_lt_one (by positivity)]
    nlinarith
  have hs : 0 < Real.sqrt (1 - e0 q) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (1 - e0 q) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hsq0 : 0 ≤ r * Real.sqrt (1 + q) := by positivity
  have a : r * Real.sqrt (1 + q) / (1 - q) ≤ r * Real.sqrt (1 + q) / (1 - 3 * q) :=
    div_le_div_of_nonneg_left hsq0 h3 (by linarith)
  have b : 2 * q ≤ 2 * q / (1 - 3 * q) := by
    rw [le_div_iff₀ h3]; nlinarith
  have hnum : r * Real.sqrt (1 + q) / (1 - q) + 4 * q ≤
      (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) + e0 q := by
    rw [add_div]; linarith
  have hnum0 : 0 ≤ (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) + e0 q := by
    have : 0 ≤ (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) := by positivity
    linarith
  calc r * Real.sqrt (1 + q) / (1 - q) + 4 * q
      ≤ (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) + e0 q := hnum
    _ ≤ _ := by
        rw [le_div_iff₀ hs]
        exact mul_le_of_le_one_right hnum0 hs1

theorem rho03tq_ge {q r : ℝ} (hq : 0 ≤ q) (hq8 : q ≤ 1 / 8) (hr : 0 ≤ r) : 4 ≤ rho03tq q r := by
  unfold rho03tq
  have h1 : 0 < 1 - q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h4 : 0 < 1 - 4 * q := by linarith
  have he0 : 0 ≤ e0 q := by unfold e0; positivity
  have he1 : e0 q < 1 := by
    unfold e0
    rw [div_lt_one (by positivity)]
    nlinarith
  have hs : 0 < Real.sqrt (1 - e0 q) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (1 - e0 q) ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hϱ : 0 ≤ r * Real.sqrt (1 + q) / (1 - q) := by positivity
  have a : 2 ≤ 2 * (1 + r * Real.sqrt (1 + q) / (1 - q)) / (1 - 3 * q) := by
    rw [le_div_iff₀ h3]; nlinarith
  have b : 2 ≤ 2 / ((1 - 3 * q) * (1 - 4 * q)) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  rw [le_div_iff₀ hs]
  nlinarith

section BlockProved

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Field (F p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

omit [Fintype P] [DecidableEq P] [∀ p, DecidableEq (F p)] in
theorem card_big {b : ℝ} (hB : MiddleBlock F b) (p : P) :
    (2 : ℝ) ^ 24 ≤ Fintype.card (F p) := by
  linarith [hB.hb, hB.hbp p, show (2 : ℝ) ^ 24 ≤ 19951586 by norm_num]

omit [Fintype P] [DecidableEq P] [∀ p, Field (F p)] [∀ p, DecidableEq (F p)] in
theorem sum_unifB_sq (p : P) (f : F p → ℝ) :
    ∑ a, unifB p a * f a ^ 2 = 1 / (Fintype.card (F p) : ℝ) * ∑ a, f a ^ 2 := by
  simp only [unifB, mul_sum]

omit [Fintype P] [DecidableEq P] [∀ p, DecidableEq (F p)] in
theorem centred_of_unifB {p : P} {f : F p → ℝ} (h7 : (7 : ℝ) ≤ Fintype.card (F p))
    (hf : ∑ a, unifB p a * f a = 0) : ∑ a, f a = 0 := by
  simp only [unifB, ← mul_sum] at hf
  rcases mul_eq_zero.mp hf with h | h
  · exact absurd h (by have : (0 : ℝ) < Fintype.card (F p) := by linarith
                       positivity)
  · exact h

omit [Fintype P] [DecidableEq P] in
/-- **`Edge03Inputs`, proved**: the one-prime bound of the edge `03` (`hprime_one`) and the two
coarse estimates of Step 3, from the exact conditional expectation (`norm_condT_sub_le`,
`condT2_norm`). -/
theorem edge03Inputs_proved {b : ℝ} (hB : MiddleBlock F b) : Edge03Inputs F b := by
  have hb0 : 0 < b := by linarith [hB.hb]
  have hq0 : 0 ≤ 1 / b := by positivity
  have hq8 : 1 / b ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith [hB.hb])
  have hr0 : 0 ≤ 1 / Real.sqrt b := by positivity
  -- `4/p ≤ 4/b ≤ ϱ̃₀₃(b)`
  have h4p : ∀ p, 4 / (Fintype.card (F p) : ℝ) ≤ 4 / b := fun p =>
    div_le_div_of_nonneg_left (by norm_num) hb0 (hB.hbp p)
  have h4b : 4 / b ≤ 1 / b * rho03tq (1 / b) (1 / Real.sqrt b) := by
    have := rho03tq_ge hq0 hq8 hr0
    rw [show 4 / b = 1 / b * 4 by ring]
    exact mul_le_mul_of_nonneg_left this hq0
  refine ⟨fun p g κ hg hη hζ => ?_, fun p f hf => ?_, fun p f hf => ?_⟩
  · -- the one-prime bound
    have h7 := hB.h7 p
    have h := hprime_one (hB.hF p) (hB.h3 p) h7 g κ (centred_of_unifB h7 hg) hη hζ
    rw [sum_unifB_sq]
    exact h
  · -- `‖T_p‖ ≤ ϱ_{0|12}(b)`
    have h7 := hB.h7 p
    have hq : (0 : ℝ) < Fintype.card (F p) := by linarith
    have hf' := centred_of_unifB h7 hf
    have hβ : ∀ c : F p × F p, 0 ≤ pairLaw c := pairLaw_nonneg (hB.hF p) (hB.h3 p) h7
    set N := Real.sqrt (1 / (Fintype.card (F p) : ℝ) * ∑ a, f a ^ 2) with hN
    have hN0 : 0 ≤ N := Real.sqrt_nonneg _
    have hd := norm_condT_sub_le (hB.hF p) (hB.h3 p) (card_big hB p) f hf'
    have h2 : wNorm pairLaw (condT2 *ᵥ f) ≤ rho02 (1 / b) (1 / Real.sqrt b) * N := by
      unfold wNorm
      rw [condT2_norm (hB.hF p) (hB.h3 p) h7 f hf', ← mul_sum, hN,
        Real.sqrt_mul (by unfold r02sq; positivity)]
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      rw [← Real.sqrt_sq (rho02_b_le hB.hb).1]
      exact Real.sqrt_le_sqrt (r02sq_b (by linarith [hB.hb]) (hB.hbp p))
    have htot : wNorm pairLaw (condT *ᵥ f) ≤ rho0bar12 (1 / b) (1 / Real.sqrt b) * N := by
      have e : condT *ᵥ f = (condT2 *ᵥ f) + fun c => (condT *ᵥ f) c - (condT2 *ᵥ f) c := by
        funext c; simp
      rw [e]
      refine (wNorm_add_le hβ _ _).trans ?_
      have hge := rho0bar12_ge hq0 hq8 hr0
      have : 4 / (Fintype.card (F p) : ℝ) * N ≤ 4 * (1 / b) * N := by
        apply mul_le_mul_of_nonneg_right _ hN0
        have := h4p p; rw [show 4 * (1 / b) = 4 / b by ring]; exact this
      nlinarith [hd, h2, this, mul_le_mul_of_nonneg_right hge hN0]
    rw [sum_unifB_sq]
    have hsq := wNorm_sq hβ (condT *ᵥ f)
    rw [← hsq]
    have hρ0 : 0 ≤ rho0bar12 (1 / b) (1 / Real.sqrt b) * N :=
      (wNorm_nonneg _ _).trans htot
    have := pow_le_pow_left₀ (wNorm_nonneg _ _) htot 2
    rw [mul_pow, hN, Real.sq_sqrt (by positivity)] at this
    exact this
  · -- `‖T_p - T_{2,p}‖ ≤ ϱ̃₀₃(b)`
    have h7 := hB.h7 p
    have hq : (0 : ℝ) < Fintype.card (F p) := by linarith
    have hf' := centred_of_unifB h7 hf
    have hβ : ∀ c : F p × F p, 0 ≤ pairLaw c := pairLaw_nonneg (hB.hF p) (hB.h3 p) h7
    have hd := norm_condT_sub_le (hB.hF p) (hB.h3 p) (card_big hB p) f hf'
    have hd' : wNorm pairLaw ((condT - condT2) *ᵥ f) ≤
        1 / b * rho03tq (1 / b) (1 / Real.sqrt b) *
          Real.sqrt (1 / (Fintype.card (F p) : ℝ) * ∑ a, f a ^ 2) := by
      rw [sub_mulVec]
      refine (show wNorm pairLaw (condT *ᵥ f - condT2 *ᵥ f) =
          wNorm pairLaw (fun c => (condT *ᵥ f) c - (condT2 *ᵥ f) c) from rfl) ▸ hd.trans ?_
      exact mul_le_mul_of_nonneg_right ((h4p p).trans h4b) (Real.sqrt_nonneg _)
    rw [sum_unifB_sq, ← wNorm_sq hβ]
    have := pow_le_pow_left₀ (wNorm_nonneg _ _) hd' 2
    rw [mul_pow, Real.sq_sqrt (by positivity)] at this
    exact this

/-- **`lem:oct24:feature-block`(a), the edge `03`, proved** in the actual block law. -/
theorem edge03_block_proved {b : ℝ} (hB : MiddleBlock F b) :
    Edge03Block F (rho03 (1 / b) (1 / Real.sqrt b)) :=
  edge03_of_prime hB ((edge03Inputs_proved hB).toPrime hB)

/-- **W2's `hcor` for the actual fold features, proved**: `lem:oct24:feature-block`(a) at every
block of primes `p ≡ 3 (mod 4)` with least prime `b ≥ Q₃`, in exactly the form of the hypothesis
`hcor` of `Envelopes.feature_frame_middle`. -/
theorem actual_hcor_proved {b : ℝ} (hB : MiddleBlock F b) (h : Fin 5 → Tri F → ℝ)
    (hf : IsFoldFeat h) :
    ∀ i j, i ≠ j → |inner ℝ (emb (h i)) (emb (h j))| ≤ foldPattern (rho02 (1 / b)
      (1 / Real.sqrt b)) (rho01 (1 / b)) (rho03 (1 / b) (1 / Real.sqrt b))
        (rho34 (1 / b) (1 / Real.sqrt b)) i j * ‖emb (h i)‖ * ‖emb (h j)‖ :=
  actual_hcor hB (edge03_block_proved hB) h hf

/-- **`lem:oct24:feature-block`(b) in the actual block law, proved**: the five fold features of
`L²(m_{0,𝔅})` satisfy `‖h₀ + ⋯ + h₄‖² ≤ Γ_F ∑_v ‖h_v‖²`,
`Γ_F = 500111979555137707696357560603/(5·10²⁹)`. -/
theorem actual_feature_frame_proved {b : ℝ} (hB : MiddleBlock F b) (h : Fin 5 → Tri F → ℝ)
    (hf : IsFoldFeat h) :
    ipm (fun x => ∑ i, h i x) (fun x => ∑ i, h i x) ≤ (gammaF : ℝ) * ∑ i, ipm (h i) (h i) :=
  actual_feature_frame hB (edge03_block_proved hB) h hf

end BlockProved

end Sarkozy.OpsFeature
