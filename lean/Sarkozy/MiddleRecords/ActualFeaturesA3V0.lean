module

public import Sarkozy.MiddleRecords.ActualFeaturesA3

/-!
# `A₃^{*_m} V₀` under the actual half marginal (`lem:actual-features`(c), the last identity)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(c):
`A₃^{*_m} V₀ = (p + 4)/(p(p - 1)(p - 4)) I` on the mean-zero functions `H₀`, i.e.
`⟨A₃ h, V₀ g⟩_{m₀} = (p + 4)/(p(p - 1)(p - 4)) ⟨h, g⟩` (`A3_V0`), with the uniform inner product
on `F` and `m₀ = oldW/oldZ`.

As in the paper, the key is the conditional mean `E_{m₀}[χ(s - x₁) χ(s - x₂) | x₀ = a] = κ(s - a)`,
here computed as the unnormalized sum `W(a, s) = ∑_{x₁,x₂} oldW(a, x₁, x₂) χ(s - x₁) χ(s - x₂)`
(`oldWchi`): `W(a, a) = -(p - 1)(p - 3)/2` and `W(a, s) = -(p - 6)(p - 3)/4` for `s ≠ a`
(`oldWchi_eq`). Dividing by the `x₀`-fibre weight `(p - 1)(p - 3)(p - 4)/4` gives the paper's
`κ₀ = -2/(p - 4)` and `κ₁ = -(p - 6)/((p - 1)(p - 4))`. The proof sums over `x₁` first
(`sum_b_oldW`: two-point character sums, with the two excluded labels), then over `x₂`, using
`χ(c - a)² = 1` and `χ(s - c) [c = s] = 0`.

With `Sarkozy.MiddleRecords.ActualFeaturesA3` this gives all four Gram identities of
`lem:actual-features`(c); the norm claims and part (d) are `ActualFeaturesNorms` and
`ActualFeaturesSynthesis`. **Not formalized:** `‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ J_F q r` and part (e).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-! ## Two-point sums -/

/-- `∑_b χ(u - b) χ(v - b) = p [u = v] - 1`. -/
theorem sum_chi_sub_sub (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (u v : F) :
    ∑ b, (χ (u - b) : ℝ) * (χ (v - b) : ℝ) = qF * (if u = v then 1 else 0) - 1 := by
  rw [← sumR_chi_chi hF u v]
  refine sum_congr rfl fun b _ => ?_
  rw [chi_swap h3 u b, chi_swap h3 v b]
  push_cast
  ring

/-- `∑_b χ(b - u) χ(v - b) = 1 - p [u = v]`. -/
theorem sum_chi_mixed (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (u v : F) :
    ∑ b, (χ (b - u) : ℝ) * (χ (v - b) : ℝ) = 1 - qF * (if u = v then 1 else 0) := by
  have h := sumR_chi_chi hF u v
  have e : ∑ b, (χ (b - u) : ℝ) * (χ (v - b) : ℝ) = -∑ b, (χ (b - u) : ℝ) * (χ (b - v) : ℝ) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [chi_swap h3 v b]
    push_cast
    ring
  rw [e, h]
  ring

/-! ## The inner sum over `x₁` -/

/-- **The `x₁`-sum**: for `a ≠ c`,
`∑_b oldW(a, b, c) χ(s - b) = (1 + χ(c - a))/4 · (p [a = s] - p [c = s] -
(p - 5 - χ(c - a))(χ(s - a) + χ(s - c)))`. -/
theorem sum_b_oldW (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a c : F} (hac : a ≠ c)
    (s : F) :
    ∑ b, oldW a b c * (χ (s - b) : ℝ) =
      (1 + (χ (c - a) : ℝ)) / 4 * (qF * (if a = s then 1 else 0) - qF * (if c = s then 1 else 0) -
        (qF - 5 - (χ (c - a) : ℝ)) * ((χ (s - a) : ℝ) + (χ (s - c) : ℝ))) := by
  set f : F → ℝ := fun b => (1 + (χ (c - a) : ℝ)) * (qF - 5 - (χ (b - a) : ℝ) -
    (χ (c - b) : ℝ)) / 4 * (χ (s - b) : ℝ) with hf
  have e : ∀ b, oldW a b c * (χ (s - b) : ℝ) = if b ≠ a ∧ b ≠ c then f b else 0 := by
    intro b
    unfold oldW
    by_cases h1 : b ≠ a ∧ b ≠ c
    · rw [ite_eq_left (show a ≠ b ∧ a ≠ c ∧ b ≠ c from ⟨Ne.symm h1.1, hac, h1.2⟩),
        ite_eq_left h1]
    · rw [ite_eq_right (fun h => h1 ⟨Ne.symm h.1, h.2.2⟩), ite_eq_right h1, zero_mul]
  simp only [e]
  rw [sum_ne_ne hac f]
  have hsum : ∑ b, f b = (1 + (χ (c - a) : ℝ)) / 4 *
      (qF * (if a = s then 1 else 0) - qF * (if c = s then 1 else 0)) := by
    have e2 : ∀ b, f b = (1 + (χ (c - a) : ℝ)) / 4 * ((qF - 5) * (χ (s - b) : ℝ) -
        (χ (b - a) : ℝ) * (χ (s - b) : ℝ) - (χ (c - b) : ℝ) * (χ (s - b) : ℝ)) := by
      intro b; rw [hf]; ring
    simp only [e2, ← mul_sum, sum_sub_distrib]
    rw [sumR_chi_sub hF s, sum_chi_mixed hF h3 a s, sum_chi_sub_sub hF h3 c s]
    ring
  have hfa : f a = (1 + (χ (c - a) : ℝ)) * (qF - 5 - (χ (c - a) : ℝ)) / 4 * (χ (s - a) : ℝ) := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero, sub_zero]
  have hfc : f c = (1 + (χ (c - a) : ℝ)) * (qF - 5 - (χ (c - a) : ℝ)) / 4 * (χ (s - c) : ℝ) := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero, sub_zero]
  rw [hsum, hfa, hfc]
  ring

/-! ## The conditional sum `W(a, s)` -/

/-- `W(a, s) = ∑_{x₁, x₂} oldW(a, x₁, x₂) χ(s - x₁) χ(s - x₂)`. -/
noncomputable def oldWchi (a s : F) : ℝ :=
  ∑ b, ∑ c, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ))

/-- The term of `W(a, s)` at `x₂ = c ≠ a`, simplified with `χ(c - a)² = 1` and
`χ(s - c)[c = s] = 0`. -/
theorem term_c {a c : F} (hac : a ≠ c) (s : F) :
    (χ (s - c) : ℝ) * ((1 + (χ (c - a) : ℝ)) / 4 * (qF * (if a = s then 1 else 0) -
      qF * (if c = s then 1 else 0) -
        (qF - 5 - (χ (c - a) : ℝ)) * ((χ (s - a) : ℝ) + (χ (s - c) : ℝ)))) =
      ((qF * (if a = s then 1 else 0) - (qF - 6) * (χ (s - a) : ℝ)) *
          ((χ (s - c) : ℝ) + (χ (c - a) : ℝ) * (χ (s - c) : ℝ)) -
        (qF - 6) * ((χ (s - c) : ℝ) ^ 2 + (χ (c - a) : ℝ) * (χ (s - c) : ℝ) ^ 2)) / 4 := by
  have hA : (χ (c - a) : ℝ) ^ 2 = 1 := chi_sq_one hac
  by_cases hcs : c = s
  · subst hcs
    simp only [sub_self, quadraticChar_zero, Int.cast_zero]
    ring
  · rw [ite_eq_right hcs]
    linear_combination (-(qF - 6) / 4 * 0 + ((χ (s - c) : ℝ) * (χ (s - a) : ℝ) +
      (χ (s - c) : ℝ) ^ 2) / 4) * hA

/-- **`W(a, s)`** in closed form (before the case split):
`W = ((p[a = s] - (p - 6)σ)(1 - σ - p[a = s]) - (p - 6)(p - 2 + [a = s] - σ))/4`, `σ = χ(s - a)`. -/
theorem oldWchi_formula (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a s : F) :
    oldWchi a s = ((qF * (if a = s then 1 else 0) - (qF - 6) * (χ (s - a) : ℝ)) *
        (1 - (χ (s - a) : ℝ) - qF * (if a = s then 1 else 0)) -
      (qF - 6) * (qF - 2 + (if a = s then 1 else 0) - (χ (s - a) : ℝ))) / 4 := by
  unfold oldWchi
  rw [sum_comm]
  -- per `c`: `χ(s - c) ∑_b oldW(a, b, c) χ(s - b)`, zero at `c = a`
  have e : ∀ c, ∑ b, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) =
      if c = a then 0 else
        ((qF * (if a = s then 1 else 0) - (qF - 6) * (χ (s - a) : ℝ)) *
            ((χ (s - c) : ℝ) + (χ (c - a) : ℝ) * (χ (s - c) : ℝ)) -
          (qF - 6) * ((χ (s - c) : ℝ) ^ 2 + (χ (c - a) : ℝ) * (χ (s - c) : ℝ) ^ 2)) / 4 := by
    intro c
    by_cases hca : c = a
    · subst hca
      rw [ite_eq_left rfl]
      exact sum_eq_zero fun b _ => by rw [oldW_diag_x1, zero_mul]
    · rw [ite_eq_right hca]
      have : ∑ b, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) =
          (χ (s - c) : ℝ) * ∑ b, oldW a b c * (χ (s - b) : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
      rw [this, sum_b_oldW hF h3 (Ne.symm hca) s, term_c (Ne.symm hca) s]
  simp only [e]
  set σ : ℝ := (χ (s - a) : ℝ) with hσ
  set E : ℝ := if a = s then 1 else 0 with hE
  set K : ℝ := qF * E - (qF - 6) * σ with hK
  -- remove the term `c = a`
  have hite : ∀ G : F → ℝ, ∑ c, (if c = a then 0 else G c) = ∑ c, G c - G a := by
    intro G
    have : ∀ c, (if c = a then 0 else G c) = G c - (if c = a then G c else 0) := by
      intro c; split_ifs <;> simp
    simp only [this, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hite (fun c => (K * ((χ (s - c) : ℝ) + (χ (c - a) : ℝ) * (χ (s - c) : ℝ)) -
      (qF - 6) * ((χ (s - c) : ℝ) ^ 2 + (χ (c - a) : ℝ) * (χ (s - c) : ℝ) ^ 2)) / 4)]
  -- the four full sums
  have S1 : ∑ c, (χ (s - c) : ℝ) = 0 := sumR_chi_sub hF s
  have S2 : ∑ c, (χ (c - a) : ℝ) * (χ (s - c) : ℝ) = 1 - qF * E := sum_chi_mixed hF h3 a s
  have S3 : ∑ c, (χ (s - c) : ℝ) ^ 2 = qF - 1 := by
    have : ∀ c, (χ (s - c) : ℝ) ^ 2 = 1 - (if c = s then 1 else 0) := by
      intro c
      by_cases hc : c = s
      · subst hc; simp
      · rw [ite_eq_right hc, sub_zero]; exact chi_sq_one (u := c) (v := s) hc
    simp only [this, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, sum_ite_eq',
      mem_univ, ↓reduceIte]
  have S4 : ∑ c, (χ (c - a) : ℝ) * (χ (s - c) : ℝ) ^ 2 = -σ := by
    have : ∀ c, (χ (c - a) : ℝ) * (χ (s - c) : ℝ) ^ 2 =
        (χ (c - a) : ℝ) - (if c = s then (χ (c - a) : ℝ) else 0) := by
      intro c
      by_cases hc : c = s
      · subst hc; simp
      · rw [ite_eq_right hc, sub_zero, chi_sq_one (u := c) (v := s) hc, mul_one]
    simp only [this, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sumR_chi_shift hF a,
      zero_sub, hσ]
  have hsum : ∑ c, (K * ((χ (s - c) : ℝ) + (χ (c - a) : ℝ) * (χ (s - c) : ℝ)) -
      (qF - 6) * ((χ (s - c) : ℝ) ^ 2 + (χ (c - a) : ℝ) * (χ (s - c) : ℝ) ^ 2)) / 4 =
      (K * (0 + (1 - qF * E)) - (qF - 6) * ((qF - 1) + -σ)) / 4 := by
    rw [← S1, ← S2, ← S3, ← S4, ← sum_div, sum_sub_distrib, ← mul_sum, ← mul_sum,
      sum_add_distrib, sum_add_distrib]
  rw [hsum]
  simp only [sub_self, quadraticChar_zero, Int.cast_zero, zero_mul, add_zero]
  have hσa : σ ^ 2 = 1 - E := by
    rw [hσ, hE]
    by_cases has : a = s
    · subst has; simp
    · rw [ite_eq_right has, sub_zero]; exact chi_sq_one has
  rw [hK]
  linear_combination ((qF - 6) / 4) * hσa

/-- **`W(a, s)`**: `W(a, a) = -(p - 1)(p - 3)/2` and `W(a, s) = -(p - 6)(p - 3)/4` for `s ≠ a`, i.e.
the paper's `κ₀ = -2/(p - 4)` and `κ₁ = -(p - 6)/((p - 1)(p - 4))` times the `x₀`-fibre weight
`(p - 1)(p - 3)(p - 4)/4`. -/
theorem oldWchi_eq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a s : F) :
    oldWchi a s = if a = s then -((qF - 1) * (qF - 3) / 2) else -((qF - 6) * (qF - 3) / 4) := by
  rw [oldWchi_formula hF h3]
  by_cases has : a = s
  · subst has
    simp only [↓reduceIte, sub_self, quadraticChar_zero, Int.cast_zero, mul_zero, sub_zero]
    ring
  · rw [ite_eq_right has, ite_eq_right has]
    have hσ : (χ (s - a) : ℝ) ^ 2 = 1 := chi_sq_one has
    linear_combination ((qF - 6) / 4) * hσ

/-- **`lem:actual-features`(c): `A₃^{*_m} V₀ = (p + 4)/(p(p - 1)(p - 4)) I` on `H₀`**:
`E_{m₀}[(A₃ h)(x₁, x₂) g(x₀)] = (p + 4)/(p(p - 1)(p - 4)) · (1/p) ∑ h g` for mean-zero `h` (and any
`g`; on `H₀` this is the operator identity). -/
theorem A3_V0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h g : F → ℝ)
    (hh : ∑ s, h s = 0) :
    (∑ a, ∑ b, ∑ c, oldW a b c * A3op h b c * g a) / oldZ (F := F) =
      (qF + 4) / (qF * (qF - 1) * (qF - 4)) * (qF⁻¹ * ∑ s, h s * g s) := by
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h3' : qF - 3 ≠ 0 := by intro h; linarith
  have h4 : qF - 4 ≠ 0 := by intro h; linarith
  -- expand `A₃` and collect `W(a, s)`
  have hexp : ∀ a, ∑ b, ∑ c, oldW a b c * A3op h b c * g a =
      -(qF⁻¹ * g a * ∑ s, h s * oldWchi a s) := by
    intro a
    have hbc : ∀ b c, oldW a b c * A3op h b c * g a = -(qF⁻¹ * g a) *
        ∑ s, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) * h s := by
      intro b c
      have : ∑ s, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) * h s =
          oldW a b c * ∑ s, (χ (s - b) : ℝ) * (χ (s - c) : ℝ) * h s := by
        rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
      rw [this, A3op_meanZero h hh]
      ring
    have hswap : ∑ b, ∑ c, ∑ s, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) * h s =
        ∑ s, h s * oldWchi a s := by
      calc ∑ b, ∑ c, ∑ s, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) * h s
          = ∑ b, ∑ s, ∑ c, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) * h s :=
            sum_congr rfl fun b _ => sum_comm
        _ = ∑ s, ∑ b, ∑ c, oldW a b c * ((χ (s - b) : ℝ) * (χ (s - c) : ℝ)) * h s := sum_comm
        _ = ∑ s, h s * oldWchi a s := by
            refine sum_congr rfl fun s _ => ?_
            unfold oldWchi
            rw [mul_sum]
            refine sum_congr rfl fun b _ => ?_
            rw [mul_sum]
            exact sum_congr rfl fun c _ => by ring
    simp only [hbc, ← mul_sum]
    rw [hswap]
    ring
  simp only [hexp]
  have hW : ∀ a, ∑ s, h s * oldWchi a s = (-((qF - 1) * (qF - 3) / 2) + (qF - 6) * (qF - 3) / 4) *
      h a := by
    intro a
    have e : ∀ s, h s * oldWchi a s = -((qF - 6) * (qF - 3) / 4) * h s +
        (-((qF - 1) * (qF - 3) / 2) + (qF - 6) * (qF - 3) / 4) * (if a = s then h s else 0) := by
      intro s
      rw [oldWchi_eq hF h3]
      split_ifs <;> ring
    simp only [e, sum_add_distrib, ← mul_sum, hh, mul_zero, zero_add, sum_ite_eq, mem_univ,
      ↓reduceIte]
  simp only [hW]
  rw [oldZ_eq hF h3, sum_neg_distrib]
  have e2 : ∑ a, qF⁻¹ * g a * ((-((qF - 1) * (qF - 3) / 2) + (qF - 6) * (qF - 3) / 4) * h a) =
      qF⁻¹ * (-((qF - 1) * (qF - 3) / 2) + (qF - 6) * (qF - 3) / 4) * ∑ s, h s * g s := by
    rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
  rw [e2]
  field_simp
  ring

end Sarkozy.MiddleRecords
