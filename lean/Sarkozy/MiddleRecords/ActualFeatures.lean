module

public import Sarkozy.TraceMixing.Paley

/-!
# The pair laws of the actual half marginal (`lem:actual-features`(a))

`paper/sections/21_middle_records.tex`, `subsec:old-f`, `lem:actual-features`(a), with the actual
half marginal `m₀ = g₀ ν_F` of `lem:old-f-law`(a).

By `lem:old-f-law`(a) the weight of a half `x` under `m₀` is proportional to
`[x₀ → x₂](d - 1 - e₀₁ - e₁₂)` on halves of three distinct labels, `d = (p - 1)/2`,
`e₀₁ = [x₀ → x₁]`, `e₁₂ = [x₁ → x₂]`. Here the weight is `oldW` (written with `χ`, and shown to
be this indicator form by `oldW_eq_indicator`), its total is `oldZ`, and the pair laws are its
normalized two-coordinate marginals `m01`, `m12`, `m02` (the law of `(x_i, x_j)` under `m₀`).
With `μ = 2/(p - 4)` (`muF`), over any finite field `F` with `p = |F| ≡ 3 (mod 4)`, `p ≥ 7`:

* `m₁₂(a, b) = m₀₁(a, b) = (1 - μ χ(b - a))/(p(p - 1))` for `a ≠ b` (`m12_eq`, `m01_eq`);
* `m₀₂` is uniform on the pairs `a → b` (`m02_eq`), and every `m_{ij}(a, a) = 0`;
* the total weight is `p(p - 1)(p - 3)(p - 4)/4` (`oldZ_eq`), and the weights are nonnegative
  (`oldW_nonneg`), so `m₀ = oldW/oldZ` is a probability law.

The paper derives `m₀₁` from `m₁₂` by the reflected transpose `ς`; here both are computed
directly (the same count with the roles of in- and out-neighbours exchanged). The only character
sums used are `∑_x χ(x - a) = 0` and `∑_t χ(t - a) χ(t - a') = -1` for `a ≠ a'` (WP-S's
`sum_chi_shift`, `sum_chi_mul_chi`).

Part (b) is `Sarkozy.MiddleRecords.ActualFeaturesOps`; the Gram identities and first norm claims
of (c) are `ActualFeaturesA3`, `ActualFeaturesA3V0`, `ActualFeaturesNorms`; the synthesis bound
`Γ_A` of (d) is `ActualFeaturesSynthesis`. **Not formalized:** `‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ J_F q r` in (c)
and the block statement (e).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-! ## Character sums in `ℝ` -/

theorem sumR_chi_sub (hF : ringChar F ≠ 2) (b : F) : ∑ x, (χ (b - x) : ℝ) = 0 := by
  have h : ∑ x, χ (b - x) = 0 := by
    rw [← quadraticChar_sum_zero hF]
    exact Equiv.sum_comp (Equiv.subLeft b) (fun x => χ x)
  exact_mod_cast h

theorem sumR_chi_mul (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a b : F}
    (hab : a ≠ b) : ∑ x, (χ (b - x) : ℝ) * (χ (a - x) : ℝ) = -1 := by
  have h := sum_chi_mul_chi hF b a
  rw [ite_eq_right (Ne.symm hab), zero_sub] at h
  have e : ∀ x, (χ (b - x) : ℝ) * (χ (a - x) : ℝ) = ((χ (x - b) * χ (x - a) : ℤ) : ℝ) := by
    intro x
    rw [chi_swap h3 b x, chi_swap h3 a x]
    push_cast
    ring
  simp only [e]
  exact_mod_cast h

/-- `∑_x (c₀ + c₁ χ(b - x) + c₂ χ(a - x) + c₃ χ(b - x) χ(a - x)) = c₀ p - c₃` for `a ≠ b`. -/
theorem sum_lin (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a b : F} (hab : a ≠ b)
    (c₀ c₁ c₂ c₃ : ℝ) :
    ∑ x, (c₀ + c₁ * (χ (b - x) : ℝ) + c₂ * (χ (a - x) : ℝ) +
      c₃ * ((χ (b - x) : ℝ) * (χ (a - x) : ℝ))) = c₀ * qF - c₃ := by
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    sumR_chi_sub hF, sumR_chi_sub hF, sumR_chi_mul hF h3 hab, sum_const, card_univ,
    nsmul_eq_mul]
  ring

omit [Field F] in
/-- Removing two points from a sum. -/
theorem sum_ne_ne {a b : F} (hab : a ≠ b) (f : F → ℝ) :
    ∑ x, (if x ≠ a ∧ x ≠ b then f x else 0) = ∑ x, f x - f a - f b := by
  have key : ∀ x, f x = (if x ≠ a ∧ x ≠ b then f x else 0) + (if x = a then f x else 0) +
      (if x = b then f x else 0) := by
    intro x
    by_cases ha : x = a
    · subst ha
      simp [hab]
    · by_cases hb : x = b
      · subst hb
        simp [ha]
      · simp [ha, hb]
  have h : ∑ x, f x = ∑ x, (if x ≠ a ∧ x ≠ b then f x else 0) + f a + f b := by
    conv_lhs => rw [Finset.sum_congr rfl fun x _ => key x]
    rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq']
    simp
  linarith

/-! ## The weight of `m₀` -/

/-- **The weight of the actual half marginal** `m₀` (`lem:old-f-law`(a)), unnormalized: on
three distinct labels `[x₀ → x₂](d - 1 - e₀₁ - e₁₂)`, in the form
`(1 + χ(x₂ - x₀))(p - 5 - χ(x₁ - x₀) - χ(x₂ - x₁))/4`; zero otherwise. -/
noncomputable def oldW (x₀ x₁ x₂ : F) : ℝ :=
  if x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂ then
    (1 + (χ (x₂ - x₀) : ℝ)) * (qF - 5 - (χ (x₁ - x₀) : ℝ) - (χ (x₂ - x₁) : ℝ)) / 4
  else 0

/-- The arrow indicator `[u → v]`. -/
noncomputable def arrow (u v : F) : ℝ := if χ (v - u) = 1 then 1 else 0

theorem one_add_chi_div_two {u v : F} (h : u ≠ v) : (1 + (χ (v - u) : ℝ)) / 2 = arrow u v := by
  unfold arrow
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr h.symm) with h1 | h1
  · rw [h1]; norm_num
  · rw [h1]; norm_num

/-- **`oldW` is the paper's weight**: on distinct labels,
`oldW x = [x₀ → x₂] (d - 1 - [x₀ → x₁] - [x₁ → x₂])`, `d - 1 = (p - 3)/2`. -/
theorem oldW_eq_indicator {x₀ x₁ x₂ : F} (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂) :
    oldW x₀ x₁ x₂ = arrow x₀ x₂ * ((qF - 3) / 2 - arrow x₀ x₁ - arrow x₁ x₂) := by
  rw [oldW, ite_eq_left (show x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂ from ⟨h01, h02, h12⟩),
    ← one_add_chi_div_two h02, ← one_add_chi_div_two h01,
    ← one_add_chi_div_two h12]
  ring

/-- **The weights are nonnegative** for `p ≥ 7`. -/
theorem oldW_nonneg (h7 : 7 ≤ qF) (x₀ x₁ x₂ : F) : 0 ≤ oldW x₀ x₁ x₂ := by
  unfold oldW
  split_ifs with h
  · have hA : 0 ≤ 1 + (χ (x₂ - x₀) : ℝ) := by
      rcases quadraticChar_dichotomy (sub_ne_zero.mpr h.2.1.symm) with h1 | h1 <;>
        · rw [h1]; norm_num
    have hB : (χ (x₁ - x₀) : ℝ) ≤ 1 := by
      rcases quadraticChar_dichotomy (sub_ne_zero.mpr h.1.symm) with h1 | h1 <;>
        · rw [h1]; norm_num
    have hC : (χ (x₂ - x₁) : ℝ) ≤ 1 := by
      rcases quadraticChar_dichotomy (sub_ne_zero.mpr h.2.2.symm) with h1 | h1 <;>
        · rw [h1]; norm_num
    have : 0 ≤ qF - 5 - (χ (x₁ - x₀) : ℝ) - (χ (x₂ - x₁) : ℝ) := by linarith
    positivity
  · exact le_refl 0

/-! ## The three pair sums -/

theorem chi_sq_one {u v : F} (h : u ≠ v) : (χ (v - u) : ℝ) ^ 2 = 1 := by
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr h.symm) with h1 | h1
  · rw [h1]; norm_num
  · rw [h1]; norm_num

/-- **The `(x₁, x₂)` pair sum**: `∑_{x₀} oldW(x₀, a, b) = (p - 3)(p - 4 - 2χ(b - a))/4`. -/
theorem sum_oldW_x0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a b : F}
    (hab : a ≠ b) :
    ∑ x₀, oldW x₀ a b = (qF - 3) * (qF - 4 - 2 * (χ (b - a) : ℝ)) / 4 := by
  set s : ℝ := (χ (b - a) : ℝ) with hs
  set f : F → ℝ := fun x => (1 + (χ (b - x) : ℝ)) * (qF - 5 - (χ (a - x) : ℝ) - s) / 4 with hf
  have e : ∀ x, oldW x a b = if x ≠ a ∧ x ≠ b then f x else 0 := by
    intro x
    unfold oldW
    by_cases h1 : x ≠ a ∧ x ≠ b
    · rw [ite_eq_left (show x ≠ a ∧ x ≠ b ∧ a ≠ b from ⟨h1.1, h1.2, hab⟩), ite_eq_left h1]
    · rw [ite_eq_right (fun h => h1 ⟨h.1, h.2.1⟩), ite_eq_right h1]
  simp only [e]
  rw [sum_ne_ne hab f]
  have hsum : ∑ x, f x = (qF - 5 - s) / 4 * qF - (-1 / 4) := by
    rw [← sum_lin hF h3 hab ((qF - 5 - s) / 4) ((qF - 5 - s) / 4) (-1 / 4) (-1 / 4)]
    exact sum_congr rfl fun x _ => by rw [hf]; ring
  have hfa : f a = (1 + s) * (qF - 5 - s) / 4 := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero, hs]; ring
  have hfb : f b = (qF - 5) / 4 := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero]
    rw [chi_swap h3 a b, Int.cast_neg, ← hs]; ring
  rw [hsum, hfa, hfb]
  have hs2 : s ^ 2 = 1 := chi_sq_one hab
  linear_combination (1 / 4) * hs2

/-- **The `(x₀, x₁)` pair sum**: `∑_{x₂} oldW(a, b, x₂) = (p - 3)(p - 4 - 2χ(b - a))/4`. -/
theorem sum_oldW_x2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a b : F}
    (hab : a ≠ b) :
    ∑ x₂, oldW a b x₂ = (qF - 3) * (qF - 4 - 2 * (χ (b - a) : ℝ)) / 4 := by
  set s : ℝ := (χ (b - a) : ℝ) with hs
  set f : F → ℝ := fun x => (1 - (χ (a - x) : ℝ)) * (qF - 5 - s + (χ (b - x) : ℝ)) / 4 with hf
  have e : ∀ x, oldW a b x = if x ≠ a ∧ x ≠ b then f x else 0 := by
    intro x
    unfold oldW
    by_cases h1 : x ≠ a ∧ x ≠ b
    · rw [ite_eq_left (show a ≠ b ∧ a ≠ x ∧ b ≠ x from ⟨hab, Ne.symm h1.1, Ne.symm h1.2⟩),
        ite_eq_left h1, hf]
      beta_reduce
      rw [chi_swap h3 x a, chi_swap h3 x b, Int.cast_neg, Int.cast_neg, ← hs]
      ring
    · rw [ite_eq_right (fun h => h1 ⟨Ne.symm h.2.1, Ne.symm h.2.2⟩), ite_eq_right h1]
  simp only [e]
  rw [sum_ne_ne hab f]
  have hsum : ∑ x, f x = (qF - 5 - s) / 4 * qF - (-1 / 4) := by
    rw [← sum_lin hF h3 hab ((qF - 5 - s) / 4) (1 / 4) (-(qF - 5 - s) / 4) (-1 / 4)]
    exact sum_congr rfl fun x _ => by rw [hf]; ring
  have hfa : f a = (qF - 5) / 4 := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero, ← hs]; ring
  have hfb : f b = (1 + s) * (qF - 5 - s) / 4 := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero]
    rw [chi_swap h3 a b, Int.cast_neg, ← hs]; ring
  rw [hsum, hfa, hfb]
  have hs2 : s ^ 2 = 1 := chi_sq_one hab
  linear_combination (1 / 4) * hs2

/-- **The `(x₀, x₂)` pair sum**: `∑_{x₁} oldW(a, x₁, b) = (1 + χ(b - a))(p - 3)(p - 4)/4`. -/
theorem sum_oldW_x1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a b : F}
    (hab : a ≠ b) :
    ∑ x₁, oldW a x₁ b = (1 + (χ (b - a) : ℝ)) * (qF - 3) * (qF - 4) / 4 := by
  set s : ℝ := (χ (b - a) : ℝ) with hs
  set f : F → ℝ := fun x => (1 + s) * (qF - 5 + (χ (a - x) : ℝ) - (χ (b - x) : ℝ)) / 4 with hf
  have e : ∀ x, oldW a x b = if x ≠ a ∧ x ≠ b then f x else 0 := by
    intro x
    unfold oldW
    by_cases h1 : x ≠ a ∧ x ≠ b
    · rw [ite_eq_left (show a ≠ x ∧ a ≠ b ∧ x ≠ b from ⟨Ne.symm h1.1, hab, h1.2⟩),
        ite_eq_left h1, hf]
      beta_reduce
      rw [chi_swap h3 x a, Int.cast_neg, ← hs]
      ring
    · rw [ite_eq_right (fun h => h1 ⟨Ne.symm h.1, h.2.2⟩), ite_eq_right h1]
  simp only [e]
  rw [sum_ne_ne hab f]
  have hsum : ∑ x, f x = (1 + s) * (qF - 5) / 4 * qF - 0 := by
    rw [← sum_lin hF h3 hab ((1 + s) * (qF - 5) / 4) (-(1 + s) / 4) ((1 + s) / 4) 0]
    exact sum_congr rfl fun x _ => by rw [hf]; ring
  have hfa : f a = (1 + s) * (qF - 5 - s) / 4 := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero, ← hs]; ring
  have hfb : f b = (1 + s) * (qF - 5 - s) / 4 := by
    simp only [hf, sub_self, quadraticChar_zero, Int.cast_zero]
    rw [chi_swap h3 a b, Int.cast_neg, ← hs]; ring
  rw [hsum, hfa, hfb]
  have hs2 : s ^ 2 = 1 := chi_sq_one hab
  linear_combination (1 / 2) * hs2

/-- The pair sums vanish on the diagonal. -/
theorem oldW_diag_x0 (a x : F) : oldW x a a = 0 := by
  unfold oldW; rw [ite_eq_right (fun h => h.2.2 rfl)]

theorem oldW_diag_x2 (a x : F) : oldW a a x = 0 := by
  unfold oldW; rw [ite_eq_right (fun h => h.1 rfl)]

theorem oldW_diag_x1 (a x : F) : oldW a x a = 0 := by
  unfold oldW; rw [ite_eq_right (fun h => h.2.1 rfl)]

/-! ## The normalization and the pair laws -/

/-- The total weight `Z = ∑_x oldW(x)`. -/
noncomputable def oldZ : ℝ := ∑ x₀, ∑ x₁, ∑ x₂, oldW (F := F) x₀ x₁ x₂

theorem sumR_chi_pairs (hF : ringChar F ≠ 2) : ∑ a, ∑ b, (χ (b - a) : ℝ) = 0 := by
  have h : ∀ a, ∑ b, (χ (b - a) : ℝ) = 0 := by
    intro a
    have := sum_chi_shift hF a
    exact_mod_cast this
  simp only [h, sum_const_zero]

/-- **The total weight** `Z = p(p - 1)(p - 3)(p - 4)/4`. -/
theorem oldZ_eq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) :
    oldZ (F := F) = qF * (qF - 1) * (qF - 3) * (qF - 4) / 4 := by
  -- sum over `x₀` last: `Z = ∑_{x₁, x₂} ∑_{x₀} oldW`
  have hZ : oldZ (F := F) = ∑ a, ∑ b, ∑ x₀, oldW (F := F) x₀ a b := by
    unfold oldZ
    rw [Finset.sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  have hab : ∀ a b : F, ∑ x₀, oldW x₀ a b =
      (qF - 3) * (qF - 4) / 4 * (if a = b then 0 else 1) -
        (qF - 3) / 2 * (χ (b - a) : ℝ) := by
    intro a b
    by_cases h : a = b
    · subst h
      rw [ite_eq_left (show a = a from rfl), sub_self, quadraticChar_zero]
      simp only [oldW_diag_x0, sum_const_zero, Int.cast_zero]
      ring
    · rw [sum_oldW_x0 hF h3 h, ite_eq_right h]
      ring
  rw [hZ]
  simp only [hab, sum_sub_distrib, ← mul_sum]
  rw [sumR_chi_pairs hF]
  have hcount : ∑ a : F, ∑ b : F, (if a = b then (0 : ℝ) else 1) = qF * (qF - 1) := by
    have : ∀ a : F, ∑ b : F, (if a = b then (0 : ℝ) else 1) = qF - 1 := by
      intro a
      have h1 : ∑ b : F, (if a = b then (0 : ℝ) else 1) =
          ∑ b : F, ((1 : ℝ) - if a = b then 1 else 0) :=
        sum_congr rfl fun b _ => by split_ifs <;> norm_num
      rw [h1, sum_sub_distrib, sum_ite_eq, sum_const, card_univ, nsmul_eq_mul]
      simp
    simp only [this, sum_const, card_univ, nsmul_eq_mul]
  rw [hcount]
  ring

/-- The law of `(x₁, x₂)` under `m₀`. -/
noncomputable def m12 (a b : F) : ℝ := (∑ x₀, oldW x₀ a b) / oldZ (F := F)

/-- The law of `(x₀, x₁)` under `m₀`. -/
noncomputable def m01 (a b : F) : ℝ := (∑ x₂, oldW a b x₂) / oldZ (F := F)

/-- The law of `(x₀, x₂)` under `m₀`. -/
noncomputable def m02 (a b : F) : ℝ := (∑ x₁, oldW a x₁ b) / oldZ (F := F)

/-- `μ = 2/(p - 4)`. -/
noncomputable def muF : ℝ := 2 / (qF - 4)

theorem oldZ_pos (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) :
    0 < oldZ (F := F) := by
  rw [oldZ_eq hF h3]
  have : 0 < qF - 4 := by linarith
  have : 0 < qF - 3 := by linarith
  have : 0 < qF - 1 := by linarith
  have : 0 < qF := by linarith
  positivity

/-- **`lem:actual-features`(a), `m₁₂`**: `m₁₂(a, b) = (1 - μ χ(b - a))/(p(p - 1))` for
`a ≠ b`. -/
theorem m12_eq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) {a b : F}
    (hab : a ≠ b) : m12 a b = (1 - muF (F := F) * (χ (b - a) : ℝ)) / (qF * (qF - 1)) := by
  unfold m12 muF
  rw [sum_oldW_x0 hF h3 hab, oldZ_eq hF h3]
  have h4 : qF - 4 ≠ 0 := by intro h; linarith
  have h3' : qF - 3 ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp

/-- **`lem:actual-features`(a), `m₀₁`**: `m₀₁(a, b) = (1 - μ χ(b - a))/(p(p - 1))` for
`a ≠ b`. -/
theorem m01_eq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) {a b : F}
    (hab : a ≠ b) : m01 a b = (1 - muF (F := F) * (χ (b - a) : ℝ)) / (qF * (qF - 1)) := by
  unfold m01 muF
  rw [sum_oldW_x2 hF h3 hab, oldZ_eq hF h3]
  have h4 : qF - 4 ≠ 0 := by intro h; linarith
  have h3' : qF - 3 ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp

/-- **`lem:actual-features`(a), `m₀₂`**: `m₀₂` is uniform on the `p(p - 1)/2` pairs `a → b`:
`m₀₂(a, b) = [a → b] · 2/(p(p - 1))` for `a ≠ b`. -/
theorem m02_eq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) {a b : F}
    (hab : a ≠ b) : m02 a b = arrow a b * (2 / (qF * (qF - 1))) := by
  unfold m02
  rw [sum_oldW_x1 hF h3 hab, oldZ_eq hF h3, ← one_add_chi_div_two hab]
  have h4 : qF - 4 ≠ 0 := by intro h; linarith
  have h3' : qF - 3 ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp

/-- The pair laws vanish on the diagonal. -/
theorem m_diag (a : F) : m12 a a = 0 ∧ m01 a a = 0 ∧ m02 a a = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold m12; simp only [oldW_diag_x0, sum_const_zero, zero_div]
  · unfold m01; simp only [oldW_diag_x2, sum_const_zero, zero_div]
  · unfold m02; simp only [oldW_diag_x1, sum_const_zero, zero_div]

end Sarkozy.MiddleRecords
