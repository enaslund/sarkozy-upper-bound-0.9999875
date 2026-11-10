module

public import Sarkozy.TraceMixing.Kernel
public import Sarkozy.Labellings.Extension

/-!
# The Paley tournament (`lem:paley-triple`(a)–(c))

`paper/sections/12_labellings.tex`, `lem:paley-triple`, over any finite field `F` with `q`
elements and odd characteristic; `a → b` means `χ(b - a) = 1`. Unconditional (the only
character sum used is the two-root identity `Sarkozy.Labellings.two_root`).

* `card_sign_pair`: for `a ≠ a'` and signs `σ, σ'`,
  `4 · #{c : χ(c - a) = σ, χ(c - a') = σ'} = q - 2 - σ' χ(a - a') - σ χ(a' - a) - σσ'`.
* (a), for `q ≡ 3 (mod 4)` and `k = (q - 3)/4`:
  - `paley_tournament`: exactly one of `a → b`, `b → a`;
  - `card_out`, `card_in`: `(q - 1)/2` out-neighbours and `(q - 1)/2` in-neighbours, stated as
    `2 · # = q - 1`;
  - `card_common_out`, `card_common_in`: `k` common out- and in-neighbours of `a ≠ a'`,
    stated as `4 · # = q - 3`;
  - `card_path`: `#{c : a → c → a'} = k + 1 - [a → a']`, stated as
    `4 · # = q + 1 - 4 [a → a']`.
* (b) `sum_chi_mul_chi`: `∑_t χ(t - a) χ(t - a') = q [a = a'] - 1`, i.e.
  `E_t χ(t - a) χ(t - a') = [a = a'] - 1/q` (any odd `q`).
* (c) the Paley operator `(P h)(s) = E_t χ(t - s) h(t)` (`paleyOp`): `paleyOp_const` (`P 1 = 0`),
  `paleyOp_adjoint` (`⟨P g, h⟩ = -⟨g, P h⟩` for `q ≡ 3 (mod 4)`, i.e. `P^* = -P`) and
  `norm_paleyOp` (`‖P h‖² = q⁻¹ (‖h‖² - (E h)²)`, i.e. `P^*P = q⁻¹(I - J)` and `‖P‖ = q^{-1/2}`
  on the mean-zero functions), norms for the uniform law.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer. -/
local notation "χ" => quadraticChar F

theorem chi_sq_eq (x : F) : (χ x) ^ 2 = if x = 0 then 0 else 1 := by
  split_ifs with h
  · rw [h, quadraticChar_zero]
    norm_num
  · exact quadraticChar_sq_one h

theorem sum_chi_shift (hF : ringChar F ≠ 2) (a : F) : ∑ c, χ (c - a) = 0 := by
  rw [← quadraticChar_sum_zero hF]
  exact Equiv.sum_comp (Equiv.subRight a) (fun x => χ x)

/-- The indicator of `χ(x) = σ` is `(χ(x)² + σ χ(x))/2`. -/
theorem two_mul_indicator (x : F) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    2 * (if χ x = σ then (1 : ℤ) else 0) = (χ x) ^ 2 + σ * χ x := by
  by_cases hx : x = 0
  · subst hx
    rw [quadraticChar_zero]
    rcases hσ with rfl | rfl <;> norm_num
  · rcases quadraticChar_dichotomy hx with h | h <;> rcases hσ with rfl | rfl <;>
      rw [h] <;> norm_num

/-- **The basic count.** For `a ≠ a'` and signs `σ, σ'`:
`4 · #{c : χ(c - a) = σ, χ(c - a') = σ'} = q - 2 - σ' χ(a - a') - σ χ(a' - a) - σσ'`. -/
theorem card_sign_pair (hF : ringChar F ≠ 2) {a a' : F} (haa : a ≠ a') {σ σ' : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1) :
    4 * ((univ.filter fun c => χ (c - a) = σ ∧ χ (c - a') = σ').card : ℤ) =
      Fintype.card F - 2 - σ' * χ (a - a') - σ * χ (a' - a) - σ * σ' := by
  have hind (c : F) : 4 * (if χ (c - a) = σ ∧ χ (c - a') = σ' then (1 : ℤ) else 0) =
      ((χ (c - a)) ^ 2 + σ * χ (c - a)) * ((χ (c - a')) ^ 2 + σ' * χ (c - a')) := by
    rw [← two_mul_indicator _ hσ, ← two_mul_indicator _ hσ']
    split_ifs <;> simp_all
  have hcard : ((univ.filter fun c => χ (c - a) = σ ∧ χ (c - a') = σ').card : ℤ) =
      ∑ c, (if χ (c - a) = σ ∧ χ (c - a') = σ' then (1 : ℤ) else 0) := by
    rw [Finset.sum_boole]
  rw [hcard, Finset.mul_sum]
  simp only [hind]
  -- the four sums
  have hsq (c b : F) : (χ (c - b)) ^ 2 = 1 - (if c = b then 1 else 0) := by
    rw [chi_sq_eq]
    by_cases h : c = b
    · subst h
      simp
    · rw [ite_eq_right (sub_ne_zero.mpr h), ite_eq_right h]
      ring
  have hS1 : ∑ c, (χ (c - a)) ^ 2 * (χ (c - a')) ^ 2 = Fintype.card F - 2 := by
    simp only [hsq]
    have h (c : F) : (1 - (if c = a then (1 : ℤ) else 0)) * (1 - (if c = a' then 1 else 0)) =
        1 - (if c = a then 1 else 0) - (if c = a' then 1 else 0) := by
      by_cases h1 : c = a
      · subst h1
        simp [haa]
      · by_cases h2 : c = a'
        · subst h2
          simp [h1]
        · simp [h1, h2]
    simp only [h, Finset.sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq', mem_univ, ite_true]
    ring
  have hS2 : ∑ c, (χ (c - a)) ^ 2 * χ (c - a') = -χ (a - a') := by
    simp only [hsq, sub_mul, one_mul, Finset.sum_sub_distrib, sum_chi_shift hF, ite_mul,
      zero_mul, Finset.sum_ite_eq', mem_univ, ite_true]
    ring
  have hS3 : ∑ c, χ (c - a) * (χ (c - a')) ^ 2 = -χ (a' - a) := by
    simp only [hsq, mul_sub, mul_one, Finset.sum_sub_distrib, sum_chi_shift hF, mul_ite,
      mul_zero, Finset.sum_ite_eq', mem_univ, ite_true]
    ring
  have hS4 : ∑ c, χ (c - a) * χ (c - a') = -1 := by
    have h := two_root hF haa
    unfold rootSum at h
    rw [← h]
    apply sum_congr rfl
    intro c _
    rw [prod_pair haa, map_mul]
  have hexp (c : F) : ((χ (c - a)) ^ 2 + σ * χ (c - a)) * ((χ (c - a')) ^ 2 + σ' * χ (c - a')) =
      (χ (c - a)) ^ 2 * (χ (c - a')) ^ 2 + σ' * ((χ (c - a)) ^ 2 * χ (c - a')) +
        σ * (χ (c - a) * (χ (c - a')) ^ 2) + σ * σ' * (χ (c - a) * χ (c - a')) := by
    ring
  simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hS1, hS2, hS3, hS4]
  ring

/-- `χ(-1) = -1` when `q ≡ 3 (mod 4)`. -/
theorem chi_neg_one_of_three (h3 : Fintype.card F % 4 = 3) : χ (-1) = -1 :=
  quadraticChar_neg_one_iff_not_isSquare.mpr (by
    rw [FiniteField.isSquare_neg_one_iff]
    omega)

theorem chi_swap (h3 : Fintype.card F % 4 = 3) (a b : F) : χ (a - b) = -χ (b - a) := by
  have : a - b = -1 * (b - a) := by ring
  rw [this, map_mul, chi_neg_one_of_three h3]
  ring

/-- **(a) The Paley relation is a tournament**: for `a ≠ b` exactly one of `a → b`,
`b → a` holds. -/
theorem paley_tournament (h3 : Fintype.card F % 4 = 3) {a b : F} (hab : a ≠ b) :
    χ (b - a) = 1 ↔ ¬ χ (a - b) = 1 := by
  rw [chi_swap h3 a b]
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm hab)) with h | h <;> rw [h] <;>
    norm_num

/-- **(a) Out-degrees**: `2 · #{b : a → b} = q - 1`. -/
theorem card_out (hF : ringChar F ≠ 2) (a : F) :
    2 * ((univ.filter fun b => χ (b - a) = 1).card : ℤ) = Fintype.card F - 1 := by
  have hcard : ((univ.filter fun b => χ (b - a) = 1).card : ℤ) =
      ∑ b, (if χ (b - a) = 1 then (1 : ℤ) else 0) := by rw [Finset.sum_boole]
  rw [hcard, Finset.mul_sum]
  simp only [two_mul_indicator _ (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1), one_mul,
    Finset.sum_add_distrib, sum_chi_shift hF]
  have h (b : F) : (χ (b - a)) ^ 2 = 1 - (if b = a then 1 else 0) := by
    rw [chi_sq_eq]
    by_cases hb : b = a
    · subst hb
      simp
    · rw [ite_eq_right (sub_ne_zero.mpr hb), ite_eq_right hb]
      ring
  simp only [h, Finset.sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
    Finset.sum_ite_eq', mem_univ, ite_true]
  ring

/-- **(a) In-degrees**: `2 · #{b : b → a} = q - 1` when `q ≡ 3 (mod 4)`. -/
theorem card_in (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a : F) :
    2 * ((univ.filter fun b => χ (a - b) = 1).card : ℤ) = Fintype.card F - 1 := by
  have h := card_out hF a
  have hfilt : (univ.filter fun b => χ (a - b) = 1) =
      univ.filter fun b => χ (b - a) = -1 := by
    ext b
    simp only [mem_filter, mem_univ, true_and, chi_swap h3 a b]
    constructor <;> intro hb <;> linarith
  have hsplit : ((univ.filter fun b => χ (b - a) = 1).card : ℤ) +
      ((univ.filter fun b => χ (b - a) = -1).card : ℤ) = Fintype.card F - 1 := by
    have h1 := card_out hF a
    have hsum : ∑ b, χ (b - a) = 0 := sum_chi_shift hF a
    have hcard1 : ((univ.filter fun b => χ (b - a) = 1).card : ℤ) =
        ∑ b, (if χ (b - a) = 1 then (1 : ℤ) else 0) := by rw [Finset.sum_boole]
    have hcard2 : ((univ.filter fun b => χ (b - a) = -1).card : ℤ) =
        ∑ b, (if χ (b - a) = -1 then (1 : ℤ) else 0) := by rw [Finset.sum_boole]
    have hpt (b : F) : (if χ (b - a) = 1 then (1 : ℤ) else 0) -
        (if χ (b - a) = -1 then (1 : ℤ) else 0) = χ (b - a) := by
      by_cases hb : b = a
      · subst hb
        simp
      · rcases quadraticChar_dichotomy (sub_ne_zero.mpr hb) with h' | h' <;> simp [h']
    have hdiff : ((univ.filter fun b => χ (b - a) = 1).card : ℤ) -
        ((univ.filter fun b => χ (b - a) = -1).card : ℤ) = 0 := by
      rw [hcard1, hcard2, ← Finset.sum_sub_distrib]
      simp only [hpt]
      exact hsum
    linarith
  rw [hfilt]
  linarith

/-- **(a) Common out-neighbours**: `4 · #{c : a → c, a' → c} = q - 3` for `a ≠ a'`,
`q ≡ 3 (mod 4)`. -/
theorem card_common_out (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a a' : F}
    (haa : a ≠ a') :
    4 * ((univ.filter fun c => χ (c - a) = 1 ∧ χ (c - a') = 1).card : ℤ) =
      Fintype.card F - 3 := by
  rw [card_sign_pair hF haa (Or.inl rfl) (Or.inl rfl), chi_swap h3 a' a]
  ring

/-- **(a) Common in-neighbours**: `4 · #{c : c → a, c → a'} = q - 3` for `a ≠ a'`,
`q ≡ 3 (mod 4)`. -/
theorem card_common_in (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a a' : F}
    (haa : a ≠ a') :
    4 * ((univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1).card : ℤ) =
      Fintype.card F - 3 := by
  have hfilt : (univ.filter fun c => χ (a - c) = 1 ∧ χ (a' - c) = 1) =
      univ.filter fun c => χ (c - a) = -1 ∧ χ (c - a') = -1 := by
    ext c
    simp only [mem_filter, mem_univ, true_and, chi_swap h3 a c, chi_swap h3 a' c]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hfilt, card_sign_pair hF haa (Or.inr rfl) (Or.inr rfl), chi_swap h3 a' a]
  ring

/-- **(a) Paths of length two**: `#{c : a → c → a'} = k + 1 - [a → a']`, `k = (q - 3)/4`,
stated as `4 · # = q + 1 - 4 [a → a']`. -/
theorem card_path (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {a a' : F}
    (haa : a ≠ a') :
    4 * ((univ.filter fun c => χ (c - a) = 1 ∧ χ (a' - c) = 1).card : ℤ) =
      Fintype.card F + 1 - 4 * (if χ (a' - a) = 1 then 1 else 0) := by
  have hfilt : (univ.filter fun c => χ (c - a) = 1 ∧ χ (a' - c) = 1) =
      univ.filter fun c => χ (c - a) = 1 ∧ χ (c - a') = -1 := by
    ext c
    simp only [mem_filter, mem_univ, true_and, chi_swap h3 a' c]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  rw [hfilt, card_sign_pair hF haa (Or.inl rfl) (Or.inr rfl), chi_swap h3 a a']
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm haa)) with h | h <;> rw [h] <;>
    norm_num <;> ring

/-- **(b) Character correlations**: `∑_t χ(t - a) χ(t - a') = q [a = a'] - 1`. -/
theorem sum_chi_mul_chi (hF : ringChar F ≠ 2) (a a' : F) :
    ∑ t, χ (t - a) * χ (t - a') = (if a = a' then (Fintype.card F : ℤ) else 0) - 1 := by
  by_cases h : a = a'
  · subst h
    rw [ite_eq_left rfl]
    have hsq (t : F) : χ (t - a) * χ (t - a) = 1 - (if t = a then 1 else 0) := by
      rw [← sq, chi_sq_eq]
      by_cases ht : t = a
      · subst ht
        simp
      · rw [ite_eq_right (sub_ne_zero.mpr ht), ite_eq_right ht]
        ring
    simp only [hsq, Finset.sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq', mem_univ, ite_true]
  · rw [ite_eq_right h, zero_sub]
    have h2 := two_root hF h
    unfold rootSum at h2
    rw [← h2]
    apply sum_congr rfl
    intro c _
    rw [prod_pair h, map_mul]

/-- The Paley operator `(P h)(s) = E_t χ(t - s) h(t)`. -/
noncomputable def paleyOp (h : F → ℝ) (s : F) : ℝ :=
  (Fintype.card F : ℝ)⁻¹ * ∑ t, (χ (t - s) : ℝ) * h t

/-- **(c) `P 1 = 0`.** -/
theorem paleyOp_const (hF : ringChar F ≠ 2) (c : ℝ) (s : F) : paleyOp (fun _ => c) s = 0 := by
  unfold paleyOp
  rw [← Finset.sum_mul]
  have : ∑ t, (χ (t - s) : ℝ) = 0 := by exact_mod_cast sum_chi_shift hF s
  rw [this, zero_mul, mul_zero]

/-- **(c) `P^* = -P`** for `q ≡ 3 (mod 4)`: `∑_s (P g)(s) h(s) = -∑_s g(s) (P h)(s)`. -/
theorem paleyOp_adjoint (h3 : Fintype.card F % 4 = 3) (g h : F → ℝ) :
    ∑ s, paleyOp g s * h s = -∑ s, g s * paleyOp h s := by
  unfold paleyOp
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_neg_distrib, Finset.sum_comm]
  apply sum_congr rfl
  intro t _
  rw [← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro s _
  have : (χ (t - s) : ℝ) = -(χ (s - t) : ℝ) := by exact_mod_cast chi_swap h3 t s
  rw [this]
  ring

/-- **(c) `P^*P = q⁻¹(I - J)`**: `E_s (P h)(s)² = q⁻¹ (E_s h(s)² - (E_s h(s))²)`, so `P` has
norm `q^{-1/2}` on the mean-zero functions. -/
theorem norm_paleyOp (hF : ringChar F ≠ 2) (h : F → ℝ) :
    (Fintype.card F : ℝ)⁻¹ * ∑ s, paleyOp h s ^ 2 =
      (Fintype.card F : ℝ)⁻¹ * ((Fintype.card F : ℝ)⁻¹ * ∑ s, h s ^ 2 -
        ((Fintype.card F : ℝ)⁻¹ * ∑ s, h s) ^ 2) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : q ≠ 0 := by rw [hq]; exact_mod_cast Fintype.card_ne_zero
  have hcorr (t t' : F) : ∑ s, (χ (t - s) : ℝ) * (χ (t' - s) : ℝ) =
      (if t = t' then q else 0) - 1 := by
    have h1 : ∑ s, (χ (t - s) : ℝ) * (χ (t' - s) : ℝ) = ∑ s, (χ (s - t) : ℝ) * (χ (s - t') : ℝ) := by
      apply sum_congr rfl
      intro s _
      have e1 : (χ (t - s) : ℤ) * χ (t' - s) = χ (s - t) * χ (s - t') := by
        rw [← map_mul, ← map_mul]
        congr 1
        ring
      exact_mod_cast e1
    rw [h1]
    have := sum_chi_mul_chi hF t t'
    have h2 : ∑ s, (χ (s - t) : ℝ) * (χ (s - t') : ℝ) = (((if t = t' then (Fintype.card F : ℤ) else 0) - 1 : ℤ) : ℝ) := by
      rw [← this]
      push_cast
      rfl
    rw [h2]
    split_ifs <;> push_cast <;> ring
  have hexp : ∑ s, paleyOp h s ^ 2 =
      q⁻¹ ^ 2 * ∑ t, ∑ t', h t * h t' * ∑ s, (χ (t - s) : ℝ) * (χ (t' - s) : ℝ) := by
    have h1 (s : F) : paleyOp h s ^ 2 =
        q⁻¹ ^ 2 * ∑ t, ∑ t', h t * h t' * ((χ (t - s) : ℝ) * (χ (t' - s) : ℝ)) := by
      unfold paleyOp
      rw [mul_pow, pow_two (∑ t, (χ (t - s) : ℝ) * h t), Finset.sum_mul_sum]
      congr 1
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro t' _
      ring
    simp only [h1]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro t _
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro t' _
    rw [Finset.mul_sum]
  rw [hexp]
  simp only [hcorr, mul_sub, mul_ite, mul_zero, mul_one, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, mem_univ, ite_true]
  have h4 : ∑ t, ∑ t', h t * h t' = (∑ s, h s) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [h4]
  have h5 : ∑ t, h t * h t * q = q * ∑ s, h s ^ 2 := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  rw [h5]
  field_simp

end Sarkozy.TraceMixing
