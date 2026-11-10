module

public import Sarkozy.NormBoundsPaper2.PrimeBounds

@[expose] public section

/-!
# Character kernels and collisions on ordered pairs (NB2)

`paper/sections/21_middle_records.tex`, proof of `lem:merge-repair`, paragraph "The mirror law":
"Put `z = (p − 2)(p − 3)/(p(p − 1))` and `τ = 1 − z`. Then `D_p` is the indicator of disjoint halves
divided by `z`, and the deleted collision kernel has constant row and column mass `τ`. On
independent
field pairs the two-edge character kernel `CH` has norm `1/p` … Schur's bound on the collision
kernel …". In unnormalized form, on `𝔽_p × 𝔽_p`:

* `chi_sq_le`: `∑_a (∑_c χ(c − a) f(c))² ≤ p ∑ f²` (JointRows' `Φ̂² = −(I − J)`);
  `chi_form_le`: `|∑_a G(a) ∑_c χ(c − a) H(c)| ≤ √p ‖G‖ ‖H‖`;
* **`two_chi_le`**: the two-edge kernel `χ(y₀ − x₁) χ(y₁ − x₀)` has form norm `≤ p` on
  `ℓ²(𝔽_p²)` (the paper's `1/p` after normalization by `p²`);
* `coll x y = [x₀ ≠ x₁][y₀ ≠ y₁] − ind4 x y`, the collision kernel: `coll_nonneg`, `coll_symm`,
  **`sum_coll_row`** (row mass `4p − 6`, i.e. `τ p(p − 1)`); **`schur_le`** (Schur's test);
* **`rows_cols_le`**: for `g` vanishing on the diagonal with `∑ g = 0`, the row and column sums
  satisfy `∑ G₀² + ∑ G₁² ≤ p ∑ g²` (the paper's "the singleton embeddings on mean-zero functions
  satisfy `V_i^* V_i = I` and `V₀^* V₁ = V₁^* V₀ = −η^G_p I`", in the form
  `‖V₀^* u‖² + ‖V₁^* u‖² ≤ (1 + η^G_p) ‖u‖²`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

open Sarkozy.NormBoundsPaper (p_gt_one)
open Sarkozy.JointRows.PaleyGauss (chiR paley paley_anti paley_sq chiR_neg chiR_zero chiR_sq)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

theorem chiR_abs_le (d : ZMod p) : |chiR p d| ≤ 1 := by
  by_cases hd : d = 0
  · rw [hd, chiR_zero]; norm_num
  · have h := chiR_sq hd
    have : |chiR p d| * |chiR p d| = 1 := by rw [← abs_mul, h, abs_one]
    nlinarith [abs_nonneg (chiR p d)]

/-- `∑_c χ(c − a) f(c) = √p Φ̂f(a)`. -/
theorem chi_sum_eq (f : ZMod p → ℝ) (a : ZMod p) :
    ∑ c, chiR p (c - a) * f c = Real.sqrt p * paley p f a := by
  have hp0 : (0 : ℝ) < p := by have := p_gt_one (p := p); linarith
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  unfold paley
  rw [← mul_assoc, show Real.sqrt p * (Real.sqrt p / p) = 1 by
    rw [← mul_div_assoc, hsq, div_self hp0.ne'], one_mul]

/-- `∑_a (∑_c χ(c − a) f(c))² ≤ p ∑ f²`. -/
theorem chi_sq_le (h3 : p % 4 = 3) (f : ZMod p → ℝ) :
    ∑ a, (∑ c, chiR p (c - a) * f c) ^ 2 ≤ p * ∑ a, f a ^ 2 := by
  have hp0 : (0 : ℝ) < p := by have := p_gt_one (p := p); linarith
  have hiso : ∑ a, paley p f a ^ 2 = ∑ a, f a ^ 2 - (∑ c, f c) ^ 2 / p := by
    have := paley_anti h3 (paley p f) f
    simp only [paley_sq h3] at this
    rw [show ∑ a, paley p f a ^ 2 = ∑ t, paley p f t * paley p f t from
      sum_congr rfl fun t _ => sq _, this]
    simp only [neg_mul, sum_neg_distrib, neg_neg, sub_mul, sum_sub_distrib]
    rw [← mul_sum]
    have e : ∑ t, f t * f t = ∑ a, f a ^ 2 := sum_congr rfl fun t _ => (sq _).symm
    rw [e]
    ring
  simp only [chi_sum_eq, mul_pow, Real.sq_sqrt hp0.le, ← mul_sum, hiso]
  have : 0 ≤ (∑ c, f c) ^ 2 / p := div_nonneg (sq_nonneg _) hp0.le
  nlinarith

omit [Fact p.Prime] in
theorem abs_sum_mul_le (s : Finset (ZMod p)) (G H : ZMod p → ℝ) :
    |∑ a ∈ s, G a * H a| ≤ Real.sqrt (∑ a ∈ s, G a ^ 2) * Real.sqrt (∑ a ∈ s, H a ^ 2) := by
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt s G H
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt s (fun a => -G a) H
  simp only [neg_sq, neg_mul, sum_neg_distrib] at h2
  rw [abs_le]
  constructor <;> linarith

/-- `|∑_a G(a) ∑_c χ(c − a) H(c)| ≤ √p ‖G‖ ‖H‖`. -/
theorem chi_form_le (h3 : p % 4 = 3) (G H : ZMod p → ℝ) :
    |∑ a, G a * ∑ c, chiR p (c - a) * H c| ≤
      Real.sqrt p * Real.sqrt (∑ a, G a ^ 2) * Real.sqrt (∑ a, H a ^ 2) := by
  have hp0 : (0 : ℝ) < p := by have := p_gt_one (p := p); linarith
  refine (abs_sum_mul_le univ G _).trans ?_
  have h := Real.sqrt_le_sqrt (chi_sq_le h3 H)
  rw [Real.sqrt_mul hp0.le] at h
  calc Real.sqrt (∑ a, G a ^ 2) * Real.sqrt (∑ a, (∑ c, chiR p (c - a) * H c) ^ 2)
      ≤ Real.sqrt (∑ a, G a ^ 2) * (Real.sqrt p * Real.sqrt (∑ a, H a ^ 2)) :=
        mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = _ := by ring

/-! ## The two-edge character kernel -/

/-- **The two-edge kernel** `χ(y₀ − x₁) χ(y₁ − x₀)` has form norm at most `p` on `ℓ²(𝔽_p²)`. -/
theorem two_chi_le (h3 : p % 4 = 3) (g h : ZMod p × ZMod p → ℝ) :
    |∑ x, ∑ y, g x * h y * (chiR p (y.1 - x.2) * chiR p (y.2 - x.1))| ≤
      p * Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (∑ x, h x ^ 2) := by
  have hp0 : (0 : ℝ) < p := by have := p_gt_one (p := p); linarith
  -- `k(x₁, y₁) = ∑_{y₀} χ(y₀ − x₁) h(y₀, y₁)`, `Wv(x₀, x₁) = ∑_{y₁} χ(y₁ − x₀) k(x₁, y₁)`
  set k : ZMod p → ZMod p → ℝ := fun x₁ y₁ => ∑ y₀, chiR p (y₀ - x₁) * h (y₀, y₁)
  set Wv : ZMod p × ZMod p → ℝ := fun x => ∑ y₁, chiR p (y₁ - x.1) * k x.2 y₁
  have hform : ∑ x, ∑ y, g x * h y * (chiR p (y.1 - x.2) * chiR p (y.2 - x.1)) =
      ∑ x, g x * Wv x := by
    refine sum_congr rfl fun x _ => ?_
    simp only [Wv, k, mul_sum, Fintype.sum_prod_type]
    rw [sum_comm]
    refine sum_congr rfl fun y₁ _ => sum_congr rfl fun y₀ _ => ?_
    ring
  have hW : ∑ x, Wv x ^ 2 ≤ (p : ℝ) ^ 2 * ∑ x, h x ^ 2 := by
    have h1 : ∀ x₁, ∑ x₀, Wv (x₀, x₁) ^ 2 ≤ p * ∑ y₁, k x₁ y₁ ^ 2 :=
      fun x₁ => chi_sq_le h3 (k x₁)
    have h2 : ∀ y₁, ∑ x₁, k x₁ y₁ ^ 2 ≤ p * ∑ y₀, h (y₀, y₁) ^ 2 :=
      fun y₁ => chi_sq_le h3 (fun y₀ => h (y₀, y₁))
    calc ∑ x, Wv x ^ 2 = ∑ x₁, ∑ x₀, Wv (x₀, x₁) ^ 2 := by
          rw [Fintype.sum_prod_type, sum_comm]
      _ ≤ ∑ x₁, p * ∑ y₁, k x₁ y₁ ^ 2 := sum_le_sum fun x₁ _ => h1 x₁
      _ = p * ∑ y₁, ∑ x₁, k x₁ y₁ ^ 2 := by rw [← mul_sum, sum_comm]
      _ ≤ p * ∑ y₁, p * ∑ y₀, h (y₀, y₁) ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun y₁ _ => h2 y₁) hp0.le
      _ = (p : ℝ) ^ 2 * ∑ x, h x ^ 2 := by
          rw [← mul_sum, Fintype.sum_prod_type, sum_comm]
          ring
  rw [hform]
  refine (abs_sum_mul_le' g Wv).trans ?_
  have hs := Real.sqrt_le_sqrt hW
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp0.le] at hs
  calc Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (∑ x, Wv x ^ 2)
      ≤ Real.sqrt (∑ x, g x ^ 2) * (p * Real.sqrt (∑ x, h x ^ 2)) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    _ = _ := by ring
where
  abs_sum_mul_le' (G H : ZMod p × ZMod p → ℝ) :
      |∑ a, G a * H a| ≤ Real.sqrt (∑ a, G a ^ 2) * Real.sqrt (∑ a, H a ^ 2) := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt univ G H
    have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun a => -G a) H
    simp only [neg_sq, neg_mul, sum_neg_distrib] at h2
    rw [abs_le]
    constructor <;> linarith

/-! ## Collisions and Schur's test -/

/-- **Schur's test**: a nonnegative kernel with row and column sums at most `R`. -/
theorem schur_le {B : Type} [Fintype B] (K : B → B → ℝ) (hK : ∀ x y, 0 ≤ K x y) {R : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ x, ∑ y, K x y ≤ R) (hcol : ∀ y, ∑ x, K x y ≤ R) (g h : B → ℝ) :
    ∑ x, ∑ y, |g x| * K x y * |h y| ≤
      R * Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (∑ x, h x ^ 2) := by
  have hB : 0 ≤ ∑ x, ∑ y, |g x| * K x y * |h y| :=
    sum_nonneg fun x _ => sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (hK x y)) (abs_nonneg _)
  rw [← abs_of_nonneg hB]
  refine abs_le_of_scaled (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hR fun t ht => ?_
  rw [abs_of_nonneg hB, Real.sq_sqrt (sum_nonneg fun x _ => sq_nonneg _),
    Real.sq_sqrt (sum_nonneg fun x _ => sq_nonneg _)]
  have hpt : ∀ x y, |g x| * K x y * |h y| ≤ K x y * (t * g x ^ 2 + h y ^ 2 / t) / 2 := by
    intro x y
    have hK' := hK x y
    have key : 2 * (|g x| * |h y|) ≤ t * g x ^ 2 + h y ^ 2 / t := by
      rw [← sq_abs (g x), ← sq_abs (h y)]
      have h1 : 0 ≤ (t * |g x| - |h y|) ^ 2 := sq_nonneg _
      have h2 : t * |g x| ^ 2 + |h y| ^ 2 / t - 2 * (|g x| * |h y|) =
          (t * |g x| - |h y|) ^ 2 / t := by
        field_simp
        ring
      have h3 : 0 ≤ (t * |g x| - |h y|) ^ 2 / t := div_nonneg h1 ht.le
      linarith
    nlinarith
  have hA : ∑ x, ∑ y, K x y * g x ^ 2 ≤ R * ∑ x, g x ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun x _ => ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _)
  have hB2 : ∑ x, ∑ y, K x y * h y ^ 2 ≤ R * ∑ y, h y ^ 2 := by
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun y _ => ?_
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)
  have hsplit : ∑ x, ∑ y, K x y * (t * g x ^ 2 + h y ^ 2 / t) / 2 =
      t / 2 * ∑ x, ∑ y, K x y * g x ^ 2 + 1 / (2 * t) * ∑ x, ∑ y, K x y * h y ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    field_simp
  calc ∑ x, ∑ y, |g x| * K x y * |h y|
      ≤ ∑ x, ∑ y, K x y * (t * g x ^ 2 + h y ^ 2 / t) / 2 :=
        sum_le_sum fun x _ => sum_le_sum fun y _ => hpt x y
    _ = t / 2 * ∑ x, ∑ y, K x y * g x ^ 2 + 1 / (2 * t) * ∑ x, ∑ y, K x y * h y ^ 2 := hsplit
    _ ≤ t / 2 * (R * ∑ x, g x ^ 2) + 1 / (2 * t) * (R * ∑ y, h y ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hA (by positivity))
          (mul_le_mul_of_nonneg_left hB2 (by positivity))
    _ = R / 2 * (t * ∑ x, g x ^ 2 + (∑ x, h x ^ 2) / t) := by
        field_simp

/-- The collision kernel `[x₀ ≠ x₁][y₀ ≠ y₁] − ind4 x y`: the two pairs share a label. -/
noncomputable def coll (x y : ZMod p × ZMod p) : ℝ := off x * off y - ind4 x y

omit [Fact p.Prime] in
theorem coll_nonneg (x y : ZMod p × ZMod p) : 0 ≤ coll x y := by
  unfold coll
  rw [ind4_eq]
  unfold off
  split_ifs <;> simp_all

omit [Fact p.Prime] in
theorem ind4_symm (x y : ZMod p × ZMod p) : ind4 x y = ind4 y x := by
  rw [ind4_eq, ind4_eq]
  congr 1
  apply propext
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;>
    exact ⟨h2, h1, Ne.symm h3, Ne.symm h5, Ne.symm h4, Ne.symm h6⟩

omit [Fact p.Prime] in
theorem coll_symm (x y : ZMod p × ZMod p) : coll x y = coll y x := by
  unfold coll
  rw [ind4_symm, mul_comm (off x)]

omit [Fact p.Prime] in
theorem coll_le_one (x y : ZMod p × ZMod p) : coll x y ≤ 1 := by
  unfold coll
  rw [ind4_eq]
  unfold off
  split_ifs <;> simp_all

theorem sum_off : ∑ x : ZMod p × ZMod p, off x = (p : ℝ) * ((p : ℝ) - 1) := by
  rw [Fintype.sum_prod_type]
  have h : ∀ a : ZMod p, ∑ b : ZMod p, off (a, b) = (p : ℝ) - 1 := by
    intro a
    have e : ∀ b : ZMod p, off (a, b) = 1 - (if b = a then 1 else 0) := by
      intro b
      unfold off
      by_cases hb : b = a
      · subst hb; simp
      · simp [hb, Ne.symm hb]
    simp only [e, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  rw [sum_congr rfl fun a _ => h a, sum_const, card_univ, ZMod.card, nsmul_eq_mul]

/-- **The row mass of the collision kernel**: `4p − 6` (`τ p(p − 1)`). -/
theorem sum_coll_row (hp : 5 ≤ p) (x : ZMod p × ZMod p) :
    ∑ y, coll x y ≤ 4 * (p : ℝ) - 6 := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  unfold coll
  rw [sum_sub_distrib, ← mul_sum, sum_off]
  obtain ⟨a, b⟩ := x
  by_cases hab : a = b
  · have h0 : off (a, b) = 0 := by simp [off, hab]
    have h1 : ∀ y, ind4 (a, b) y = 0 := fun y => by simp [ind4, h0]
    simp only [h0, h1, zero_mul, sum_const_zero, sub_zero]
    linarith
  · have h1 : off (a, b) = 1 := by simp [off, hab]
    rw [h1, sum_ind4_row hab, ZMod.card]
    nlinarith

theorem sum_coll_col (hp : 5 ≤ p) (y : ZMod p × ZMod p) :
    ∑ x, coll x y ≤ 4 * (p : ℝ) - 6 := by
  simp only [coll_symm _ y]
  exact sum_coll_row hp y

/-- **A collision form**: `|∑ g(x) coll(x, y) c(x, y) h(y)| ≤ M (4p − 6) ‖g‖ ‖h‖` for
`|c| ≤ M`. -/
theorem coll_form_le (hp : 5 ≤ p) (c : ZMod p × ZMod p → ZMod p × ZMod p → ℝ) {M : ℝ}
    (hM : ∀ x y, |c x y| ≤ M) (g h : ZMod p × ZMod p → ℝ) :
    |∑ x, ∑ y, g x * coll x y * c x y * h y| ≤
      M * (4 * (p : ℝ) - 6) * Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (∑ x, h x ^ 2) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have hS := schur_le (fun x y => M * coll x y) (fun x y => mul_nonneg hM0 (coll_nonneg x y))
    (mul_nonneg hM0 (by linarith : (0 : ℝ) ≤ 4 * (p : ℝ) - 6))
    (fun x => by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_coll_row hp x) hM0)
    (fun y => by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_coll_col hp y) hM0) g h
  refine ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => abs_sum_le_sum_abs _ _)).trans ?_
  refine le_trans (sum_le_sum fun x _ => sum_le_sum fun y _ => ?_) hS
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (coll_nonneg x y)]
  have := hM x y
  have hc := coll_nonneg x y
  calc |g x| * coll x y * |c x y| * |h y| = (|g x| * coll x y * |h y|) * |c x y| := by ring
    _ ≤ (|g x| * coll x y * |h y|) * M :=
        mul_le_mul_of_nonneg_left this (mul_nonneg (mul_nonneg (abs_nonneg _) hc) (abs_nonneg _))
    _ = |g x| * (M * coll x y) * |h y| := by ring

/-! ## Row and column sums -/

/-- `G₀(a) = ∑_b g(a, b)`. -/
noncomputable def rowS (g : ZMod p × ZMod p → ℝ) (a : ZMod p) : ℝ := ∑ b, g (a, b)

/-- `G₁(b) = ∑_a g(a, b)`. -/
noncomputable def colS (g : ZMod p × ZMod p → ℝ) (b : ZMod p) : ℝ := ∑ a, g (a, b)

/-- **`‖V₀^* u‖² + ‖V₁^* u‖² ≤ (1 + η^G_p) ‖u‖²`** in unnormalized form. -/
theorem rows_cols_le {g : ZMod p × ZMod p → ℝ} (hg : OffDiag g) (h0 : ∑ x, g x = 0) :
    ∑ a, rowS g a ^ 2 + ∑ b, colS g b ^ 2 ≤ p * ∑ x, g x ^ 2 := by
  have hp0 : (0 : ℝ) < p := by have := p_gt_one (p := p); linarith
  set S := ∑ a, rowS g a ^ 2 + ∑ b, colS g b ^ 2
  have hS0 : 0 ≤ S := add_nonneg (sum_nonneg fun a _ => sq_nonneg _)
    (sum_nonneg fun b _ => sq_nonneg _)
  set Fv : ZMod p × ZMod p → ℝ := fun x => off x * (rowS g x.1 + colS g x.2)
  have hgo := mul_off hg
  have hSeq : S = ∑ x, g x * Fv x := by
    have e1 : ∑ a, rowS g a ^ 2 = ∑ x : ZMod p × ZMod p, g x * rowS g x.1 := by
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => ?_
      rw [sq, rowS, sum_mul]
      rfl
    have e2 : ∑ b, colS g b ^ 2 = ∑ x : ZMod p × ZMod p, g x * colS g x.2 := by
      rw [Fintype.sum_prod_type, sum_comm]
      refine sum_congr rfl fun b _ => ?_
      rw [sq, colS, sum_mul]
      rfl
    rw [show S = ∑ a, rowS g a ^ 2 + ∑ b, colS g b ^ 2 from rfl, e1, e2, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    simp only [Fv]
    rw [← mul_assoc, hgo x]
    ring
  have hr0 : ∑ a, rowS g a = 0 := by
    simp only [rowS]; rw [← Fintype.sum_prod_type (f := fun x => g x)]; exact h0
  have hc0 : ∑ b, colS g b = 0 := by
    simp only [colS]; rw [sum_comm, ← Fintype.sum_prod_type (f := fun x => g x)]; exact h0
  have hF : ∑ x, Fv x ^ 2 ≤ p * S := by
    have e : ∀ x : ZMod p × ZMod p, Fv x ^ 2 = (rowS g x.1 + colS g x.2) ^ 2 -
        (if x.1 = x.2 then (rowS g x.1 + colS g x.2) ^ 2 else 0) := by
      intro x
      simp only [Fv, off]
      split_ifs <;> ring
    simp only [e, sum_sub_distrib, Fintype.sum_prod_type, sum_ite_eq, mem_univ, ↓reduceIte]
    have e2 : ∑ a, ∑ b, (rowS g a + colS g b) ^ 2 =
        p * ∑ a, rowS g a ^ 2 + p * ∑ b, colS g b ^ 2 + 2 * (∑ a, rowS g a) * ∑ b, colS g b := by
      have : ∀ a b, (rowS g a + colS g b) ^ 2 =
          rowS g a ^ 2 + colS g b ^ 2 + 2 * (rowS g a * colS g b) := fun a b => by ring
      have t1 : ∑ a : ZMod p, ∑ _b : ZMod p, rowS g a ^ 2 = (p : ℝ) * ∑ a, rowS g a ^ 2 := by
        simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_sum]
      have t2 : ∑ _a : ZMod p, ∑ b : ZMod p, colS g b ^ 2 = (p : ℝ) * ∑ b, colS g b ^ 2 := by
        simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      have t3 : ∑ a, ∑ b, 2 * (rowS g a * colS g b) = 2 * (∑ a, rowS g a) * ∑ b, colS g b := by
        rw [mul_assoc, Finset.sum_mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
      simp only [this, sum_add_distrib]
      rw [t1, t2, t3]
    rw [e2, hr0, hc0]
    have : 0 ≤ ∑ a, (rowS g a + colS g a) ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    simp only [S]
    nlinarith
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ g Fv
  rw [← hSeq] at hcs
  have h2 : S ≤ Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (p * S) :=
    hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hF) (Real.sqrt_nonneg _))
  have hsq : S ^ 2 ≤ (∑ x, g x ^ 2) * (p * S) := by
    have h3 := mul_self_le_mul_self hS0 h2
    rw [show Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (p * S) *
      (Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (p * S)) =
      (Real.sqrt (∑ x, g x ^ 2) * Real.sqrt (∑ x, g x ^ 2)) *
        (Real.sqrt (p * S) * Real.sqrt (p * S)) by ring,
      Real.mul_self_sqrt (sum_nonneg fun x _ => sq_nonneg _),
      Real.mul_self_sqrt (mul_nonneg hp0.le hS0)] at h3
    nlinarith
  rcases hS0.lt_or_eq with hpos | hz
  · have : S * S ≤ (p * ∑ x, g x ^ 2) * S := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hz]
    exact mul_nonneg hp0.le (sum_nonneg fun x _ => sq_nonneg _)

end Sarkozy.NormBoundsPaper2
