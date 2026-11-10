module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The source operator `D_p` on ordered pairs: the algebra (NB2)

`paper/sections/21_middle_records.tex`, proof of `lem:merge-repair`, paragraph "The source and the
first-coordinate law": "The source operator averages over ordered pairs disjoint from its input
pair. Its eigenvalues are `1` on constants, zero on antisymmetric pair functions, `−2/(p − 2)` on
`u(x₀) + u(x₁)` with `E u = 0`, and `2/((p − 2)(p − 3))` on symmetric functions with zero row sums.
… summing a function over all pairs and subtracting the pairs meeting the input gives the displayed
values. In particular `‖D_p − J‖ = d_p`."

On a finite set `X` with `n = |X| ≥ 4` (later `X = 𝔽_p`), for functions `g, h` on `X × X` that
vanish on the diagonal:

* `ind4 x y = [x₀ ≠ x₁][y₀ ≠ y₁](1 − δ_{y₀x₀} − δ_{y₀x₁})(1 − δ_{y₁x₀} − δ_{y₁x₁})`, the indicator
  of four distinct labels (`ind4_eq`), and the form `T(g, h) = ∑_{x,y} g(x) ind4(x, y) h(y)`;
* **`T_eq`** ("summing over all pairs and subtracting the pairs meeting the input"):
  `T(g, h) = (∑g)(∑h) − ∑_a u_g(a) u_h(a) + ∑ g h + ∑ g h̃`, `u_g(a) = ∑_b (g(a,b) + g(b,a))`,
  `h̃(a, b) = h(b, a)`;
* **`sos_rows`**: for a symmetric `h` vanishing on the diagonal with row sums `u` of total zero,
  `2 ∑_a u(a)² ≤ (n − 2) ∑_{a,c} h(a,c)²` (the eigenvalue `n − 2` of the incidence operator);
* **`T_upper`**, **`T_lower`**: for `∑ g = 0`, `−2(n − 3) ∑ g² ≤ T(g, g) ≤ 2 ∑ g²`;
* **`T_bilin`** (polarization): `|T(g, h)| ≤ 2(n − 3) ‖g‖₂ ‖h‖₂` for `∑ g = ∑ h = 0`.

With the normalization `1/(n(n−1)(n−2)(n−3))` of the source law and `‖·‖² = (n(n − 1))⁻¹ ∑ ·²`,
this is `|⟨g, (D_p − J) h⟩| ≤ (2/(n − 2)) ‖g‖ ‖h‖`, i.e. `‖D_p − J‖ ≤ d_p`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

section Algebra

variable {X : Type} [Fintype X] [DecidableEq X]

/-- `δ_{ab}`. -/
def dl (a b : X) : ℝ := if a = b then 1 else 0

/-- The off-diagonal indicator `[x₀ ≠ x₁]`. -/
def off (x : X × X) : ℝ := if x.1 = x.2 then 0 else 1

/-- The indicator of four distinct labels `x₀, x₁, y₀, y₁`, in product form. -/
def ind4 (x y : X × X) : ℝ :=
  off x * off y * ((1 - dl y.1 x.1 - dl y.1 x.2) * (1 - dl y.2 x.1 - dl y.2 x.2))

omit [Fintype X] in
/-- `ind4` is the indicator of four distinct labels. -/
theorem ind4_eq (x y : X × X) :
    ind4 x y = if x.1 ≠ x.2 ∧ y.1 ≠ y.2 ∧ y.1 ≠ x.1 ∧ y.1 ≠ x.2 ∧ y.2 ≠ x.1 ∧ y.2 ≠ x.2
      then 1 else 0 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [ind4, off, dl]
  by_cases hab : a = b
  · simp [hab]
  by_cases hcd : c = d
  · simp [hcd]
  by_cases h1 : c = a <;> by_cases h2 : c = b <;> by_cases h3 : d = a <;> by_cases h4 : d = b <;>
    simp_all

/-- The row count of the source: `(n − 2)(n − 3)` disjoint ordered pairs. -/
theorem sum_ind4_row {a b : X} (hab : a ≠ b) :
    ∑ y, ind4 (a, b) y = ((Fintype.card X : ℝ) - 2) * ((Fintype.card X : ℝ) - 3) := by
  set A : X → ℝ := fun c => 1 - dl c a - dl c b
  have hA : ∑ c, A c = (Fintype.card X : ℝ) - 2 := by
    simp only [A, dl, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ,
      nsmul_eq_mul, mul_one]
    ring
  have hA2 : ∀ c, A c * A c = A c := by
    intro c
    simp only [A, dl]
    by_cases h1 : c = a <;> by_cases h2 : c = b <;> simp_all
  have e : ∀ c d, ind4 (a, b) (c, d) = A c * A d - (if c = d then A c * A d else 0) := by
    intro c d
    simp only [ind4, off, A, hab, ↓reduceIte]
    by_cases h : c = d <;> simp [h]
  rw [Fintype.sum_prod_type]
  simp only [e, sum_sub_distrib, sum_ite_eq, mem_univ, ↓reduceIte, hA2]
  rw [← sum_mul_sum, hA]
  ring

/-- The form `T(g, h) = ∑_{x,y} g(x) ind4(x, y) h(y)`. -/
noncomputable def T (g h : X × X → ℝ) : ℝ := ∑ x, ∑ y, g x * ind4 x y * h y

/-- The symmetrized row sums `u_g(a) = ∑_b (g(a, b) + g(b, a))`. -/
noncomputable def us (g : X × X → ℝ) (a : X) : ℝ := ∑ b, (g (a, b) + g (b, a))

/-- Vanishing on the diagonal. -/
def OffDiag (g : X × X → ℝ) : Prop := ∀ a, g (a, a) = 0

omit [Fintype X] in
theorem mul_off {g : X × X → ℝ} (hg : OffDiag g) (x : X × X) : g x * off x = g x := by
  obtain ⟨a, b⟩ := x
  unfold off
  by_cases h : a = b
  · subst h
    simp [hg a]
  · simp [h]

/-- **The source form, by inclusion–exclusion over the pairs meeting the input.** -/
theorem T_eq {g h : X × X → ℝ} (hg : OffDiag g) (hh : OffDiag h) :
    T g h = (∑ x, g x) * (∑ y, h y) - ∑ a, us g a * us h a + ∑ x, g x * h x +
      ∑ x, g x * h (x.2, x.1) := by
  have e1 : T g h = ∑ x, ∑ y, g x * h y *
      ((1 - dl y.1 x.1 - dl y.1 x.2) * (1 - dl y.2 x.1 - dl y.2 x.2)) := by
    unfold T ind4
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    have h1 := mul_off hg x
    have h2 := mul_off hh y
    calc g x * (off x * off y * ((1 - dl y.1 x.1 - dl y.1 x.2) *
          (1 - dl y.2 x.1 - dl y.2 x.2))) * h y
        = (g x * off x) * (h y * off y) * ((1 - dl y.1 x.1 - dl y.1 x.2) *
          (1 - dl y.2 x.1 - dl y.2 x.2)) := by ring
      _ = _ := by rw [h1, h2]
  rw [e1]
  simp only [Fintype.sum_prod_type, us]
  have expand : ∀ a b c d : X, g (a, b) * h (c, d) *
      ((1 - dl c a - dl c b) * (1 - dl d a - dl d b)) =
      g (a, b) * h (c, d) - g (a, b) * h (c, d) * dl c a - g (a, b) * h (c, d) * dl c b -
        g (a, b) * h (c, d) * dl d a - g (a, b) * h (c, d) * dl d b +
        g (a, b) * h (c, d) * (dl c a * dl d a) + g (a, b) * h (c, d) * (dl c a * dl d b) +
        g (a, b) * h (c, d) * (dl c b * dl d a) + g (a, b) * h (c, d) * (dl c b * dl d b) := by
    intro a b c d
    ring
  simp only [expand, sum_add_distrib, sum_sub_distrib]
  simp only [dl, mul_ite, mul_one, mul_zero, sum_ite_eq',
    mem_univ, ↓reduceIte, sum_const_zero, Finset.sum_ite_irrel]
  simp only [mul_add, add_mul, sum_add_distrib, sum_mul, mul_sum]
  have s1 : ∑ a, ∑ b, ∑ c, ∑ d, g (a, b) * h (c, d) =
      ∑ a, ∑ b, ∑ c, ∑ d, g (a, b) * h (c, d) := rfl
  have c1 : ∑ a, ∑ b, ∑ d, g (a, b) * h (b, d) = ∑ a, ∑ b, ∑ d, g (b, a) * h (a, d) := sum_comm
  have c2 : ∑ a, ∑ b, ∑ c, g (a, b) * h (c, b) = ∑ a, ∑ b, ∑ c, g (b, a) * h (c, a) := sum_comm
  have c3 : ∑ a, ∑ b, ∑ c, g (a, b) * h (c, a) = ∑ a, ∑ b, ∑ c, g (a, b) * h (c, a) := rfl
  clear s1 c3
  rw [c1, c2]
  have r1 : ∀ a, ∑ b, ∑ d, g (b, a) * h (a, d) = ∑ d, ∑ b, g (b, a) * h (a, d) :=
    fun a => sum_comm
  have r2 : ∀ a, ∑ b, ∑ c, g (b, a) * h (c, a) = ∑ c, ∑ b, g (b, a) * h (c, a) :=
    fun a => sum_comm
  have r3 : ∀ a, ∑ b, ∑ c, g (a, b) * h (c, a) = ∑ c, ∑ b, g (a, b) * h (c, a) :=
    fun a => sum_comm
  have r4 : ∀ a, ∑ b, ∑ d, g (a, b) * h (a, d) = ∑ d, ∑ b, g (a, b) * h (a, d) :=
    fun a => sum_comm
  have hh' : ∀ a, h (a, a) = 0 := hh
  simp only [r1, r2, r3, r4]
  simp only [← mul_sum, ← sum_mul, hh', mul_zero, sum_const_zero, add_zero]
  ring

omit [DecidableEq X] in
/-- `∑ g h̃ ≤ ∑ g²`. -/
theorem sum_swap_le (g : X × X → ℝ) : ∑ x, g x * g (x.2, x.1) ≤ ∑ x, g x ^ 2 := by
  have hs : ∑ x : X × X, g (x.2, x.1) ^ 2 = ∑ x, g x ^ 2 :=
    Fintype.sum_equiv (Equiv.prodComm X X) _ _ (fun x => rfl)
  have h : ∀ x : X × X, g x * g (x.2, x.1) ≤ (g x ^ 2 + g (x.2, x.1) ^ 2) / 2 := fun x => by
    nlinarith [sq_nonneg (g x - g (x.2, x.1))]
  calc ∑ x, g x * g (x.2, x.1) ≤ ∑ x, (g x ^ 2 + g (x.2, x.1) ^ 2) / 2 :=
        sum_le_sum fun x _ => h x
    _ = _ := by simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib, hs]; ring

omit [DecidableEq X] in
/-- **The incidence bound**: for symmetric `h` vanishing on the diagonal, with row sums `u` of
total zero, `2 ∑ u² ≤ (n − 2) ∑ h²`. -/
theorem sos_rows (hn : 3 ≤ Fintype.card X) (h : X → X → ℝ) (hsym : ∀ a c, h a c = h c a)
    (hd : ∀ a, h a a = 0) (hu : ∑ a, ∑ c, h a c = 0) :
    2 * ∑ a, (∑ c, h a c) ^ 2 ≤ ((Fintype.card X : ℝ) - 2) * ∑ a, ∑ c, h a c ^ 2 := by
  set n : ℝ := (Fintype.card X : ℝ)
  set k : ℝ := n - 2
  set u : X → ℝ := fun a => ∑ c, h a c
  have hk : 0 < k := by
    have : (3 : ℝ) ≤ n := by simp only [n]; exact_mod_cast hn
    simp only [k]; linarith
  have hu0 : ∑ a, u a = 0 := hu
  have hcol : ∀ c, ∑ a, h a c = u c := fun c => sum_congr rfl fun a _ => hsym a c
  -- the full sum of squares
  have hfull : 0 ≤ ∑ a, ∑ c, (k * h a c - (u a + u c)) ^ 2 - ∑ a, (k * h a a - 2 * u a) ^ 2 := by
    rw [← sum_sub_distrib]
    refine sum_nonneg fun a _ => ?_
    have := single_le_sum (f := fun c => (k * h a c - (u a + u c)) ^ 2)
      (fun c _ => sq_nonneg _) (mem_univ a)
    rw [show k * h a a - 2 * u a = k * h a a - (u a + u a) by ring]
    linarith
  have t1 : ∑ a, ∑ c, h a c * u a = ∑ a, u a ^ 2 := by
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_mul, sq]
  have t2 : ∑ a, ∑ c, h a c * u c = ∑ a, u a ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [← sum_mul, hcol, sq]
  have t3 : ∑ a : X, ∑ c : X, u a ^ 2 = n * ∑ a, u a ^ 2 := by
    simp only [sum_const, card_univ, nsmul_eq_mul, n]
    rw [mul_sum]
  have t4 : ∑ a : X, ∑ c : X, u c ^ 2 = n * ∑ a, u a ^ 2 := by
    simp only [sum_const, card_univ, nsmul_eq_mul, n]
  have t5 : ∑ a, ∑ c, u a * u c = 0 := by
    simp only [← mul_sum, hu0, mul_zero, sum_const_zero]
  have e : ∑ a, ∑ c, (k * h a c - (u a + u c)) ^ 2 =
      k ^ 2 * ∑ a, ∑ c, h a c ^ 2 - 2 * k * ∑ a, ∑ c, h a c * u a -
        2 * k * ∑ a, ∑ c, h a c * u c + ∑ a, ∑ c : X, u a ^ 2 + 2 * ∑ a, ∑ c, u a * u c +
          ∑ a : X, ∑ c, u c ^ 2 := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
    ring
  have e2 : ∑ a, (k * h a a - 2 * u a) ^ 2 = 4 * ∑ a, u a ^ 2 := by
    simp only [hd, mul_zero, zero_sub, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    ring
  rw [e, e2, t1, t2, t3, t4, t5] at hfull
  have hsum : 0 ≤ ∑ a, u a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
  have : 2 * k * ∑ a, u a ^ 2 ≤ k ^ 2 * ∑ a, ∑ c, h a c ^ 2 := by
    have hn' : n = k + 2 := by simp only [k]; ring
    rw [hn'] at hfull
    nlinarith
  have h2 : k * (2 * ∑ a, u a ^ 2) ≤ k * (k * ∑ a, ∑ c, h a c ^ 2) := by nlinarith
  exact le_of_mul_le_mul_left h2 hk

theorem T_upper {g : X × X → ℝ} (hg : OffDiag g) (h0 : ∑ x, g x = 0) :
    T g g ≤ 2 * ∑ x, g x ^ 2 := by
  rw [T_eq hg hg, h0, zero_mul]
  have h1 : 0 ≤ ∑ a, us g a * us g a := sum_nonneg fun a _ => mul_self_nonneg _
  have h2 := sum_swap_le g
  have h3 : ∑ x, g x * g x = ∑ x, g x ^ 2 := sum_congr rfl fun x _ => (sq (g x)).symm
  linarith

theorem T_lower (hn : 4 ≤ Fintype.card X) {g : X × X → ℝ} (hg : OffDiag g)
    (h0 : ∑ x, g x = 0) :
    -(2 * ((Fintype.card X : ℝ) - 3) * ∑ x, g x ^ 2) ≤ T g g := by
  rw [T_eq hg hg, h0, zero_mul]
  set hh : X → X → ℝ := fun a c => g (a, c) + g (c, a)
  have hsym : ∀ a c, hh a c = hh c a := fun a c => by simp only [hh]; ring
  have hd : ∀ a, hh a a = 0 := fun a => by simp only [hh, hg a, add_zero]
  have hu : ∑ a, ∑ c, hh a c = 0 := by
    simp only [hh, sum_add_distrib]
    rw [sum_comm (f := fun a c => g (c, a))]
    rw [← Fintype.sum_prod_type (f := fun x => g x)] at *
    rw [h0, add_zero]
  have hsos := sos_rows (by omega) hh hsym hd hu
  have hus : ∀ a, us g a = ∑ c, hh a c := fun a => rfl
  have hsq : ∑ a, ∑ c, hh a c ^ 2 = 2 * ∑ x, g x ^ 2 + 2 * ∑ x, g x * g (x.2, x.1) := by
    have e : ∀ a c, hh a c ^ 2 = g (a, c) ^ 2 + g (c, a) ^ 2 + 2 * (g (a, c) * g (c, a)) :=
      fun a c => by simp only [hh]; ring
    simp only [e, sum_add_distrib, ← mul_sum]
    rw [sum_comm (f := fun a c => g (c, a) ^ 2)]
    simp only [Fintype.sum_prod_type]
    ring
  have h2 := sum_swap_le g
  have h3 : ∑ x, g x * g x = ∑ x, g x ^ 2 := sum_congr rfl fun x _ => (sq (g x)).symm
  have hU : ∑ a, us g a * us g a = ∑ a, (∑ c, hh a c) ^ 2 :=
    sum_congr rfl fun a _ => by rw [hus, sq]
  have hn' : (4 : ℝ) ≤ Fintype.card X := by exact_mod_cast hn
  have hS : 0 ≤ ∑ x, g x ^ 2 := sum_nonneg fun x _ => sq_nonneg _
  rw [hU, h3]
  rw [hsq] at hsos
  -- `2 ∑ u² ≤ (n − 2)(2∑g² + 2∑gg̃)` and `∑ gg̃ ≤ ∑ g²`
  have hk : 0 ≤ (Fintype.card X : ℝ) - 3 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hk]

/-- **Polarization** with an optimized scale: if `|B| ≤ (c/2)(t a² + b²/t)` for every `t > 0`,
then `|B| ≤ c a b`. -/
theorem abs_le_of_scaled {B a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 < t → |B| ≤ c / 2 * (t * a ^ 2 + b ^ 2 / t)) : |B| ≤ c * a * b := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have := h (b / a) (div_pos hb' ha')
      have e : b / a * a ^ 2 + b ^ 2 / (b / a) = 2 * (a * b) := by
        field_simp
        ring
      rw [e] at this
      linarith
    · -- `b = 0`
      subst hb'
      by_contra hlt
      push Not at hlt
      have hB : 0 < |B| := lt_of_le_of_lt (by positivity) hlt
      have ht : 0 < |B| / (c * a ^ 2 + 1) := div_pos hB (by positivity)
      have := h _ ht
      have e : c / 2 * (|B| / (c * a ^ 2 + 1) * a ^ 2 + 0 ^ 2 / (|B| / (c * a ^ 2 + 1))) =
          |B| * (c * a ^ 2) / (2 * (c * a ^ 2 + 1)) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity)] at this
      nlinarith [mul_nonneg hc (sq_nonneg a)]
  · -- `a = 0`
    subst ha'
    by_contra hlt
    push Not at hlt
    have hB : 0 < |B| := lt_of_le_of_lt (by positivity) hlt
    have ht : 0 < (c * b ^ 2 + 1) / |B| := div_pos (by positivity) hB
    have := h _ ht
    have e : c / 2 * ((c * b ^ 2 + 1) / |B| * 0 ^ 2 + b ^ 2 / ((c * b ^ 2 + 1) / |B|)) =
        |B| * (c * b ^ 2) / (2 * (c * b ^ 2 + 1)) := by
      field_simp
      ring
    rw [e, le_div_iff₀ (by positivity)] at this
    nlinarith [mul_nonneg hc (sq_nonneg b)]

theorem T_symm (g h : X × X → ℝ) : T g h = T h g := by
  unfold T
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
  have : ind4 x y = ind4 y x := by
    rw [ind4_eq, ind4_eq]
    congr 1
    apply propext
    constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;>
      exact ⟨h2, h1, Ne.symm h3, Ne.symm h5, Ne.symm h4, Ne.symm h6⟩
  rw [this]
  ring

theorem T_add_left (g₁ g₂ h : X × X → ℝ) : T (g₁ + g₂) h = T g₁ h + T g₂ h := by
  unfold T
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  simp only [Pi.add_apply]
  ring

theorem T_smul_left (t : ℝ) (g h : X × X → ℝ) : T (t • g) h = t * T g h := by
  unfold T
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem T_add_right (g h₁ h₂ : X × X → ℝ) : T g (h₁ + h₂) = T g h₁ + T g h₂ := by
  rw [T_symm, T_add_left, T_symm h₁, T_symm h₂]

theorem T_smul_right (t : ℝ) (g h : X × X → ℝ) : T g (t • h) = t * T g h := by
  rw [T_symm, T_smul_left, T_symm h]

/-- **`‖D_p − J‖ ≤ d_p` in unnormalized form**: `|T(g, h)| ≤ 2(n − 3) ‖g‖₂ ‖h‖₂` for `g`, `h`
vanishing on the diagonal with `∑ g = ∑ h = 0`. -/
theorem T_bilin (hn : 4 ≤ Fintype.card X) {g h : X × X → ℝ} (hg : OffDiag g) (hh : OffDiag h)
    (hg0 : ∑ x, g x = 0) (hh0 : ∑ x, h x = 0) :
    |T g h| ≤ 2 * ((Fintype.card X : ℝ) - 3) * Real.sqrt (∑ x, g x ^ 2) *
      Real.sqrt (∑ x, h x ^ 2) := by
  set c := 2 * ((Fintype.card X : ℝ) - 3)
  have hn' : (4 : ℝ) ≤ Fintype.card X := by exact_mod_cast hn
  have hc : 0 ≤ c := by simp only [c]; linarith
  have hQ : ∀ w : X × X → ℝ, OffDiag w → ∑ x, w x = 0 → |T w w| ≤ c * ∑ x, w x ^ 2 := by
    intro w hw hw0
    have hS : 0 ≤ ∑ x, w x ^ 2 := sum_nonneg fun x _ => sq_nonneg _
    rw [abs_le]
    refine ⟨T_lower hn hw hw0, (T_upper hw hw0).trans ?_⟩
    nlinarith
  refine abs_le_of_scaled (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hc fun t ht => ?_
  set s := Real.sqrt t
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hss : s * s = t := Real.mul_self_sqrt ht.le
  set w₁ : X × X → ℝ := s • g + s⁻¹ • h
  set w₂ : X × X → ℝ := s • g - s⁻¹ • h
  have hw₁ : OffDiag w₁ := fun a => by simp [w₁, hg a, hh a]
  have hw₂ : OffDiag w₂ := fun a => by simp [w₂, hg a, hh a]
  have hw₁0 : ∑ x, w₁ x = 0 := by
    simp only [w₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hg0,
      hh0, mul_zero, add_zero]
  have hw₂0 : ∑ x, w₂ x = 0 := by
    simp only [w₂, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sum_sub_distrib, ← mul_sum, hg0,
      hh0, mul_zero, sub_zero]
  have hpol : T w₁ w₁ - T w₂ w₂ = 4 * T g h := by
    have e₂ : w₂ = s • g + (-s⁻¹) • h := by
      simp only [w₂, neg_smul, sub_eq_add_neg]
    rw [e₂]
    simp only [w₁, T_add_left, T_add_right, T_smul_left, T_smul_right]
    rw [T_symm h g]
    have : s * s⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
    linear_combination (4 * T g h) * this
  have hn₁ : ∑ x, w₁ x ^ 2 + ∑ x, w₂ x ^ 2 = 2 * (t * ∑ x, g x ^ 2 + (∑ x, h x ^ 2) / t) := by
    simp only [w₁, w₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sum_add_distrib]
    rw [show (∑ x, h x ^ 2) / t = ∑ x, h x ^ 2 / t by simp only [div_eq_mul_inv, sum_mul],
      mul_sum, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← hss]
    field_simp
    ring
  have h1 := hQ w₁ hw₁ hw₁0
  have h2 := hQ w₂ hw₂ hw₂0
  have hgS := Real.sq_sqrt (sum_nonneg (s := univ) fun x _ => sq_nonneg (g x))
  have hhS := Real.sq_sqrt (sum_nonneg (s := univ) fun x _ => sq_nonneg (h x))
  rw [hgS, hhS]
  have : 4 * |T g h| ≤ c * (∑ x, w₁ x ^ 2 + ∑ x, w₂ x ^ 2) := by
    rw [← abs_of_pos (by norm_num : (0 : ℝ) < 4), ← abs_mul, ← hpol]
    calc |T w₁ w₁ - T w₂ w₂| ≤ |T w₁ w₁| + |T w₂ w₂| := abs_sub _ _
      _ ≤ c * ∑ x, w₁ x ^ 2 + c * ∑ x, w₂ x ^ 2 := add_le_add h1 h2
      _ = _ := by ring
  rw [hn₁] at this
  linarith

end Algebra

end Sarkozy.NormBoundsPaper2
