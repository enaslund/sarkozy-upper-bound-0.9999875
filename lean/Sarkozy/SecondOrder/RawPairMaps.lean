module

public import Sarkozy.SecondOrder.WeightedStars

/-!
# Raw pair maps (`cor:raw-pair-maps`(a))

`paper/sections/15_second_order.tex`, `cor:raw-pair-maps`(a), with uniform probability on every
label and `q = 1/p`. For a pair `y = (y₀, y₁)`, `ψ_y(s) = χ(s - y₀) χ(s - y₁)`. All three bounds
come from `eq:two-root`, `E_a χ(s - a)χ(s' - a) = 1_{s=s'} - q`.

* `raw_pair_full`: the raw pair map `h ↦ E_s ψ_y(s) h(s)` into functions of `y ∈ 𝔽_p²` has
  `E_y(E_s ψ_y h)² ≤ q(1 - q) E h²`, i.e. norm at most `√(q(1 - q))`.
* `raw_pair_distinct`: into functions of `y` uniform on the ordered pairs of distinct labels,
  `E_y(E_s ψ_y h)² ≤ q E h²`, i.e. norm at most `r`.
* `second_map_bound`: the map `F ↦ E_{s,t} χ(s - a)χ(t - a)F(s, t)` into functions of `a` has
  norm at most `√(q(1 - q))`, by duality from its Gram kernel `(1_{a=a'} - q)²`.

These are upper bounds; the paper also states that they are attained.

Part (b): `S_diag` evaluates `S` on the diagonal functions `Df`, giving `Sd = r(1 - 2q)` and
`(RDf)(y) = -qr(f(y₀) + f(y₁))` for `E f = 0`. `RD_norm` is `‖RDf‖ ≤ √2 qr ‖f‖`, and `R_row_norm`
shows that every row of `R` has norm at most one. The bound `‖R‖ ≤ 2q/√(1 - q)` off the diagonal
needs `cor:dl:normalized`, which rests on `thm:dl:K`. Since 1 November 2026, `thm:dl:K` is the
hypothesis `Target.FourCycle`, and (b) is proved in full in `Sarkozy/DLK/`. The tensor-product
remark of (a) is not formalized.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime]

/-- `χ` as a real function. -/
noncomputable def chiRe (a : ZMod p) : ℝ := ((quadraticChar (ZMod p) a : ℤ) : ℝ)

theorem chiRe_sq_le (a : ZMod p) : chiRe a ^ 2 ≤ 1 := by
  unfold chiRe
  rcases quadraticChar_isQuadratic (ZMod p) a with h | h | h <;> rw [h] <;> norm_num

/-- `∑_y χ(s - y) χ(s' - y) = p[s = s'] - 1` (`eq:two-root`). -/
theorem sum_chiRe_mul (hp2 : p ≠ 2) (s s' : ZMod p) :
    ∑ y, chiRe (s - y) * chiRe (s' - y) = (p : ℝ) * (if s = s' then 1 else 0) - 1 :=
  sum_chi_mul_chi hp2 s s'

/-- `(∑ h)² ≤ p ∑ h²` on `𝔽_p`. -/
theorem sq_sum_le (h : ZMod p → ℝ) : (∑ s, h s) ^ 2 ≤ (p : ℝ) * ∑ s, h s ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (ZMod p))) (f := h)
  simpa [ZMod.card] using this

/-- The quadratic form of the kernel `(p[s = s'] - 1)²`: `∑_{s,s'} h h' (p[s=s'] - 1)²
= (p² - 2p) ∑ h² + (∑ h)²`. -/
theorem quad_two_root_sq (h : ZMod p → ℝ) :
    ∑ s, ∑ s', h s * h s' * ((p : ℝ) * (if s = s' then 1 else 0) - 1) ^ 2 =
      ((p : ℝ) ^ 2 - 2 * p) * ∑ s, h s ^ 2 + (∑ s, h s) ^ 2 := by
  have e : ∀ s s' : ZMod p, h s * h s' * ((p : ℝ) * (if s = s' then 1 else 0) - 1) ^ 2 =
      ((p : ℝ) ^ 2 - 2 * p) * (if s = s' then h s * h s' else 0) + h s * h s' := by
    intro s s'; split_ifs <;> ring
  simp_rw [e, sum_add_distrib, ← mul_sum]
  simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  rw [sq (∑ s, h s), sum_mul_sum]
  refine congrArg₂ (· + ·) ?_ (sum_congr rfl fun i _ => mul_sum _ _ _)
  congr 1
  exact sum_congr rfl fun s _ => by ring

/-- **The raw pair map into `𝔽_p²`** (`cor:raw-pair-maps`(a)):
`E_y (E_s ψ_y(s) h(s))² ≤ q(1 - q) E_s h(s)²`. -/
theorem raw_pair_full (hp2 : p ≠ 2) (h : ZMod p → ℝ) :
    (1 / (p : ℝ) ^ 2) * ∑ y : ZMod p × ZMod p,
        ((1 / (p : ℝ)) * ∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 ≤
      (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * ((1 / (p : ℝ)) * ∑ s, h s ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  -- expand the square and sum over `y` first
  have hexp : ∑ y : ZMod p × ZMod p, (∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 =
      ∑ s, ∑ s', h s * h s' * ((p : ℝ) * (if s = s' then 1 else 0) - 1) ^ 2 := by
    have e1 : ∀ y : ZMod p × ZMod p, (∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 =
        ∑ s, ∑ s', h s * h s' * ((chiRe (s - y.1) * chiRe (s' - y.1)) *
          (chiRe (s - y.2) * chiRe (s' - y.2))) := by
      intro y
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun s _ => sum_congr rfl fun s' _ => by ring
    rw [sum_congr rfl fun y _ => e1 y, sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun s' _ => ?_
    rw [← mul_sum, Fintype.sum_prod_type]
    simp_rw [← mul_sum, ← sum_mul, sum_chiRe_mul hp2]
    ring
  have hq := quad_two_root_sq h
  have hcs := sq_sum_le h
  have hS : 0 ≤ ∑ s, h s ^ 2 := sum_nonneg fun s _ => sq_nonneg _
  have hmain : ∑ y : ZMod p × ZMod p, ((1 / (p : ℝ)) * ∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 =
      (1 / (p : ℝ)) ^ 2 * (((p : ℝ) ^ 2 - 2 * p) * ∑ s, h s ^ 2 + (∑ s, h s) ^ 2) := by
    simp_rw [mul_pow]
    rw [← mul_sum, hexp, hq]
  rw [hmain]
  have hbound : ((p : ℝ) ^ 2 - 2 * p) * ∑ s, h s ^ 2 + (∑ s, h s) ^ 2 ≤
      ((p : ℝ) ^ 2 - p) * ∑ s, h s ^ 2 := by nlinarith
  calc 1 / (p : ℝ) ^ 2 * ((1 / (p : ℝ)) ^ 2 *
        (((p : ℝ) ^ 2 - 2 * p) * ∑ s, h s ^ 2 + (∑ s, h s) ^ 2))
      ≤ 1 / (p : ℝ) ^ 2 * ((1 / (p : ℝ)) ^ 2 * (((p : ℝ) ^ 2 - p) * ∑ s, h s ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * ((1 / (p : ℝ)) * ∑ s, h s ^ 2) := by
        field_simp


/-- `∑_y (∑_s ψ_y(s) h(s))² = (p² - 2p) ∑ h² + (∑ h)²` over all pairs `y ∈ 𝔽_p²`. -/
theorem sum_sq_raw_pair (hp2 : p ≠ 2) (h : ZMod p → ℝ) :
    ∑ y : ZMod p × ZMod p, (∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 =
      ((p : ℝ) ^ 2 - 2 * p) * ∑ s, h s ^ 2 + (∑ s, h s) ^ 2 := by
  have e1 : ∀ y : ZMod p × ZMod p, (∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 =
      ∑ s, ∑ s', h s * h s' * ((chiRe (s - y.1) * chiRe (s' - y.1)) *
        (chiRe (s - y.2) * chiRe (s' - y.2))) := by
    intro y
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun s _ => sum_congr rfl fun s' _ => by ring
  rw [sum_congr rfl fun y _ => e1 y, sum_comm]
  rw [← quad_two_root_sq h]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s' _ => ?_
  rw [← mul_sum, Fintype.sum_prod_type]
  simp_rw [← mul_sum, ← sum_mul, sum_chiRe_mul hp2]
  ring

theorem chiRe_sq (a : ZMod p) : chiRe a ^ 2 = if a = 0 then 0 else 1 := by
  unfold chiRe
  split_ifs with h
  · rw [h, quadraticChar_zero]; simp
  · rw [← Int.cast_pow, quadraticChar_sq_one h, Int.cast_one]

/-- `∑_t χ(s - t)² χ(s' - t)² = p - 2 + [s = s']`. -/
theorem sum_chiRe_sq_mul (s s' : ZMod p) :
    ∑ t, chiRe (s - t) ^ 2 * chiRe (s' - t) ^ 2 = (p : ℝ) - 2 + (if s = s' then 1 else 0) := by
  have e : ∀ t, chiRe (s - t) ^ 2 * chiRe (s' - t) ^ 2 =
      1 - (if s = t then 1 else 0) - (if s' = t then 1 else 0) +
        (if s = t then (if s' = s then 1 else 0) else 0) := by
    intro t
    rw [chiRe_sq, chiRe_sq]
    by_cases h1 : s = t <;> by_cases h2 : s' = t
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · have h1' : s - t ≠ 0 := sub_ne_zero.mpr h1
      have h2' : s' - t ≠ 0 := sub_ne_zero.mpr h2
      simp [h1, h2, h1', h2']
  rw [sum_congr rfl fun t _ => e t, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    sum_ite_eq, sum_ite_eq, sum_ite_eq]
  simp only [mem_univ, ↓reduceIte, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  by_cases h : s = s'
  · subst h; simp; ring
  · simp [h, Ne.symm h]; ring

/-- **The raw pair map on distinct pairs** (`cor:raw-pair-maps`(a)): for `y` uniform on the
ordered pairs of distinct labels, `E_y (E_s ψ_y(s) h(s))² ≤ q E_s h(s)²`. -/
theorem raw_pair_distinct (hp2 : p ≠ 2) (h : ZMod p → ℝ) :
    (1 / ((p : ℝ) * (p - 1))) * ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2),
        ((1 / (p : ℝ)) * ∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 ≤
      (1 / (p : ℝ)) * ((1 / (p : ℝ)) * ∑ s, h s ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := hp.out.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  set Q : ZMod p × ZMod p → ℝ := fun y => (∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2
  -- the diagonal pairs
  have hdiag : ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 = y.2), Q y =
      ((p : ℝ) - 2) * (∑ s, h s) ^ 2 + ∑ s, h s ^ 2 := by
    rw [sum_filter, Fintype.sum_prod_type]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    simp only [Q]
    have e : ∀ t : ZMod p, (∑ s, chiRe (s - t) * chiRe (s - t) * h s) ^ 2 =
        ∑ s, ∑ s', h s * h s' * (chiRe (s - t) ^ 2 * chiRe (s' - t) ^ 2) := by
      intro t
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun s _ => sum_congr rfl fun s' _ => by ring
    rw [sum_congr rfl fun t _ => e t, sum_comm]
    have e2 : ∀ s : ZMod p, ∑ t, ∑ s', h s * h s' * (chiRe (s - t) ^ 2 * chiRe (s' - t) ^ 2) =
        ∑ s', h s * h s' * ((p : ℝ) - 2 + (if s = s' then 1 else 0)) := by
      intro s
      rw [sum_comm]
      refine sum_congr rfl fun s' _ => ?_
      rw [← mul_sum, sum_chiRe_sq_mul]
    rw [sum_congr rfl fun s _ => e2 s]
    have e3 : ∀ s s' : ZMod p, h s * h s' * ((p : ℝ) - 2 + (if s = s' then 1 else 0)) =
        ((p : ℝ) - 2) * (h s * h s') + (if s = s' then h s * h s' else 0) := by
      intro s s'; split_ifs <;> ring
    simp_rw [e3, sum_add_distrib, ← mul_sum]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [sq (∑ s, h s), sum_mul_sum]
    exact congrArg₂ (· + ·) (congrArg _ (sum_congr rfl fun i _ => mul_sum _ _ _))
      (sum_congr rfl fun s _ => by ring)
  have hall := sum_sq_raw_pair hp2 h
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (ZMod p × ZMod p))
    (fun y => y.1 = y.2) Q
  have hD : ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2), Q y =
      ((p : ℝ) ^ 2 - 2 * p - 1) * ∑ s, h s ^ 2 - ((p : ℝ) - 3) * (∑ s, h s) ^ 2 := by
    have : ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => ¬ y.1 = y.2), Q y =
        ∑ y, Q y - ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 = y.2), Q y := by
      linarith
    simp only [ne_eq]
    rw [this, hdiag]
    simp only [Q]
    rw [hall]
    ring
  have hsq0 : 0 ≤ (∑ s, h s) ^ 2 := sq_nonneg _
  have hS : 0 ≤ ∑ s, h s ^ 2 := sum_nonneg fun s _ => sq_nonneg _
  have hmain : ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2),
      ((1 / (p : ℝ)) * ∑ s, chiRe (s - y.1) * chiRe (s - y.2) * h s) ^ 2 =
      (1 / (p : ℝ)) ^ 2 * (((p : ℝ) ^ 2 - 2 * p - 1) * ∑ s, h s ^ 2 -
        ((p : ℝ) - 3) * (∑ s, h s) ^ 2) := by
    simp_rw [mul_pow]
    rw [← mul_sum]
    congr 1
  rw [hmain]
  have hb : ((p : ℝ) ^ 2 - 2 * p - 1) * ∑ s, h s ^ 2 - ((p : ℝ) - 3) * (∑ s, h s) ^ 2 ≤
      ((p : ℝ) ^ 2 - p) * ∑ s, h s ^ 2 := by nlinarith
  have hp1 : (0 : ℝ) < (p : ℝ) * (p - 1) := by nlinarith
  calc 1 / ((p : ℝ) * (p - 1)) * ((1 / (p : ℝ)) ^ 2 * (((p : ℝ) ^ 2 - 2 * p - 1) *
        ∑ s, h s ^ 2 - ((p : ℝ) - 3) * (∑ s, h s) ^ 2))
      ≤ 1 / ((p : ℝ) * (p - 1)) * ((1 / (p : ℝ)) ^ 2 * (((p : ℝ) ^ 2 - p) * ∑ s, h s ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (1 / (p : ℝ)) * ((1 / (p : ℝ)) * ∑ s, h s ^ 2) := by
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp


theorem chiRe_sub_comm_mul (s a a' : ZMod p) :
    chiRe (s - a) * chiRe (s - a') = chiRe (a - s) * chiRe (a' - s) := by
  unfold chiRe
  rw [← Int.cast_mul, ← Int.cast_mul, ← map_mul, ← map_mul,
    show (s - a) * (s - a') = (a - s) * (a' - s) by ring]

/-- **The second map** (`cor:raw-pair-maps`(a)): `F ↦ E_{s,t} χ(s - a)χ(t - a)F(s, t)` has norm
at most `√(q(1 - q))`, i.e. `E_a(E_{s,t} χ(s-a)χ(t-a)F)² ≤ q(1 - q) E_{s,t} F²`. -/
theorem second_map_bound (hp2 : p ≠ 2) (F : ZMod p → ZMod p → ℝ) :
    (1 / (p : ℝ)) * ∑ a, ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ t, chiRe (s - a) * chiRe (t - a) * F s t) ^ 2 ≤
      (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ t, F s t ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  set g : ZMod p → ℝ := fun a => (1 / (p : ℝ) ^ 2) * ∑ s, ∑ t, chiRe (s - a) * chiRe (t - a) * F s t
    with hg
  set G : ZMod p → ZMod p → ℝ := fun s t => ∑ a, chiRe (s - a) * chiRe (t - a) * g a with hG
  -- `‖g‖² = p⁻² ⟨F, G⟩`
  have hid : ∑ a, g a ^ 2 = (1 / (p : ℝ) ^ 2) * ∑ s, ∑ t, F s t * G s t := by
    have e : ∀ a, g a ^ 2 = (1 / (p : ℝ) ^ 2) * ∑ s, ∑ t, F s t * (chiRe (s - a) * chiRe (t - a) * g a) := by
      intro a
      rw [sq]
      conv_lhs => rw [show g a * g a = g a * ((1 / (p : ℝ) ^ 2) *
        ∑ s, ∑ t, chiRe (s - a) * chiRe (t - a) * F s t) from rfl]
      rw [mul_left_comm, mul_sum]
      congr 1
      refine sum_congr rfl fun s _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun t _ => by ring
    rw [sum_congr rfl fun a _ => e a, ← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    simp only [hG]
    rw [mul_sum]
  -- `‖G‖² = (p² - 2p)‖g‖² + (∑ g)²`
  have hGsq : ∑ s, ∑ t, G s t ^ 2 = ((p : ℝ) ^ 2 - 2 * p) * ∑ a, g a ^ 2 + (∑ a, g a) ^ 2 := by
    rw [← quad_two_root_sq g]
    have e : ∀ s t, G s t ^ 2 = ∑ a, ∑ a', g a * g a' *
        ((chiRe (s - a) * chiRe (s - a')) * (chiRe (t - a) * chiRe (t - a'))) := by
      intro s t
      simp only [hG]
      rw [sq, sum_mul_sum]
      exact sum_congr rfl fun a _ => sum_congr rfl fun a' _ => by ring
    simp_rw [e]
    have swap : ∀ f : ZMod p → ZMod p → ZMod p → ZMod p → ℝ,
        ∑ s, ∑ t, ∑ a, ∑ a', f s t a a' = ∑ a, ∑ a', ∑ s, ∑ t, f s t a a' := by
      intro f
      calc ∑ s, ∑ t, ∑ a, ∑ a', f s t a a' = ∑ s, ∑ a, ∑ t, ∑ a', f s t a a' :=
            sum_congr rfl fun s _ => sum_comm
        _ = ∑ a, ∑ s, ∑ t, ∑ a', f s t a a' := sum_comm
        _ = ∑ a, ∑ s, ∑ a', ∑ t, f s t a a' :=
            sum_congr rfl fun a _ => sum_congr rfl fun s _ => sum_comm
        _ = ∑ a, ∑ a', ∑ s, ∑ t, f s t a a' := sum_congr rfl fun a _ => sum_comm
    rw [swap]
    refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
    have hfac : ∑ s, ∑ t, g a * g a' *
        ((chiRe (s - a) * chiRe (s - a')) * (chiRe (t - a) * chiRe (t - a'))) =
        g a * g a' * ((∑ s, chiRe (s - a) * chiRe (s - a')) *
          (∑ t, chiRe (t - a) * chiRe (t - a'))) := by
      rw [sum_mul_sum, mul_sum]
      exact sum_congr rfl fun s _ => by rw [mul_sum]
    have hsum : ∑ s, chiRe (s - a) * chiRe (s - a') =
        (p : ℝ) * (if a = a' then 1 else 0) - 1 := by
      rw [sum_congr rfl fun s _ => chiRe_sub_comm_mul s a a']
      exact sum_chiRe_mul hp2 a a'
    rw [hfac, hsum]
    ring
  have hcs : (∑ s, ∑ t, F s t * G s t) ^ 2 ≤ (∑ s, ∑ t, F s t ^ 2) * ∑ s, ∑ t, G s t ^ 2 := by
    have := sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod p × ZMod p))
      (fun x => F x.1 x.2) (fun x => G x.1 x.2)
    simpa only [Fintype.sum_prod_type] using this
  have hsg := sq_sum_le g
  have hS : 0 ≤ ∑ a, g a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
  have hF : 0 ≤ ∑ s, ∑ t, F s t ^ 2 := sum_nonneg fun s _ => sum_nonneg fun t _ => sq_nonneg _
  have hG2 : ∑ s, ∑ t, G s t ^ 2 ≤ ((p : ℝ) ^ 2 - p) * ∑ a, g a ^ 2 := by
    rw [hGsq]; nlinarith
  -- `‖g‖⁴ ≤ p⁻⁴ ‖F‖² ‖G‖² ≤ p⁻⁴ ‖F‖² (p² - p) ‖g‖²`
  have hkey : (∑ a, g a ^ 2) ^ 2 ≤ (1 / (p : ℝ) ^ 2) ^ 2 * (∑ s, ∑ t, F s t ^ 2) *
      (((p : ℝ) ^ 2 - p) * ∑ a, g a ^ 2) := by
    have h1 : (∑ a, g a ^ 2) ^ 2 = (1 / (p : ℝ) ^ 2) ^ 2 * (∑ s, ∑ t, F s t * G s t) ^ 2 := by
      rw [hid, mul_pow]
    rw [h1, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hcs.trans (mul_le_mul_of_nonneg_left hG2 hF)
  have hmain : ∑ a, g a ^ 2 ≤ (1 / (p : ℝ) ^ 2) ^ 2 * (∑ s, ∑ t, F s t ^ 2) * ((p : ℝ) ^ 2 - p) := by
    rcases hS.lt_or_eq with hpos | hzero
    · have := hkey
      rw [sq (∑ a, g a ^ 2)] at this
      have h' : (∑ a, g a ^ 2) * (∑ a, g a ^ 2) ≤
          ((1 / (p : ℝ) ^ 2) ^ 2 * (∑ s, ∑ t, F s t ^ 2) * ((p : ℝ) ^ 2 - p)) * ∑ a, g a ^ 2 := by
        linarith
      exact le_of_mul_le_mul_right h' hpos
    · rw [← hzero]
      have : (0 : ℝ) ≤ (p : ℝ) ^ 2 - p := by nlinarith
      positivity
  calc (1 / (p : ℝ)) * ∑ a, g a ^ 2
      ≤ (1 / (p : ℝ)) * ((1 / (p : ℝ) ^ 2) ^ 2 * (∑ s, ∑ t, F s t ^ 2) * ((p : ℝ) ^ 2 - p)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * ((1 / (p : ℝ) ^ 2) * ∑ s, ∑ t, F s t ^ 2) := by
        field_simp


/-! ## Part (b): the diagonal pieces of `S` -/

/-- `ψ_y(s)² = 1_{s ∉ {y₀, y₁}}`. -/
theorem psi_sq (s y0 y1 : ZMod p) :
    (chiRe (s - y0) * chiRe (s - y1)) ^ 2 = (if s = y0 then 0 else 1) * (if s = y1 then 0 else 1) := by
  rw [mul_pow, chiRe_sq, chiRe_sq]
  simp only [sub_eq_zero]

/-- `∑_s ψ_y(s)² f(s) = ∑ f - f(y₀) - f(y₁)` for `y₀ ≠ y₁`. -/
theorem sum_psi_sq_mul {y0 y1 : ZMod p} (hy : y0 ≠ y1) (f : ZMod p → ℝ) :
    ∑ s, (chiRe (s - y0) * chiRe (s - y1)) ^ 2 * f s = ∑ s, f s - f y0 - f y1 := by
  have e : ∀ s, (chiRe (s - y0) * chiRe (s - y1)) ^ 2 * f s =
      f s - (if s = y0 then f s else 0) - (if s = y1 then f s else 0) := by
    intro s
    rw [psi_sq]
    by_cases h0 : s = y0
    · have h1 : ¬ s = y1 := fun h => hy (h0 ▸ h)
      simp only [eq_true h0, eq_false h1, ↓reduceIte]
      ring
    · by_cases h1 : s = y1
      · simp only [eq_false h0, eq_true h1, ↓reduceIte]
        ring
      · simp only [eq_false h0, eq_false h1, ↓reduceIte]
        ring
  rw [sum_congr rfl fun s _ => e s, sum_sub_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  simp

/-- **`cor:raw-pair-maps`(b), on the diagonal**: for `y₀ ≠ y₁` and `f` on `𝔽_p`, with
`(Df)(s, u) = √p 1_{s=u} f(s)`, `(SDf)(y) = r E f - q r (f(y₀) + f(y₁))`. In particular
`Sd = r(1 - 2q)` for `d = D1`, and `(RDf)(y) = -q r (f(y₀) + f(y₁))` when `E f = 0`. -/
theorem S_diag {y0 y1 : ZMod p} (hy : y0 ≠ y1) (f : ZMod p → ℝ) :
    (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, chiRe (s - y0) * chiRe (s - y1) *
        (chiRe (u - y0) * chiRe (u - y1)) * (Real.sqrt p * (if s = u then 1 else 0) * f s) =
      (1 / Real.sqrt p) * ((1 / (p : ℝ)) * ∑ s, f s) -
        (1 / (p : ℝ)) * (1 / Real.sqrt p) * (f y0 + f y1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hsq0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have e : ∀ s, ∑ u, chiRe (s - y0) * chiRe (s - y1) * (chiRe (u - y0) * chiRe (u - y1)) *
      (Real.sqrt p * (if s = u then 1 else 0) * f s) =
      Real.sqrt p * ((chiRe (s - y0) * chiRe (s - y1)) ^ 2 * f s) := by
    intro s
    rw [sum_eq_single s]
    · simp only [↓reduceIte, mul_one]; ring
    · intro u _ hu; simp [Ne.symm hu]
    · intro h; exact absurd (mem_univ s) h
  rw [sum_congr rfl fun s _ => e s, ← mul_sum, sum_psi_sq_mul hy]
  field_simp
  rw [Real.sq_sqrt hp0.le]
  ring

/-- **`cor:raw-pair-maps`(b), `‖RDf‖ ≤ √2 q r ‖f‖`**: for `E f = 0` and `y` uniform on distinct
pairs, `E_y (q r (f(y₀) + f(y₁)))² ≤ 2 q³ E f²`. -/
theorem RD_norm {f : ZMod p → ℝ} (hf : ∑ s, f s = 0) :
    (1 / ((p : ℝ) * (p - 1))) * ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2),
        ((1 / (p : ℝ)) * (1 / Real.sqrt p) * (f y.1 + f y.2)) ^ 2 ≤
      2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ)) * ∑ s, f s ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  set S2 := ∑ s, f s ^ 2
  -- the sum over distinct pairs of `(f y₀ + f y₁)²`
  have hall : ∑ y : ZMod p × ZMod p, (f y.1 + f y.2) ^ 2 = 2 * (p : ℝ) * S2 := by
    rw [Fintype.sum_prod_type]
    have e : ∀ a b : ZMod p, (f a + f b) ^ 2 = f a ^ 2 + f b ^ 2 + 2 * f a * f b :=
      fun a b => by ring
    simp_rw [e, sum_add_distrib]
    have t1 : ∑ a : ZMod p, ∑ _b : ZMod p, f a ^ 2 = (p : ℝ) * S2 := by
      rw [sum_congr rfl fun a _ => by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul], ← mul_sum]
    have t2 : ∑ _a : ZMod p, ∑ b : ZMod p, f b ^ 2 = (p : ℝ) * S2 := by
      rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    have t3 : ∑ a : ZMod p, ∑ b : ZMod p, 2 * f a * f b = 0 := by
      refine sum_eq_zero fun a _ => ?_
      rw [← mul_sum, hf, mul_zero]
    rw [t1, t2, t3]
    ring
  have hdiag : ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 = y.2), (f y.1 + f y.2) ^ 2 =
      4 * S2 := by
    rw [sum_filter, Fintype.sum_prod_type]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [mul_sum]
    exact sum_congr rfl fun a _ => by ring
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (ZMod p × ZMod p))
    (fun y => y.1 = y.2) (fun y => (f y.1 + f y.2) ^ 2)
  have hD : ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2), (f y.1 + f y.2) ^ 2 =
      (2 * (p : ℝ) - 4) * S2 := by
    simp only [ne_eq]
    linarith
  have hS2 : 0 ≤ S2 := sum_nonneg fun s _ => sq_nonneg _
  have hpt : ∀ y : ZMod p × ZMod p, ((1 / (p : ℝ)) * (1 / Real.sqrt p) * (f y.1 + f y.2)) ^ 2 =
      (1 / (p : ℝ)) ^ 3 * (f y.1 + f y.2) ^ 2 := by
    intro y
    rw [mul_pow, mul_pow, div_pow (1 : ℝ) (Real.sqrt p), one_pow, hsq]
    ring
  rw [sum_congr rfl fun y _ => hpt y, ← mul_sum, hD]
  have hp1 : (0 : ℝ) < (p : ℝ) * (p - 1) := by nlinarith
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [show 1 / ((p : ℝ) * (p - 1)) * ((1 / (p : ℝ)) ^ 3 * ((2 * (p : ℝ) - 4) * S2)) =
    2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ)) * S2) * ((p - 2) / (p - 1)) by field_simp; ring]
  have hfrac : ((p : ℝ) - 2) / (p - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hnn : 0 ≤ 2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ)) * S2) := by positivity
  calc 2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ)) * S2) * ((p - 2) / (p - 1))
      ≤ 2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ)) * S2) * 1 := mul_le_mul_of_nonneg_left hfrac hnn
    _ = 2 * (1 / (p : ℝ)) ^ 3 * ((1 / (p : ℝ)) * S2) := mul_one _

/-- **`cor:raw-pair-maps`(b), the rows of `R`**: for every `y` with `y₀ ≠ y₁`, the row
`(s, u) ↦ ψ_y(s)ψ_y(u) - r(1 - 2q) d(s, u)` has `L²(𝔽_p²)` norm at most one:
its square is `(1 - 2q)²(1 - q)`. -/
theorem R_row_norm {y0 y1 : ZMod p} (hy : y0 ≠ y1) :
    (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, (chiRe (s - y0) * chiRe (s - y1) * (chiRe (u - y0) * chiRe (u - y1)) -
        (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * (Real.sqrt p * (if s = u then 1 else 0))) ^ 2 =
      (1 - 2 / (p : ℝ)) ^ 2 * (1 - 1 / (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsq0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hc : (1 / Real.sqrt p) * Real.sqrt p = 1 := by field_simp
  set c : ℝ := 1 - 2 / (p : ℝ)
  set ψ : ZMod p → ℝ := fun s => chiRe (s - y0) * chiRe (s - y1)
  have hψ2 : ∀ s, ψ s ^ 2 = (if s = y0 then 0 else 1) * (if s = y1 then 0 else 1) := fun s => psi_sq s y0 y1
  have hsumψ2 : ∑ s, ψ s ^ 2 = (p : ℝ) - 2 := by
    have := sum_psi_sq_mul hy (fun _ => (1 : ℝ))
    simp only [mul_one] at this
    rw [show ∑ s, ψ s ^ 2 = ∑ s, (chiRe (s - y0) * chiRe (s - y1)) ^ 2 from rfl, this]
    simp [ZMod.card]
    ring
  have e : ∀ s u, (ψ s * ψ u - (1 / Real.sqrt p) * c * (Real.sqrt p * (if s = u then 1 else 0))) ^ 2 =
      ψ s ^ 2 * ψ u ^ 2 - (if s = u then 2 * c * ψ s ^ 2 - c ^ 2 else 0) := by
    intro s u
    by_cases h : s = u
    · subst h
      simp only [↓reduceIte, mul_one]
      rw [show (1 / Real.sqrt p) * c * Real.sqrt p = c by
        rw [mul_comm (1 / Real.sqrt p) c, mul_assoc, hc, mul_one]]
      ring
    · simp only [h, ↓reduceIte, mul_zero, sub_zero]
      ring
  simp only [ψ] at e
  rw [sum_congr rfl fun s _ => sum_congr rfl fun u _ => e s u]
  simp_rw [sum_sub_distrib]
  simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  have h1 : ∑ s, ∑ u, (chiRe (s - y0) * chiRe (s - y1)) ^ 2 * (chiRe (u - y0) * chiRe (u - y1)) ^ 2 =
      ((p : ℝ) - 2) ^ 2 := by
    rw [← sum_mul_sum]
    have : ∑ s, (chiRe (s - y0) * chiRe (s - y1)) ^ 2 = (p : ℝ) - 2 := hsumψ2
    rw [this, sq]
  have h2 : ∑ s, (2 * c * (chiRe (s - y0) * chiRe (s - y1)) ^ 2 - c ^ 2) =
      2 * c * ((p : ℝ) - 2) - (p : ℝ) * c ^ 2 := by
    rw [sum_sub_distrib, ← mul_sum]
    have : ∑ s, (chiRe (s - y0) * chiRe (s - y1)) ^ 2 = (p : ℝ) - 2 := hsumψ2
    rw [this]
    simp [ZMod.card]
  rw [h1, h2]
  simp only [c]
  field_simp
  ring

end Sarkozy.SecondOrder
