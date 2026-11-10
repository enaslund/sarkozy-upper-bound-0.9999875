module

public import Sarkozy.RecordExpansion.Selections
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Monomials of selections and the bound `e^S cosh A - 1`

Section 10 of the paper, `lem:record:record-expansion` (ii) without classes:
the monomial of a selection `ω` is `π_ω = ∏_{b ∈ X} π^{ε_b}_{b,t_b}`, and the
sum of the monomials of all selections is dominated by `e^S cosh A - 1`, where
`S = ∑_b s_b`, `A = ∑_b a_b` and `s_b = ∑_t π^s_{b,t}`, `a_b = ∑_t π^a_{b,t}`
are the per-atom totals of (CP4)(b).

The paper argues through formal power series: `e^{S(x)} cosh A(x) - 1` has
coefficient one on every squarefree monomial of even skew degree, in
particular on the monomial of every selection, and nonnegative coefficients
elsewhere. Here the sum over selections is computed exactly,

  `∑_{ω selection} π_ω = ½ [∏_b (1 + s_b + a_b) + ∏_b (1 + s_b - a_b)] - 1`
  (`sum_monomial_selections`),

and this closed form is bounded by `e^S cosh A - 1` for nonnegative prices
(`half_prod_add_prod_le_exp_mul_cosh`, `sum_monomial_selections_le`), by
induction over the atoms using `1 + s ≤ e^s`, `1 ≤ cosh a` and `a ≤ sinh a`.
The prices are arbitrary nonnegative reals: no smallness and no relation
between the `π^ε_{b,t}` and the measures is used here.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

open Choice

/-! ### Prices of entries -/

/-- The price of one entry: `1` off the selected atoms and `π^ε_{b,t}` at a
selected atom with record `t` and type `ε`. -/
def entryPrice {α : Type*} (πb : α → ChangeType → ℝ) : Option (α × ChangeType) → ℝ
  | none => 1
  | some (t, e) => πb t e

theorem sum_entryPrice {α : Type*} [Fintype α] (πb : α → ChangeType → ℝ) :
    ∑ o, entryPrice πb o = 1 + (∑ t, πb t .sym) + ∑ t, πb t .skew := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [entryPrice, sum_changeType, Finset.sum_add_distrib]
  ring

theorem sum_entrySign_mul_entryPrice {α : Type*} [Fintype α] (πb : α → ChangeType → ℝ) :
    ∑ o, entrySign o * entryPrice πb o = 1 + (∑ t, πb t .sym) - ∑ t, πb t .skew := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [entryPrice, entrySign, isSkewEntry, sum_changeType, Finset.sum_add_distrib]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, Finset.sum_neg_distrib]
  ring

theorem entryPrice_nonneg {α : Type*} {πb : α → ChangeType → ℝ}
    (hπ : ∀ t e, 0 ≤ πb t e) (o : Option (α × ChangeType)) : 0 ≤ entryPrice πb o := by
  rcases o with _ | ⟨t, e⟩
  · exact zero_le_one
  · exact hπ t e

section Monomials

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]

/-- The monomial `π_ω = ∏_{b ∈ X} π^{ε_b}_{b,t_b}` of a choice (equal to `1` for
the empty choice). -/
def monomial (π : ∀ b, T b → ChangeType → ℝ) (ω : Choice T) : ℝ :=
  ∏ b, entryPrice (π b) (ω b)

/-- The symmetric total `s_b = ∑_t π^s_{b,t}` of an atom. -/
def symTotal (π : ∀ b, T b → ChangeType → ℝ) (b : J) : ℝ := ∑ t, π b t .sym

/-- The skew total `a_b = ∑_t π^a_{b,t}` of an atom. -/
def skewTotal (π : ∀ b, T b → ChangeType → ℝ) (b : J) : ℝ := ∑ t, π b t .skew

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem monomial_nonneg {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (ω : Choice T) : 0 ≤ monomial π ω :=
  Finset.prod_nonneg fun b _ => entryPrice_nonneg (hπ b) (ω b)

omit [DecidableEq J] [∀ b, Fintype (T b)] in
theorem monomial_empty (π : ∀ b, T b → ChangeType → ℝ) :
    monomial π (Choice.empty : Choice T) = 1 :=
  Finset.prod_eq_one fun _ _ => rfl

/-- The sum of the monomials of all choices, the empty one included. -/
theorem sum_monomial (π : ∀ b, T b → ChangeType → ℝ) :
    ∑ ω : Choice T, monomial π ω = ∏ b, (1 + symTotal π b + skewTotal π b) := by
  unfold monomial
  rw [← Fintype.prod_sum (fun b o => entryPrice (π b) o)]
  simp only [sum_entryPrice, symTotal, skewTotal]

/-- The signed sum of the monomials, the sign being `(-1)^(number of skew types)`. -/
theorem sum_signed_monomial (π : ∀ b, T b → ChangeType → ℝ) :
    ∑ ω : Choice T, (-1 : ℝ) ^ skewCount ω * monomial π ω =
      ∏ b, (1 + symTotal π b - skewTotal π b) := by
  have he (ω : Choice T) : (-1 : ℝ) ^ skewCount ω * monomial π ω =
      ∏ b, entrySign (ω b) * entryPrice (π b) (ω b) := by
    rw [← prod_entrySign, monomial, ← Finset.prod_mul_distrib]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun b o => entrySign o * entryPrice (π b) o)]
  simp only [sum_entrySign_mul_entryPrice, symTotal, skewTotal]

theorem even_indicator (k : ℕ) : (1 + (-1 : ℝ) ^ k) / 2 = if Even k then 1 else 0 := by
  split_ifs with hk
  · rw [hk.neg_one_pow]
    norm_num
  · rw [(Nat.not_even_iff_odd.mp hk).neg_one_pow]
    norm_num

/-- The sum of the monomials of the choices with an even number of skew types,
the empty one included. -/
theorem sum_monomial_even (π : ∀ b, T b → ChangeType → ℝ) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => Even (skewCount ω)), monomial π ω =
      ((∏ b, (1 + symTotal π b + skewTotal π b)) +
        ∏ b, (1 + symTotal π b - skewTotal π b)) / 2 := by
  rw [Finset.sum_filter, ← sum_monomial, ← sum_signed_monomial, ← Finset.sum_add_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs with hk
  · rw [hk.neg_one_pow]
    ring
  · rw [(Nat.not_even_iff_odd.mp hk).neg_one_pow]
    ring

/-- **The sum over selections** (`lem:record:record-expansion` (ii), without
classes, evaluated exactly): the monomials of the selections of (CP4)(c) sum to
`½ [∏_b (1 + s_b + a_b) + ∏_b (1 + s_b - a_b)] - 1`. -/
theorem sum_monomial_selections [∀ b, DecidableEq (T b)] (π : ∀ b, T b → ChangeType → ℝ) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), monomial π ω =
      ((∏ b, (1 + symTotal π b + skewTotal π b)) +
        ∏ b, (1 + symTotal π b - skewTotal π b)) / 2 - 1 := by
  have hs : univ.filter (fun ω : Choice T => IsSelection ω) =
      (univ.filter fun ω : Choice T => Even (skewCount ω)).erase Choice.empty := by
    ext ω
    rw [mem_filter, mem_erase, mem_filter]
    simp only [mem_univ, true_and]
    rfl
  have hmem : (Choice.empty : Choice T) ∈ univ.filter fun ω : Choice T => Even (skewCount ω) := by
    rw [mem_filter, skewCount_empty]
    exact ⟨mem_univ _, ⟨0, rfl⟩⟩
  rw [← sum_monomial_even, ← Finset.add_sum_erase _ _ hmem, monomial_empty, hs]
  ring

end Monomials

/-! ### The exponential bound -/

section Exponential

variable {J : Type*} [DecidableEq J]

/-- The inductive bounds behind `e^S cosh A`: for nonnegative `s_b`, `a_b` and the
products `P = ∏ (1 + s_b + a_b)`, `M = ∏ (1 + s_b - a_b)` over a finite set,
`0 ≤ P ± M`, `P + M ≤ 2 e^S cosh A` and `P - M ≤ 2 e^S sinh A`. -/
theorem prod_bounds (s a : J → ℝ) (hs : ∀ b, 0 ≤ s b) (ha : ∀ b, 0 ≤ a b) (U : Finset J) :
    0 ≤ (∏ b ∈ U, (1 + s b + a b)) + ∏ b ∈ U, (1 + s b - a b) ∧
    0 ≤ (∏ b ∈ U, (1 + s b + a b)) - ∏ b ∈ U, (1 + s b - a b) ∧
    (∏ b ∈ U, (1 + s b + a b)) + ∏ b ∈ U, (1 + s b - a b) ≤
      2 * (Real.exp (∑ b ∈ U, s b) * Real.cosh (∑ b ∈ U, a b)) ∧
    (∏ b ∈ U, (1 + s b + a b)) - ∏ b ∈ U, (1 + s b - a b) ≤
      2 * (Real.exp (∑ b ∈ U, s b) * Real.sinh (∑ b ∈ U, a b)) := by
  induction U using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sum_empty, Real.exp_zero, Real.cosh_zero, Real.sinh_zero]
    norm_num
  | @insert b U hb ih =>
    obtain ⟨hE0, hO0, hE, hO⟩ := ih
    rw [prod_insert hb, prod_insert hb, sum_insert hb, sum_insert hb, Real.exp_add,
      Real.cosh_add, Real.sinh_add]
    set P := ∏ b ∈ U, (1 + s b + a b)
    set M := ∏ b ∈ U, (1 + s b - a b)
    set S := ∑ b ∈ U, s b
    set A := ∑ b ∈ U, a b
    have hsb := hs b
    have hab := ha b
    have hA : 0 ≤ A := Finset.sum_nonneg fun b _ => ha b
    have hex : 0 < Real.exp S := Real.exp_pos S
    have hch : 0 < Real.cosh A := Real.cosh_pos A
    have hsh : 0 ≤ Real.sinh A := Real.sinh_nonneg_iff.mpr hA
    have hes : 1 + s b ≤ Real.exp (s b) := by linarith [Real.add_one_le_exp (s b)]
    have hes1 : 1 ≤ Real.exp (s b) := by linarith
    have hca : 1 ≤ Real.cosh (a b) := Real.one_le_cosh (a b)
    have hsa : a b ≤ Real.sinh (a b) := Real.self_le_sinh_iff.mpr hab
    have hsa0 : 0 ≤ Real.sinh (a b) := Real.sinh_nonneg_iff.mpr hab
    have hEP : (1 + s b + a b) * P + (1 + s b - a b) * M =
        (1 + s b) * (P + M) + a b * (P - M) := by ring
    have hOP : (1 + s b + a b) * P - (1 + s b - a b) * M =
        (1 + s b) * (P - M) + a b * (P + M) := by ring
    have hC : 0 ≤ 2 * (Real.exp S * Real.cosh A) := by positivity
    have hD : 0 ≤ 2 * (Real.exp S * Real.sinh A) := by positivity
    -- the two linear pieces, bounded factor by factor
    have h1 : (1 + s b) * (P + M) ≤ Real.exp (s b) * Real.cosh (a b) *
        (2 * (Real.exp S * Real.cosh A)) := by
      calc (1 + s b) * (P + M) ≤ (1 + s b) * (2 * (Real.exp S * Real.cosh A)) :=
            mul_le_mul_of_nonneg_left hE (by linarith)
        _ ≤ Real.exp (s b) * 1 * (2 * (Real.exp S * Real.cosh A)) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right hes hC
        _ ≤ Real.exp (s b) * Real.cosh (a b) * (2 * (Real.exp S * Real.cosh A)) := by
            apply mul_le_mul_of_nonneg_right _ hC
            exact mul_le_mul_of_nonneg_left hca (by positivity)
    have h2 : a b * (P - M) ≤ Real.exp (s b) * Real.sinh (a b) *
        (2 * (Real.exp S * Real.sinh A)) := by
      calc a b * (P - M) ≤ a b * (2 * (Real.exp S * Real.sinh A)) :=
            mul_le_mul_of_nonneg_left hO hab
        _ ≤ 1 * Real.sinh (a b) * (2 * (Real.exp S * Real.sinh A)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right hsa hD
        _ ≤ Real.exp (s b) * Real.sinh (a b) * (2 * (Real.exp S * Real.sinh A)) := by
            apply mul_le_mul_of_nonneg_right _ hD
            exact mul_le_mul_of_nonneg_right hes1 hsa0
    have h3 : (1 + s b) * (P - M) ≤ Real.exp (s b) * Real.cosh (a b) *
        (2 * (Real.exp S * Real.sinh A)) := by
      calc (1 + s b) * (P - M) ≤ (1 + s b) * (2 * (Real.exp S * Real.sinh A)) :=
            mul_le_mul_of_nonneg_left hO (by linarith)
        _ ≤ Real.exp (s b) * 1 * (2 * (Real.exp S * Real.sinh A)) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right hes hD
        _ ≤ Real.exp (s b) * Real.cosh (a b) * (2 * (Real.exp S * Real.sinh A)) := by
            apply mul_le_mul_of_nonneg_right _ hD
            exact mul_le_mul_of_nonneg_left hca (by positivity)
    have h4 : a b * (P + M) ≤ Real.exp (s b) * Real.sinh (a b) *
        (2 * (Real.exp S * Real.cosh A)) := by
      calc a b * (P + M) ≤ a b * (2 * (Real.exp S * Real.cosh A)) :=
            mul_le_mul_of_nonneg_left hE hab
        _ ≤ 1 * Real.sinh (a b) * (2 * (Real.exp S * Real.cosh A)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right hsa hC
        _ ≤ Real.exp (s b) * Real.sinh (a b) * (2 * (Real.exp S * Real.cosh A)) := by
            apply mul_le_mul_of_nonneg_right _ hC
            exact mul_le_mul_of_nonneg_right hes1 hsa0
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hEP]
      have := mul_nonneg (show (0 : ℝ) ≤ 1 + s b by linarith) hE0
      have := mul_nonneg hab hO0
      linarith
    · rw [hOP]
      have := mul_nonneg (show (0 : ℝ) ≤ 1 + s b by linarith) hO0
      have := mul_nonneg hab hE0
      linarith
    · rw [hEP]
      have he : 2 * (Real.exp (s b) * Real.exp S *
          (Real.cosh (a b) * Real.cosh A + Real.sinh (a b) * Real.sinh A)) =
          Real.exp (s b) * Real.cosh (a b) * (2 * (Real.exp S * Real.cosh A)) +
          Real.exp (s b) * Real.sinh (a b) * (2 * (Real.exp S * Real.sinh A)) := by ring
      rw [he]
      linarith
    · rw [hOP]
      have he : 2 * (Real.exp (s b) * Real.exp S *
          (Real.sinh (a b) * Real.cosh A + Real.cosh (a b) * Real.sinh A)) =
          Real.exp (s b) * Real.cosh (a b) * (2 * (Real.exp S * Real.sinh A)) +
          Real.exp (s b) * Real.sinh (a b) * (2 * (Real.exp S * Real.cosh A)) := by ring
      rw [he]
      linarith

/-- `½ [∏_b (1 + s_b + a_b) + ∏_b (1 + s_b - a_b)] ≤ e^S cosh A` for nonnegative
`s_b`, `a_b`, with `S = ∑_b s_b`, `A = ∑_b a_b`. -/
theorem half_prod_add_prod_le_exp_mul_cosh [Fintype J] (s a : J → ℝ) (hs : ∀ b, 0 ≤ s b)
    (ha : ∀ b, 0 ≤ a b) :
    ((∏ b, (1 + s b + a b)) + ∏ b, (1 + s b - a b)) / 2 ≤
      Real.exp (∑ b, s b) * Real.cosh (∑ b, a b) := by
  have h := (prod_bounds s a hs ha univ).2.2.1
  linarith

end Exponential

section Bound

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)]

/-- **The monomial sum is at most `e^S cosh A - 1`**
(`lem:record:record-expansion` (ii), without classes): for nonnegative prices
`π^ε_{b,t}`, `∑_ω π_ω ≤ e^S cosh A - 1`, the sum over the selections of (CP4)(c),
with `S = ∑_b s_b` and `A = ∑_b a_b`. -/
theorem sum_monomial_selections_le {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), monomial π ω ≤
      Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1 := by
  rw [sum_monomial_selections]
  have h := half_prod_add_prod_le_exp_mul_cosh (symTotal π) (skewTotal π)
    (fun b => Finset.sum_nonneg fun t _ => hπ b t _)
    (fun b => Finset.sum_nonneg fun t _ => hπ b t _)
  linarith

end Bound

end Sarkozy.RecordExpansion
