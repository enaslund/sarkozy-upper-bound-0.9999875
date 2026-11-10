module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The couplings of the pure-pair substitute (`lem:oct24:pure-pair-substitute`, second part)

`paper/sections/23_envelopes.tex`, `lem:oct24:pure-pair-substitute`: "every `P_i`, `P_ij` and `J`
is the Markov operator of a normalized nonnegative coupling of the actual marginal with itself, and
so is, for singleton coordinates `i ≠ j`, the operator `M_ij = Ṽ_i Ṽ_j^*`: choose a uniform label,
then sample the two halves independently, conditioned on their coordinates `i` and `j`,
respectively, taking that label. Both half marginals of these couplings are the actual marginal,
`M_ii = P_i`, and `V_i V_j^* = M_ij - J`. … each such coupling … is invariant under independent
simultaneous translations."

**Setting.** A finite probability `m` on the object triples `Ω` (the actual half marginal), and
coordinate maps `x_i, x_j : Ω → L` to a finite label set with uniform marginals (`UniformCoord`),
as for the actual half marginals of the fold and matching records. The coupling `M_ij` has the
density `κ(x, x') = |L| m(x) m(x') 1[x_i = x'_j]` (`pairCoupling`), and the conditional expectation
given `x_j = y` is `Ṽ_j^* g (y) = |L| ∑_{x'} m(x') 1[x'_j = y] g(x')` (`condExp`).

**Proved.**
* `pairCoupling_nonneg`, `pairCoupling_fst`, `pairCoupling_snd`, `pairCoupling_mass`: a normalized
  nonnegative coupling with both half marginals `m`;
* `pairCoupling_markov`: its Markov operator is `g ↦ (Ṽ_j^* g)(x_i)`, i.e. `M_ij = Ṽ_i Ṽ_j^*`;
* `condExp_const_mean`, `condExp_of_comp`, `condExp_selfAdjoint`, `condExp_isFunction`: for `i = j`
  the operator `g ↦ Ṽ_i^* g (x_i)` fixes the functions of `x_i`, is self-adjoint in `L²(m)` and has
  its range in the functions of `x_i`: it is the orthogonal projection `P_i` (`M_ii = P_i`);
* `centred_adjoint_mean`: `Ṽ_j^* g` has uniform mean `E_m[g]`, so `V_j^* g = Ṽ_j^* g - E_m[g]` is
  centred and `V_i V_j^* = M_ij - J`;
* `pairCoupling_translation`: if a translation acts on `Ω` shifting both coordinates by the same
  label and preserving `m`, the coupling is invariant under the simultaneous translation of both
  halves.

The couplings `P_ij` and `J` are the analogous constructions with a pair of coordinates and with
no coordinate (`J` is `m ⊗ m`, `pairCoupling` with a constant coordinate map); they are not
spelled out separately.
-/

namespace Sarkozy.Envelopes

open Finset

variable {Ω L : Type*} [Fintype Ω] [Fintype L] [DecidableEq L]

/-- The coordinate `c : Ω → L` has the uniform marginal under `m`. -/
def UniformCoord (m : Ω → ℝ) (c : Ω → L) : Prop :=
  ∀ y, ∑ x, (if c x = y then m x else 0) = (Fintype.card L : ℝ)⁻¹

/-- The coupling `M_ij`: `κ(x, x') = |L| m(x) m(x') 1[x_i = x'_j]`. -/
noncomputable def pairCoupling (m : Ω → ℝ) (xi xj : Ω → L) (x x' : Ω) : ℝ :=
  (Fintype.card L : ℝ) * m x * m x' * (if xi x = xj x' then 1 else 0)

/-- The conditional expectation given `x_j = y` under a law with uniform `x_j`-marginal:
`Ṽ_j^* g (y) = |L| ∑_{x'} m(x') 1[x'_j = y] g(x')`. -/
noncomputable def condExp (m : Ω → ℝ) (c : Ω → L) (g : Ω → ℝ) (y : L) : ℝ :=
  (Fintype.card L : ℝ) * ∑ x', (if c x' = y then m x' * g x' else 0)

omit [Fintype Ω] in
theorem pairCoupling_nonneg {m : Ω → ℝ} (hm : ∀ x, 0 ≤ m x) (xi xj : Ω → L) (x x' : Ω) :
    0 ≤ pairCoupling m xi xj x x' := by
  unfold pairCoupling
  have := hm x; have := hm x'
  split_ifs <;> positivity

/-- **The first half marginal of `M_ij` is `m`.** -/
theorem pairCoupling_fst [Nonempty L] {m : Ω → ℝ} {xi xj : Ω → L} (hj : UniformCoord m xj)
    (x : Ω) : ∑ x', pairCoupling m xi xj x x' = m x := by
  have hL : (Fintype.card L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e : ∀ x', pairCoupling m xi xj x x' =
      (Fintype.card L : ℝ) * m x * (if xj x' = xi x then m x' else 0) := by
    intro x'
    unfold pairCoupling
    by_cases h : xi x = xj x'
    · simp only [h, ↓reduceIte]; ring
    · have h' : ¬ xj x' = xi x := fun h'' => h h''.symm
      simp only [h, h', ↓reduceIte]; ring
  simp only [e]
  rw [← mul_sum, hj (xi x)]
  field_simp

/-- **The second half marginal of `M_ij` is `m`.** -/
theorem pairCoupling_snd [Nonempty L] {m : Ω → ℝ} {xi xj : Ω → L} (hi : UniformCoord m xi)
    (x' : Ω) : ∑ x, pairCoupling m xi xj x x' = m x' := by
  have hL : (Fintype.card L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e : ∀ x, pairCoupling m xi xj x x' =
      (Fintype.card L : ℝ) * m x' * (if xi x = xj x' then m x else 0) := by
    intro x
    unfold pairCoupling
    by_cases h : xi x = xj x'
    · simp only [h, ↓reduceIte]; ring
    · simp only [h, ↓reduceIte]; ring
  simp only [e]
  rw [← mul_sum, hi (xj x')]
  field_simp

/-- **`M_ij` is normalized.** -/
theorem pairCoupling_mass [Nonempty L] {m : Ω → ℝ} {xi xj : Ω → L} (hj : UniformCoord m xj)
    (hm1 : ∑ x, m x = 1) : ∑ x, ∑ x', pairCoupling m xi xj x x' = 1 := by
  simp only [pairCoupling_fst hj, hm1]

/-- **The Markov operator of `M_ij` is `Ṽ_i Ṽ_j^*`:** `∑_{x'} κ(x, x') g(x') = m(x) (Ṽ_j^* g)(x_i)`,
so the conditional expectation of `g(x')` given `x` is `(Ṽ_j^* g)(x_i)`. -/
theorem pairCoupling_markov (m : Ω → ℝ) (xi xj : Ω → L) (g : Ω → ℝ) (x : Ω) :
    ∑ x', pairCoupling m xi xj x x' * g x' = m x * condExp m xj g (xi x) := by
  unfold pairCoupling condExp
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun x' _ => ?_
  by_cases h : xi x = xj x'
  · simp only [h, ↓reduceIte]; ring
  · have h' : ¬ xj x' = xi x := fun h'' => h h''.symm
    simp only [h, h', ↓reduceIte]; ring

/-- `Ṽ_c^*` fixes the functions of `c`: `Ṽ_c^*(φ ∘ c) = φ`. Hence the operator
`g ↦ Ṽ_c^* g (c x)` fixes the functions of `x_c`. -/
theorem condExp_of_comp [Nonempty L] {m : Ω → ℝ} {c : Ω → L} (hc : UniformCoord m c)
    (φ : L → ℝ) (y : L) : condExp m c (fun x => φ (c x)) y = φ y := by
  have hL : (Fintype.card L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold condExp
  have e : ∀ x', (if c x' = y then m x' * φ (c x') else 0) =
      φ y * (if c x' = y then m x' else 0) := by
    intro x'
    by_cases h : c x' = y
    · simp only [h, ↓reduceIte]; ring
    · simp only [h, ↓reduceIte, mul_zero]
  simp only [e]
  rw [← mul_sum, hc y]
  field_simp

/-- The operator `g ↦ Ṽ_c^* g (c ·)` is self-adjoint in `L²(m)`:
`∑ m(x) f(x) Ṽ_c^* g (c x) = ∑ m(x) Ṽ_c^* f (c x) g(x)`. -/
theorem condExp_selfAdjoint (m : Ω → ℝ) (c : Ω → L) (f g : Ω → ℝ) :
    ∑ x, m x * f x * condExp m c g (c x) = ∑ x, m x * condExp m c f (c x) * g x := by
  unfold condExp
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
  by_cases h : c x' = c x
  · simp only [h, ↓reduceIte]; ring
  · have h' : ¬ c x = c x' := fun h'' => h h''.symm
    simp only [h, h', ↓reduceIte, mul_zero, zero_mul]

omit [Fintype Ω] [Fintype L] [DecidableEq L] in
/-- The range of `g ↦ Ṽ_c^* g (c ·)` consists of functions of `x_c`. -/
theorem condExp_isFunction (F : L → ℝ) (c : Ω → L) {x x' : Ω} (h : c x = c x') :
    F (c x) = F (c x') := by rw [h]

/-- **`V_i V_j^* = M_ij - J`.** The uniform mean of `Ṽ_j^* g` is `E_m[g]`; so
`V_j^* g = Ṽ_j^* g - E_m[g]` is the centred conditional expectation, and
`V_i V_j^* g = (Ṽ_j^* g)(x_i) - E_m[g] = M_ij g - J g`. -/
theorem centred_adjoint_mean [Nonempty L] (m : Ω → ℝ) (c : Ω → L) (g : Ω → ℝ) :
    (Fintype.card L : ℝ)⁻¹ * ∑ y, condExp m c g y = ∑ x, m x * g x := by
  have hL : (Fintype.card L : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold condExp
  rw [← mul_sum, ← mul_assoc, inv_mul_cancel₀ hL, one_mul, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_ite_eq]
  simp

omit [Fintype Ω] in
/-- **Translation invariance.** If `τ` acts on `Ω` so that both coordinates are shifted by the same
label (`x_i(τ x) = x_i(x) + a`, `x_j(τ x) = x_j(x) + a`) and `m` is invariant, then `M_ij` is
invariant under the simultaneous translation of both halves. -/
theorem pairCoupling_translation [AddGroup L] {m : Ω → ℝ} {xi xj : Ω → L} (τ : Ω → Ω) (a : L)
    (hm : ∀ x, m (τ x) = m x) (hi : ∀ x, xi (τ x) = xi x + a) (hj : ∀ x, xj (τ x) = xj x + a)
    (x x' : Ω) : pairCoupling m xi xj (τ x) (τ x') = pairCoupling m xi xj x x' := by
  unfold pairCoupling
  rw [hm, hm, hi, hj]
  have : (xi x + a = xj x' + a) ↔ (xi x = xj x') := add_left_inj a
  simp only [this]

/-! ### A toy instance -/

/-- Non-vacuity of `UniformCoord`: the uniform law on `L × L` with the two coordinate maps. -/
example : UniformCoord (fun _ : Fin 2 × Fin 2 => (1 / 4 : ℝ)) Prod.fst := by
  intro y
  simp only [Fintype.card_fin]
  fin_cases y <;> simp [Fintype.sum_prod_type, Fin.sum_univ_two] <;> norm_num

end Sarkozy.Envelopes
