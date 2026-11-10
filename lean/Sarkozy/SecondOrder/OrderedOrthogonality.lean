module

public import Mathlib

/-!
# Ordered almost orthogonality (`lem:ordered-orthogonality`)

`paper/sections/15_second_order.tex`. A random vector `x = (x_i)_{i∈ι}` with values in a finite set
`X` and an arbitrary law `μ`; `F = ∑_i F_i`, where `F_i` depends only on `(x_j)_{j ≤ i}`. If
`E[F_i² | x_{-i}] ≤ α_i²` and `|E[F_i | x_{-i}]| ≤ β_i` almost surely, then
`E F² ≤ ∑_i α_i² + 2 ∑_i β_i ∑_{j<i} α_j`.

The conditional hypotheses are stated fibrewise, without conditional expectations: for every `x`
and the fibre `{x[i ↦ y] : y ∈ X}` of `x_{-i}`,
`∑_y μ(x[i↦y]) F_i(x[i↦y])² ≤ α_i² ∑_y μ(x[i↦y])` and
`|∑_y μ(x[i↦y]) F_i(x[i↦y])| ≤ β_i ∑_y μ(x[i↦y])`.
On fibres of positive mass these are exactly the conditional statements; on null fibres they are
trivially true.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]

/-- Resampling coordinate `i` is measure preserving: `∑_x ∑_y g(x[i ↦ y]) = |X| ∑_x g x`. -/
theorem sum_sum_update (i : ι) (g : (ι → X) → ℝ) :
    ∑ x, ∑ y, g (Function.update x i y) = (Fintype.card X : ℝ) * ∑ x, g x := by
  let e : ((ι → X) × X) ≃ ((ι → X) × X) :=
    { toFun := fun q => (Function.update q.1 i q.2, q.1 i)
      invFun := fun q => (Function.update q.1 i q.2, q.1 i)
      left_inv := fun q => by simp
      right_inv := fun q => by simp }
  have h := Equiv.sum_comp e (fun q => g q.1)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  simp only [e, Equiv.coe_fn_mk] at h
  rw [h]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]

variable [LinearOrder ι]

/-- **`lem:ordered-orthogonality`**, with the conditional hypotheses in fibrewise form. -/
theorem ordered_orthogonality [Nonempty X] (μ : (ι → X) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) (F : ι → (ι → X) → ℝ)
    (hF : ∀ i x x', (∀ k ≤ i, x k = x' k) → F i x = F i x')
    (α β : ι → ℝ) (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (h2 : ∀ i x, ∑ y, μ (Function.update x i y) * F i (Function.update x i y) ^ 2 ≤
        α i ^ 2 * ∑ y, μ (Function.update x i y))
    (h1 : ∀ i x, |∑ y, μ (Function.update x i y) * F i (Function.update x i y)| ≤
        β i * ∑ y, μ (Function.update x i y)) :
    ∑ x, μ x * (∑ i, F i x) ^ 2 ≤
      ∑ i, α i ^ 2 + 2 * ∑ i, β i * ∑ j ∈ univ.filter (· < i), α j := by
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  -- averaging over the fibres of coordinate `i`
  have havg : ∀ i (g : (ι → X) → ℝ), ∑ x, g x =
      (Fintype.card X : ℝ)⁻¹ * ∑ x, ∑ y, g (Function.update x i y) := by
    intro i g
    rw [sum_sum_update, ← mul_assoc, inv_mul_cancel₀ hX.ne', one_mul]
  -- second moments
  have hsq : ∀ i, ∑ x, μ x * F i x ^ 2 ≤ α i ^ 2 := by
    intro i
    rw [havg i (fun x => μ x * F i x ^ 2)]
    calc (Fintype.card X : ℝ)⁻¹ *
          ∑ x, ∑ y, μ (Function.update x i y) * F i (Function.update x i y) ^ 2
        ≤ (Fintype.card X : ℝ)⁻¹ * ∑ x, α i ^ 2 * ∑ y, μ (Function.update x i y) :=
          mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => h2 i x) (by positivity)
      _ = α i ^ 2 * ((Fintype.card X : ℝ)⁻¹ * ∑ x, ∑ y, μ (Function.update x i y)) := by
          rw [← mul_sum]; ring
      _ = α i ^ 2 := by rw [← havg i μ, hμ1, mul_one]
  -- first absolute moments, by Cauchy–Schwarz
  have habs : ∀ j, ∑ x, μ x * |F j x| ≤ α j := by
    intro j
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (μ x))
      (fun x => Real.sqrt (μ x) * |F j x|)
    have e1 : ∀ x, Real.sqrt (μ x) * (Real.sqrt (μ x) * |F j x|) = μ x * |F j x| := by
      intro x; rw [← mul_assoc, Real.mul_self_sqrt (hμ0 x)]
    have e2 : ∀ x, Real.sqrt (μ x) ^ 2 = μ x := fun x => Real.sq_sqrt (hμ0 x)
    have e3 : ∀ x, (Real.sqrt (μ x) * |F j x|) ^ 2 = μ x * F j x ^ 2 := by
      intro x; rw [mul_pow, Real.sq_sqrt (hμ0 x), sq_abs]
    simp only [e1, e2, e3, hμ1, one_mul] at hcs
    have h0 : 0 ≤ ∑ x, μ x * |F j x| := sum_nonneg fun x _ => mul_nonneg (hμ0 x) (abs_nonneg _)
    have := hcs.trans (hsq j)
    nlinarith [hα j]
  -- cross terms: condition on everything but the later coordinate
  have hcross : ∀ i j, j < i → |∑ x, μ x * (F i x * F j x)| ≤ β i * α j := by
    intro i j hji
    have hfix : ∀ x y, F j (Function.update x i y) = F j x := by
      intro x y
      refine hF j _ _ fun k hk => ?_
      exact Function.update_of_ne (ne_of_lt (lt_of_le_of_lt hk hji)) y x
    have hre : ∀ x, ∑ y, μ (Function.update x i y) *
        (F i (Function.update x i y) * F j (Function.update x i y)) =
        F j x * ∑ y, μ (Function.update x i y) * F i (Function.update x i y) := by
      intro x; rw [mul_sum]; exact sum_congr rfl fun y _ => by rw [hfix]; ring
    have hR : ∀ x, ∑ y, μ (Function.update x i y) * |F j (Function.update x i y)| =
        |F j x| * ∑ y, μ (Function.update x i y) := by
      intro x; rw [mul_sum]; exact sum_congr rfl fun y _ => by rw [hfix]; ring
    rw [havg i (fun x => μ x * (F i x * F j x))]
    simp_rw [hre]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hX)]
    calc (Fintype.card X : ℝ)⁻¹ *
          |∑ x, F j x * ∑ y, μ (Function.update x i y) * F i (Function.update x i y)|
        ≤ (Fintype.card X : ℝ)⁻¹ * ∑ x, |F j x| * (β i * ∑ y, μ (Function.update x i y)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (h1 i x) (abs_nonneg _)
      _ = β i * ((Fintype.card X : ℝ)⁻¹ *
            ∑ x, ∑ y, μ (Function.update x i y) * |F j (Function.update x i y)|) := by
          simp_rw [hR]
          have hc : ∀ x, |F j x| * (β i * ∑ y, μ (Function.update x i y)) =
              β i * (|F j x| * ∑ y, μ (Function.update x i y)) := fun x => by ring
          simp_rw [hc, ← mul_sum]
          ring
      _ = β i * ∑ x, μ x * |F j x| := by rw [← havg i (fun x => μ x * |F j x|)]
      _ ≤ β i * α j := mul_le_mul_of_nonneg_left (habs j) (hβ i)
  -- assemble
  set C : ι → ι → ℝ := fun i j => ∑ x, μ x * (F i x * F j x) with hC
  have hexp : ∑ x, μ x * (∑ i, F i x) ^ 2 = ∑ i, ∑ j, C i j := by
    have hx : ∀ x, μ x * (∑ i, F i x) ^ 2 = ∑ i, ∑ j, μ x * (F i x * F j x) := by
      intro x
      rw [sq, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by rw [mul_sum]
    rw [sum_congr rfl fun x _ => hx x, sum_comm]
    exact sum_congr rfl fun i _ => sum_comm
  have hB : ∀ i j, C i j ≤ (if j = i then α i ^ 2 else 0) + (if j < i then β i * α j else 0) +
      (if i < j then β j * α i else 0) := by
    intro i j
    rcases lt_trichotomy j i with h | h | h
    · have h' : ¬ i < j := not_lt.mpr h.le
      simp only [h.ne, h, h', ↓reduceIte, add_zero, zero_add]
      exact (le_abs_self _).trans (hcross i j h)
    · subst h
      simp only [lt_irrefl, ↓reduceIte, add_zero]
      have : C j j = ∑ x, μ x * F j x ^ 2 := sum_congr rfl fun x _ => by ring
      rw [this]; exact hsq j
    · have h' : ¬ j < i := not_lt.mpr h.le
      simp only [h.ne', h, h', ↓reduceIte, add_zero, zero_add]
      have : C i j = ∑ x, μ x * (F j x * F i x) := sum_congr rfl fun x _ => by ring
      rw [this]; exact (le_abs_self _).trans (hcross j i h)
  have hP : ∀ i, β i * ∑ j ∈ univ.filter (· < i), α j =
      ∑ j, if j < i then β i * α j else 0 := by
    intro i; rw [sum_filter, mul_sum]; exact sum_congr rfl fun j _ => by split_ifs <;> simp
  have hQ : ∑ i, ∑ j, (if i < j then β j * α i else 0) =
      ∑ i, ∑ j, (if j < i then β i * α j else 0) := sum_comm
  calc ∑ x, μ x * (∑ i, F i x) ^ 2 = ∑ i, ∑ j, C i j := hexp
    _ ≤ ∑ i, ∑ j, ((if j = i then α i ^ 2 else 0) + (if j < i then β i * α j else 0) +
          (if i < j then β j * α i else 0)) :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hB i j
    _ = ∑ i, α i ^ 2 + 2 * ∑ i, β i * ∑ j ∈ univ.filter (· < i), α j := by
        simp only [sum_add_distrib]
        rw [hQ]
        simp only [hP, sum_ite_eq', mem_univ, ↓reduceIte]
        ring

end Sarkozy.SecondOrder
