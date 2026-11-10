module

public import Sarkozy.PrimeGram.OldAB

@[expose] public section

/-!
# Elementary bounds for kernels on pairs of halves (SD2)

`paper/sections/21_middle_records.tex`, `subsec:middle-records:notation` ("star monomials have
norms of order `r`"), and the Schur test used throughout section 21.

For kernels `K(x, y)` on pairs of halves `x, y : Fin 3 → 𝔽_p`, with the unnormalized `ℓ²` norms:
* **`separable_bound`**: if `K` contains a cross character `χ(y_j - x_i)` and every other factor
  depends on at most one of `x_i`, `y_j` (formally:
  `K(x[i ↦ a], y[j ↦ b]) = χ(b - a) Φ₁(x, y, a) Φ₂(x, y, b)` with `|Φ₁| ≤ c₁`, `|Φ₂| ≤ c₂`), then
  `|∑_{x,y} g(x) K(x, y) f(y)| ≤ c₁ c₂ √p p² ‖g‖ ‖f‖`. This is the Paley bound `‖χ‖ = √p` in the
  pair `(x_i, y_j)` (PG's `paley_sq_le`) and Cauchy–Schwarz in the four other labels; relative to
  `ν_F ⊗ ν_F` it is `c₁ c₂ · 2r(1 + O(q))`, the order `r` of a star monomial.
* **`schur_bound`**: the Schur test `|∑ g K f| ≤ R ‖g‖ ‖f‖` when all row and column sums of `|K|`
  are at most `R`.
* `sum_update`: `∑_x ∑_a G(x[i ↦ a]) = p ∑_x G(x)`.
-/

open Finset

namespace Sarkozy.SignedDecomp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

omit [Field F] [DecidableEq F] in
/-- `∑_x ∑_a G(x[i ↦ a]) = p ∑_x G(x)`. -/
theorem sum_update (i : Fin 3) (G : (Fin 3 → F) → ℝ) :
    ∑ x : Fin 3 → F, ∑ a, G (Function.update x i a) = qF * ∑ x, G x := by
  set e := Equiv.funSplitAt i F
  have hu : ∀ (x : Fin 3 → F) (a : F), Function.update x i a = e.symm (a, (e x).2) := by
    intro x a
    ext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  simp only [hu]
  rw [sum_comm]
  have h1 : ∀ a : F, ∑ x : Fin 3 → F, G (e.symm (a, (e x).2)) =
      qF * ∑ w : {j // j ≠ i} → F, G (e.symm (a, w)) := by
    intro a
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.apply_symm_apply, sum_const, card_univ, nsmul_eq_mul]
  simp only [h1, ← mul_sum]
  congr 1
  rw [← Fintype.sum_prod_type', e.symm.sum_comp (fun z => G z)]

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)

include hR h3 in
/-- **The Paley form**: `|∑_{a,b} G(a) χ(b - a) H(b)| ≤ √p ‖G‖ ‖H‖`. -/
theorem paley_form (G H : F → ℝ) :
    |∑ a, ∑ b, G a * (χ (b - a) : ℝ) * H b| ≤ √qF * (√(∑ a, G a ^ 2) * √(∑ b, H b ^ 2)) := by
  have e : ∑ a, ∑ b, G a * (χ (b - a) : ℝ) * H b = ∑ a, G a * ∑ b, (χ (b - a) : ℝ) * H b := by
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [e]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ G (fun a => ∑ b, (χ (b - a) : ℝ) * H b)
  have hp := Sarkozy.PrimeGram.paley_sq_le hR h3 H
  have h0 : 0 ≤ ∑ a, G a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
  have h1 : 0 ≤ ∑ b, H b ^ 2 := sum_nonneg fun a _ => sq_nonneg _
  have hq : (0 : ℝ) ≤ qF := Nat.cast_nonneg _
  have hsq : (∑ a, G a * ∑ b, (χ (b - a) : ℝ) * H b) ^ 2 ≤
      qF * ((∑ a, G a ^ 2) * ∑ b, H b ^ 2) := by
    calc (∑ a, G a * ∑ b, (χ (b - a) : ℝ) * H b) ^ 2
        ≤ (∑ a, G a ^ 2) * ∑ a, (∑ b, (χ (b - a) : ℝ) * H b) ^ 2 := hcs
      _ ≤ (∑ a, G a ^ 2) * (qF * ∑ b, H b ^ 2) := mul_le_mul_of_nonneg_left hp h0
      _ = qF * ((∑ a, G a ^ 2) * ∑ b, H b ^ 2) := by ring
  refine (Real.abs_le_sqrt hsq).trans (le_of_eq ?_)
  rw [Real.sqrt_mul hq, Real.sqrt_mul h0]

/-- Cauchy–Schwarz for square roots: `∑_x √(S x) ≤ √N √(∑ S)`, `N` the number of terms. -/
theorem sum_sqrt_le {α : Type} [Fintype α] (S : α → ℝ) (hS : ∀ x, 0 ≤ S x) :
    ∑ x, √(S x) ≤ √(Fintype.card α : ℝ) * √(∑ x, S x) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => (1 : ℝ)) (fun x => √(S x))
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcs
  have e : ∀ x, √(S x) ^ 2 = S x := fun x => Real.sq_sqrt (hS x)
  simp only [e] at hcs
  have h0 : 0 ≤ ∑ x, √(S x) := sum_nonneg fun x _ => Real.sqrt_nonneg _
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le hcs

include hR h3 in
/-- **The bound of a kernel with a separable cross character** (see the module docstring). -/
theorem separable_bound (i j : Fin 3) (K : (Fin 3 → F) → (Fin 3 → F) → ℝ)
    (Φ₁ Φ₂ : (Fin 3 → F) → (Fin 3 → F) → F → ℝ) {c₁ c₂ : ℝ}
    (hΦ₁ : ∀ x y a, |Φ₁ x y a| ≤ c₁) (hΦ₂ : ∀ x y b, |Φ₂ x y b| ≤ c₂)
    (hK : ∀ x y a b, K (Function.update x i a) (Function.update y j b) =
      (χ (b - a) : ℝ) * Φ₁ x y a * Φ₂ x y b)
    (g f : (Fin 3 → F) → ℝ) :
    |∑ x, ∑ y, g x * K x y * f y| ≤
      c₁ * c₂ * (√qF * qF ^ 2) * (√(∑ x, g x ^ 2) * √(∑ y, f y ^ 2)) := by
  have hq : (0 : ℝ) < qF := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  have hc₁ : 0 ≤ c₁ := (abs_nonneg _).trans (hΦ₁ 0 0 0)
  have hc₂ : 0 ≤ c₂ := (abs_nonneg _).trans (hΦ₂ 0 0 0)
  -- spread the two coordinates
  set S := ∑ x, ∑ y, g x * K x y * f y
  have hspread : qF ^ 2 * S = ∑ x, ∑ y, ∑ a, ∑ b,
      g (Function.update x i a) * K (Function.update x i a) (Function.update y j b) *
        f (Function.update y j b) := by
    have h1 : ∀ x', ∑ y, ∑ b, g x' * K x' (Function.update y j b) * f (Function.update y j b) =
        qF * ∑ y, g x' * K x' y * f y := fun x' =>
      sum_update j (fun y => g x' * K x' y * f y)
    have h2 := sum_update i (fun x' => ∑ y, g x' * K x' y * f y)
    have e : ∀ x, ∑ y, ∑ a, ∑ b, g (Function.update x i a) * K (Function.update x i a)
        (Function.update y j b) * f (Function.update y j b) =
        qF * ∑ a, ∑ y, g (Function.update x i a) * K (Function.update x i a) y * f y := by
      intro x
      rw [sum_comm, mul_sum]
      exact sum_congr rfl fun a _ => h1 _
    simp only [e, ← mul_sum]
    rw [h2]
    ring
  -- the inner Paley bound
  set A : (Fin 3 → F) → ℝ := fun x => ∑ a, g (Function.update x i a) ^ 2
  set B : (Fin 3 → F) → ℝ := fun y => ∑ b, f (Function.update y j b) ^ 2
  have hA0 : ∀ x, 0 ≤ A x := fun x => sum_nonneg fun a _ => sq_nonneg _
  have hB0 : ∀ y, 0 ≤ B y := fun y => sum_nonneg fun a _ => sq_nonneg _
  have hinner : ∀ x y, |∑ a, ∑ b, g (Function.update x i a) * K (Function.update x i a)
      (Function.update y j b) * f (Function.update y j b)| ≤
      c₁ * c₂ * √qF * (√(A x) * √(B y)) := by
    intro x y
    have e : ∑ a, ∑ b, g (Function.update x i a) * K (Function.update x i a)
        (Function.update y j b) * f (Function.update y j b) =
        ∑ a, ∑ b, (g (Function.update x i a) * Φ₁ x y a) * (χ (b - a) : ℝ) *
          (Φ₂ x y b * f (Function.update y j b)) := by
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [hK]; ring
    rw [e]
    refine (paley_form hR h3 _ _).trans ?_
    have hG : √(∑ a, (g (Function.update x i a) * Φ₁ x y a) ^ 2) ≤ c₁ * √(A x) := by
      rw [← Real.sqrt_sq hc₁, ← Real.sqrt_mul (sq_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      rw [mul_sum]
      refine sum_le_sum fun a _ => ?_
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp (hΦ₁ x y a)).1
        (abs_le.mp (hΦ₁ x y a)).2) (sq_nonneg _)
    have hH : √(∑ b, (Φ₂ x y b * f (Function.update y j b)) ^ 2) ≤ c₂ * √(B y) := by
      rw [← Real.sqrt_sq hc₂, ← Real.sqrt_mul (sq_nonneg _)]
      refine Real.sqrt_le_sqrt ?_
      rw [mul_sum]
      refine sum_le_sum fun b _ => ?_
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp (hΦ₂ x y b)).1
        (abs_le.mp (hΦ₂ x y b)).2) (sq_nonneg _)
    have := mul_le_mul hG hH (Real.sqrt_nonneg _) (mul_nonneg hc₁ (Real.sqrt_nonneg _))
    calc √qF * (√(∑ a, (g (Function.update x i a) * Φ₁ x y a) ^ 2) *
          √(∑ b, (Φ₂ x y b * f (Function.update y j b)) ^ 2))
        ≤ √qF * (c₁ * √(A x) * (c₂ * √(B y))) :=
          mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = c₁ * c₂ * √qF * (√(A x) * √(B y)) := by ring
  -- the outer Cauchy–Schwarz
  have hcard : (Fintype.card (Fin 3 → F) : ℝ) = qF ^ 3 := by
    rw [Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  have hAs : ∑ x, √(A x) ≤ qF ^ 2 * √(∑ x, g x ^ 2) := by
    refine (sum_sqrt_le A hA0).trans ?_
    rw [hcard]
    have : ∑ x, A x = qF * ∑ x, g x ^ 2 := sum_update i (fun x => g x ^ 2)
    rw [this, ← Real.sqrt_mul (by positivity), ← mul_assoc, ← pow_succ,
      Real.sqrt_mul (by positivity), show (3 + 1 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sqrt_sq (by positivity)]
  have hBs : ∑ y, √(B y) ≤ qF ^ 2 * √(∑ y, f y ^ 2) := by
    refine (sum_sqrt_le B hB0).trans ?_
    rw [hcard]
    have : ∑ y, B y = qF * ∑ y, f y ^ 2 := sum_update j (fun y => f y ^ 2)
    rw [this, ← Real.sqrt_mul (by positivity), ← mul_assoc, ← pow_succ,
      Real.sqrt_mul (by positivity), show (3 + 1 : ℕ) = 2 * 2 by norm_num, pow_mul,
      Real.sqrt_sq (by positivity)]
  have hsum : |qF ^ 2 * S| ≤ c₁ * c₂ * √qF * ((∑ x, √(A x)) * ∑ y, √(B y)) := by
    rw [hspread, sum_mul_sum, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun y _ => ?_)
    exact hinner x y
  have hk : 0 ≤ c₁ * c₂ * √qF := by positivity
  have hfin : |qF ^ 2 * S| ≤ qF ^ 2 * (c₁ * c₂ * (√qF * qF ^ 2) *
      (√(∑ x, g x ^ 2) * √(∑ y, f y ^ 2))) := by
    refine hsum.trans ?_
    have := mul_le_mul hAs hBs (sum_nonneg fun y _ => Real.sqrt_nonneg _) (by positivity)
    calc c₁ * c₂ * √qF * ((∑ x, √(A x)) * ∑ y, √(B y))
        ≤ c₁ * c₂ * √qF * (qF ^ 2 * √(∑ x, g x ^ 2) * (qF ^ 2 * √(∑ y, f y ^ 2))) :=
          mul_le_mul_of_nonneg_left this hk
      _ = _ := by ring
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < qF ^ 2)] at hfin
  exact le_of_mul_le_mul_left hfin (by positivity)

omit [Field F] [Fintype F] [DecidableEq F] in
/-- **The Schur test**: if every row and column sum of `|K|` is at most `R`, then
`|∑ g K f| ≤ R ‖g‖ ‖f‖`. -/
theorem schur_bound {α : Type} [Fintype α] (K : α → α → ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hrow : ∀ x, ∑ y, |K x y| ≤ R) (hcol : ∀ y, ∑ x, |K x y| ≤ R) (g f : α → ℝ) :
    |∑ x, ∑ y, g x * K x y * f y| ≤ R * (√(∑ x, g x ^ 2) * √(∑ y, f y ^ 2)) := by
  set u : α × α → ℝ := fun z => |g z.1| * √|K z.1 z.2|
  set v : α × α → ℝ := fun z => √|K z.1 z.2| * |f z.2|
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ u v
  have huv : ∑ z, u z * v z = ∑ x, ∑ y, |g x| * |K x y| * |f y| := by
    rw [← Fintype.sum_prod_type']
    refine sum_congr rfl fun z _ => ?_
    simp only [u, v]
    have := Real.mul_self_sqrt (abs_nonneg (K z.1 z.2))
    calc |g z.1| * √|K z.1 z.2| * (√|K z.1 z.2| * |f z.2|)
        = |g z.1| * (√|K z.1 z.2| * √|K z.1 z.2|) * |f z.2| := by ring
      _ = _ := by rw [this]
  have hu : ∑ z, u z ^ 2 ≤ R * ∑ x, g x ^ 2 := by
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_le_sum fun x _ => ?_
    have e : ∑ y, u (x, y) ^ 2 = g x ^ 2 * ∑ y, |K x y| := by
      rw [mul_sum]
      refine sum_congr rfl fun y _ => ?_
      simp only [u, mul_pow, sq_abs, Real.sq_sqrt (abs_nonneg _)]
    rw [e, mul_comm R]
    exact mul_le_mul_of_nonneg_left (hrow x) (sq_nonneg _)
  have hv : ∑ z, v z ^ 2 ≤ R * ∑ y, f y ^ 2 := by
    rw [Fintype.sum_prod_type, sum_comm, mul_sum]
    refine sum_le_sum fun y _ => ?_
    have e : ∑ x, v (x, y) ^ 2 = f y ^ 2 * ∑ x, |K x y| := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      simp only [v, mul_pow, sq_abs, Real.sq_sqrt (abs_nonneg _)]
      ring
    rw [e, mul_comm R]
    exact mul_le_mul_of_nonneg_left (hcol y) (sq_nonneg _)
  have hg0 : 0 ≤ ∑ x, g x ^ 2 := sum_nonneg fun x _ => sq_nonneg _
  have hf0 : 0 ≤ ∑ y, f y ^ 2 := sum_nonneg fun x _ => sq_nonneg _
  have habs : |∑ x, ∑ y, g x * K x y * f y| ≤ ∑ z, u z * v z := by
    rw [huv]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun y _ => ?_))
    rw [abs_mul, abs_mul]
  have hsq : (∑ z, u z * v z) ^ 2 ≤ (R * (√(∑ x, g x ^ 2) * √(∑ y, f y ^ 2))) ^ 2 := by
    refine hcs.trans ?_
    rw [mul_pow, mul_pow, Real.sq_sqrt hg0, Real.sq_sqrt hf0]
    have := mul_le_mul hu hv (sum_nonneg fun z _ => sq_nonneg _) (by positivity)
    linarith
  have h0 : 0 ≤ ∑ z, u z * v z := habs.trans' (abs_nonneg _)
  exact habs.trans (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero |>.mp hsq)

end Sarkozy.SignedDecomp
