module

public import Sarkozy.DLK.Normalized
public import Mathlib.Algebra.Order.Chebyshev

/-!
# `cor:dl:normalized` for all `a, b ≥ 2`, from `thm:dl:K`

`paper/sections/15_second_order.tex`, `cor:dl:normalized`, with real functions. For `a = n + 2`,
`b = m + 2`, signs `ς_{ij} = ±1` and
`K(x, y) = ∏_{i < a, j < b} χ(ς_{ij}(y_j - x_i))` (`rectKernel`, `x ∈ 𝔽_p^a`, `y ∈ 𝔽_p^b`):

* `slice_bilinear`: the slicing step of the paper's proof, on product spaces. If `K₂` on `𝔽_p²`
  satisfies `|∑ F K₂ H| ≤ Λ ‖F‖ ‖H‖` for `F`, `H` vanishing on the diagonal, and
  `K((x, x'), (y, y')) = K₂(x, y) α(x, y') β(y, x') c(x', y')` with `|α|, |β|, |c| ≤ 1`, then
  `|∑ f K h| ≤ Λ √|X'| √|Y'| ‖f‖ ‖h‖` for `f`, `h` vanishing where `x₁ = x₂`, resp. `y₁ = y₂`
  (fix `x'`, `y'`; the case `a = b = 2` bounds the inner sum; Cauchy–Schwarz in `x'` and `y'`).
* `rectKernel_split`: the factorization of `K` along `(x₀, x₁ | x₂, …)` and `(y₀, y₁ | y₂, …)`.
* `normalized`: **`eq:dl:normalized`, `cor:dl:normalized`(a)** for all `a, b ≥ 2`: for uniform
  probability, `f` vanishing where `x₀ = x₁` and `h` where `y₀ = y₁`,
  `|E_{x,y} f(x) K(x, y) h(y)| ≤ (2/p) ‖f‖₂ ‖h‖₂`.
* `normalized_density`: **`cor:dl:normalized`(b)** for all `a, b ≥ 2`, with weights
  `ν₁ ≥ 0` on `𝔽_p^a` vanishing where `x₀ = x₁`, density `p^a ν₁ ≤ D₁`, and likewise `ν₂`:
  `|E_{x∼ν₁, y∼ν₂} f K h| ≤ (2/p) √(D₁ D₂) ‖f‖_{ν₁} ‖h‖_{ν₂}`.

(The paper's coordinates are `x₁, x₂, …`; here they are `x 0, x 1, …`.)
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DLK

open Sarkozy Sarkozy.Influence Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

theorem abs_chiR_le_one (t : ZMod p) : |chiR t| ≤ 1 := by
  unfold chiR
  rcases quadraticChar_isQuadratic (ZMod p) t with h | h | h <;> rw [h] <;> norm_num

theorem sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  have e : x ^ n = (Real.sqrt x ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]
  rw [e, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) n)]

theorem abs_mul_chiR_le_one (s t : ZMod p) : |chiR s * chiR t| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul (abs_chiR_le_one s) (abs_chiR_le_one t) (abs_nonneg _) zero_le_one).trans
    (by norm_num)

theorem abs_prod_chiR_le_one {ι : Type*} (s : Finset ι) (g : ι → ZMod p) :
    |∏ i ∈ s, chiR (g i)| ≤ 1 := by
  rw [abs_prod]
  exact prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_chiR_le_one _)

/-! ## The slicing step -/

/-- `∑_{x'} (∑_x f(x, x')²)^{1/2} ≤ √|X'| (∑_{x', x} f(x, x')²)^{1/2}` (Cauchy–Schwarz). -/
theorem sum_sqrt_le {X X' : Type*} [Fintype X] [Fintype X'] (f : X → X' → ℝ) :
    ∑ x', Real.sqrt (∑ x, f x x' ^ 2) ≤
      Real.sqrt (Fintype.card X') * Real.sqrt (∑ x', ∑ x, f x x' ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset X'))
    (f := fun x' => Real.sqrt (∑ x, f x x' ^ 2))
  have e : ∑ x', Real.sqrt (∑ x, f x x' ^ 2) ^ 2 = ∑ x', ∑ x, f x x' ^ 2 :=
    sum_congr rfl fun x' _ => Real.sq_sqrt (sum_nonneg fun x _ => sq_nonneg _)
  rw [e, card_univ] at h
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le h

/-- **The slicing step of `cor:dl:normalized`(a)**, on product spaces: if `K₂` satisfies
`|∑ F K₂ H| ≤ Λ ‖F‖ ‖H‖` for `F`, `H` on `𝔽_p²` vanishing on the diagonal, then the kernel
`K₂(x, y) α(x, y') β(y, x') c(x', y')` with `|α|, |β|, |c| ≤ 1` satisfies
`|∑ f K h| ≤ Λ √|X'| √|Y'| ‖f‖ ‖h‖` for `f(x, x')`, `h(y, y')` vanishing where `x`, resp. `y`, is
diagonal. -/
theorem slice_bilinear {X' Y' : Type*} [Fintype X'] [Fintype Y']
    (K₂ : ZMod p × ZMod p → ZMod p × ZMod p → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hK₂ : ∀ F H : ZMod p × ZMod p → ℝ, (∀ x : ZMod p × ZMod p, x.1 = x.2 → F x = 0) →
      (∀ y : ZMod p × ZMod p, y.1 = y.2 → H y = 0) →
      |∑ x, ∑ y, F x * K₂ x y * H y| ≤ Λ * Real.sqrt (∑ x, F x ^ 2) * Real.sqrt (∑ y, H y ^ 2))
    (α : ZMod p × ZMod p → Y' → ℝ) (β : ZMod p × ZMod p → X' → ℝ) (c : X' → Y' → ℝ)
    (hα : ∀ x y', |α x y'| ≤ 1) (hβ : ∀ y x', |β y x'| ≤ 1) (hc : ∀ x' y', |c x' y'| ≤ 1)
    (f : ZMod p × ZMod p → X' → ℝ) (h : ZMod p × ZMod p → Y' → ℝ)
    (hf : ∀ (x : ZMod p × ZMod p) x', x.1 = x.2 → f x x' = 0)
    (hh : ∀ (y : ZMod p × ZMod p) y', y.1 = y.2 → h y y' = 0) :
    |∑ x', ∑ y', ∑ x, ∑ y, f x x' * (K₂ x y * α x y' * β y x' * c x' y') * h y y'| ≤
      Λ * Real.sqrt (Fintype.card X') * Real.sqrt (Fintype.card Y') *
        Real.sqrt (∑ x', ∑ x, f x x' ^ 2) * Real.sqrt (∑ y', ∑ y, h y y' ^ 2) := by
  -- the bound of one slice
  have hslice : ∀ x' y', |∑ x, ∑ y, f x x' * (K₂ x y * α x y' * β y x' * c x' y') * h y y'| ≤
      Λ * Real.sqrt (∑ x, f x x' ^ 2) * Real.sqrt (∑ y, h y y' ^ 2) := by
    intro x' y'
    have e : ∑ x, ∑ y, f x x' * (K₂ x y * α x y' * β y x' * c x' y') * h y y' =
        c x' y' * ∑ x, ∑ y, (f x x' * α x y') * K₂ x y * (β y x' * h y y') := by
      rw [mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun y _ => by ring
    rw [e, abs_mul]
    have hb := hK₂ (fun x => f x x' * α x y') (fun y => β y x' * h y y')
      (fun x hx => by simp [hf x x' hx]) (fun y hy => by simp [hh y y' hy])
    have s1 : Real.sqrt (∑ x, (f x x' * α x y') ^ 2) ≤ Real.sqrt (∑ x, f x x' ^ 2) := by
      refine Real.sqrt_le_sqrt (sum_le_sum fun x _ => ?_)
      rw [mul_pow]
      have : α x y' ^ 2 ≤ 1 := by
        have := hα x y'
        rw [← sq_abs]; nlinarith [abs_nonneg (α x y')]
      nlinarith [sq_nonneg (f x x')]
    have s2 : Real.sqrt (∑ y, (β y x' * h y y') ^ 2) ≤ Real.sqrt (∑ y, h y y' ^ 2) := by
      refine Real.sqrt_le_sqrt (sum_le_sum fun y _ => ?_)
      rw [mul_pow]
      have : β y x' ^ 2 ≤ 1 := by
        have := hβ y x'
        rw [← sq_abs]; nlinarith [abs_nonneg (β y x')]
      nlinarith [sq_nonneg (h y y')]
    calc |c x' y'| * |∑ x, ∑ y, (f x x' * α x y') * K₂ x y * (β y x' * h y y')|
        ≤ 1 * (Λ * Real.sqrt (∑ x, (f x x' * α x y') ^ 2) *
            Real.sqrt (∑ y, (β y x' * h y y') ^ 2)) :=
          mul_le_mul (hc x' y') hb (abs_nonneg _) zero_le_one
      _ ≤ Λ * Real.sqrt (∑ x, f x x' ^ 2) * Real.sqrt (∑ y, h y y' ^ 2) := by
          rw [one_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left s1 hΛ) s2 (Real.sqrt_nonneg _)
            (mul_nonneg hΛ (Real.sqrt_nonneg _))
  calc |∑ x', ∑ y', ∑ x, ∑ y, f x x' * (K₂ x y * α x y' * β y x' * c x' y') * h y y'|
      ≤ ∑ x', ∑ y', |∑ x, ∑ y, f x x' * (K₂ x y * α x y' * β y x' * c x' y') * h y y'| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x' _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x', ∑ y', Λ * Real.sqrt (∑ x, f x x' ^ 2) * Real.sqrt (∑ y, h y y' ^ 2) :=
        sum_le_sum fun x' _ => sum_le_sum fun y' _ => hslice x' y'
    _ = Λ * (∑ x', Real.sqrt (∑ x, f x x' ^ 2)) * (∑ y', Real.sqrt (∑ y, h y y' ^ 2)) := by
        rw [mul_assoc, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun x' _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun y' _ => by ring
    _ ≤ Λ * (Real.sqrt (Fintype.card X') * Real.sqrt (∑ x', ∑ x, f x x' ^ 2)) *
          (Real.sqrt (Fintype.card Y') * Real.sqrt (∑ y', ∑ y, h y y' ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (sum_sqrt_le f) hΛ) (sum_sqrt_le h)
          (sum_nonneg fun _ _ => Real.sqrt_nonneg _) (mul_nonneg hΛ (by positivity))
    _ = _ := by ring

/-! ## The kernel `K` on `𝔽_p^a × 𝔽_p^b` -/

/-- `K(x, y) = ∏_{i < a, j < b} χ(ς_{ij}(y_j - x_i))` for `x ∈ 𝔽_p^a`, `y ∈ 𝔽_p^b`. -/
noncomputable def rectKernel {a b : ℕ} (ς : Fin a → Fin b → ZMod p) (x : Fin a → ZMod p)
    (y : Fin b → ZMod p) : ℝ :=
  ∏ i, ∏ j, chiR (ς i j * (y j - x i))

/-- Splitting off the first two coordinates: `x ↦ ((x₀, x₁), (x₂, …))`. -/
def splitTwo (n : ℕ) : (Fin (n + 2) → ZMod p) ≃ (ZMod p × ZMod p) × (Fin n → ZMod p) where
  toFun x := ((x 0, x 1), fun i => x i.succ.succ)
  invFun z := Fin.cons z.1.1 (Fin.cons z.1.2 z.2)
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨a, b⟩, w⟩
    rfl

omit [Fact p.Prime] in
theorem splitTwo_symm_apply (n : ℕ) (z : (ZMod p × ZMod p) × (Fin n → ZMod p)) :
    (splitTwo n).symm z = Fin.cons z.1.1 (Fin.cons z.1.2 z.2) := rfl

/-- The factorization of `K` along `(x₀, x₁ | x₂, …)` and `(y₀, y₁ | y₂, …)`:
`K = K₂(x, y) α(x, y') β(y, x') c(x', y')`, with `K₂` the rectangle kernel of the signs
`ς_{ij}`, `i, j ≤ 1`. -/
theorem rectKernel_split {n m : ℕ} (ς : Fin (n + 2) → Fin (m + 2) → ZMod p)
    (x : ZMod p × ZMod p) (x' : Fin n → ZMod p) (y : ZMod p × ZMod p) (y' : Fin m → ZMod p) :
    rectKernel ς ((splitTwo n).symm (x, x')) ((splitTwo m).symm (y, y')) =
      twoCycleRectangle (fun a b => ς (![0, 1] a) (![0, 1] b)) x y *
        (∏ j : Fin m, (chiR (ς 0 j.succ.succ * (y' j - x.1)) *
          chiR (ς 1 j.succ.succ * (y' j - x.2)))) *
        (∏ i : Fin n, (chiR (ς i.succ.succ 0 * (y.1 - x' i)) *
          chiR (ς i.succ.succ 1 * (y.2 - x' i)))) *
        (∏ i : Fin n, ∏ j : Fin m, chiR (ς i.succ.succ j.succ.succ * (y' j - x' i))) := by
  unfold rectKernel twoCycleRectangle
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [splitTwo_symm_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    prod_mul_distrib, Fin.succ_zero_eq_one]
  ring

theorem normalized_counting (hDLK : Target.FourCycle) (hp2 : p ≠ 2) {n m : ℕ}
    {ς : Fin (n + 2) → Fin (m + 2) → ZMod p} (hς : ∀ i j, ς i j = 1 ∨ ς i j = -1)
    (f : (Fin (n + 2) → ZMod p) → ℝ) (h : (Fin (m + 2) → ZMod p) → ℝ)
    (hf : ∀ x, x 0 = x 1 → f x = 0) (hh : ∀ y, y 0 = y 1 → h y = 0) :
    |∑ x, ∑ y, f x * rectKernel ς x y * h y| ≤
      2 * (p : ℝ) * Real.sqrt p ^ n * Real.sqrt p ^ m * Real.sqrt (∑ x, f x ^ 2) *
        Real.sqrt (∑ y, h y ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set F : ZMod p × ZMod p → (Fin n → ZMod p) → ℝ := fun x x' => f ((splitTwo n).symm (x, x'))
  set H : ZMod p × ZMod p → (Fin m → ZMod p) → ℝ := fun y y' => h ((splitTwo m).symm (y, y'))
  have hK := slice_bilinear (p := p) (X' := Fin n → ZMod p) (Y' := Fin m → ZMod p)
    (twoCycleRectangle (fun a b => ς (![0, 1] a) (![0, 1] b))) (Λ := 2 * (p : ℝ))
    (by positivity) (fun F H hF hH => rectangle_bilinear hDLK hp2 (fun a b => hς _ _) F H hF hH)
    (fun x y' => ∏ j : Fin m, (chiR (ς 0 j.succ.succ * (y' j - x.1)) *
          chiR (ς 1 j.succ.succ * (y' j - x.2))))
    (fun y x' => ∏ i : Fin n, (chiR (ς i.succ.succ 0 * (y.1 - x' i)) *
          chiR (ς i.succ.succ 1 * (y.2 - x' i))))
    (fun x' y' => ∏ i : Fin n, ∏ j : Fin m, chiR (ς i.succ.succ j.succ.succ * (y' j - x' i)))
    (fun x y' => by
      rw [abs_prod]
      exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun j _ => abs_mul_chiR_le_one _ _)
    (fun y x' => by
      rw [abs_prod]
      exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_mul_chiR_le_one _ _)
    (fun x' y' => by
      rw [abs_prod]
      exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => abs_prod_chiR_le_one _ _)
    F H (fun x x' hx => hf _ (by simpa [splitTwo_symm_apply] using hx))
    (fun y y' hy => hh _ (by simpa [splitTwo_symm_apply] using hy))
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, sqrt_pow_eq hp0.le]
    at hK
  -- reindex the sums along `splitTwo`
  have eF : ∑ x, f x ^ 2 = ∑ x', ∑ x, F x x' ^ 2 := by
    rw [← (splitTwo n).symm.sum_comp, Fintype.sum_prod_type, sum_comm]
  have eH : ∑ y, h y ^ 2 = ∑ y', ∑ y, H y y' ^ 2 := by
    rw [← (splitTwo m).symm.sum_comp, Fintype.sum_prod_type, sum_comm]
  have eS : ∑ x, ∑ y, f x * rectKernel ς x y * h y =
      ∑ x', ∑ y', ∑ x, ∑ y, F x x' * (twoCycleRectangle (fun a b => ς (![0, 1] a) (![0, 1] b)) x y *
        (∏ j : Fin m, (chiR (ς 0 j.succ.succ * (y' j - x.1)) *
          chiR (ς 1 j.succ.succ * (y' j - x.2)))) *
        (∏ i : Fin n, (chiR (ς i.succ.succ 0 * (y.1 - x' i)) *
          chiR (ς i.succ.succ 1 * (y.2 - x' i)))) *
        (∏ i : Fin n, ∏ j : Fin m, chiR (ς i.succ.succ j.succ.succ * (y' j - x' i)))) *
        H y y' := by
    rw [← (splitTwo n).symm.sum_comp, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun x' _ => ?_
    have e1 : ∀ x : ZMod p × ZMod p, ∑ y, f ((splitTwo n).symm (x, x')) *
        rectKernel ς ((splitTwo n).symm (x, x')) y * h y =
        ∑ y', ∑ y, F x x' * (twoCycleRectangle (fun a b => ς (![0, 1] a) (![0, 1] b)) x y *
          (∏ j : Fin m, (chiR (ς 0 j.succ.succ * (y' j - x.1)) *
            chiR (ς 1 j.succ.succ * (y' j - x.2)))) *
          (∏ i : Fin n, (chiR (ς i.succ.succ 0 * (y.1 - x' i)) *
            chiR (ς i.succ.succ 1 * (y.2 - x' i)))) *
          (∏ i : Fin n, ∏ j : Fin m, chiR (ς i.succ.succ j.succ.succ * (y' j - x' i)))) *
          H y y' := by
      intro x
      rw [← (splitTwo m).symm.sum_comp, Fintype.sum_prod_type, sum_comm]
      refine sum_congr rfl fun y' _ => sum_congr rfl fun y _ => ?_
      rw [rectKernel_split]
    rw [sum_congr rfl fun x _ => e1 x, sum_comm]
  rw [eS, eF, eH]
  calc _ ≤ 2 * (p : ℝ) * Real.sqrt p ^ n * Real.sqrt p ^ m * Real.sqrt (∑ x', ∑ x, F x x' ^ 2) *
        Real.sqrt (∑ y', ∑ y, H y y' ^ 2) := hK

/-- **`eq:dl:normalized`, `cor:dl:normalized`(a)** for all `a = n + 2 ≥ 2`, `b = m + 2 ≥ 2`, from
`thm:dl:K`: for signs `ς_{ij} = ±1`, `f` on `𝔽_p^a` vanishing where `x₀ = x₁` and `h` on `𝔽_p^b`
vanishing where `y₀ = y₁`, with uniform probability on `𝔽_p^a`, `𝔽_p^b`,
`|E_{x,y} f(x) K(x, y) h(y)| ≤ (2/p) ‖f‖₂ ‖h‖₂`. -/
theorem normalized (hDLK : Target.FourCycle) (hp2 : p ≠ 2) {n m : ℕ}
    {ς : Fin (n + 2) → Fin (m + 2) → ZMod p} (hς : ∀ i j, ς i j = 1 ∨ ς i j = -1)
    (f : (Fin (n + 2) → ZMod p) → ℝ) (h : (Fin (m + 2) → ZMod p) → ℝ)
    (hf : ∀ x, x 0 = x 1 → f x = 0) (hh : ∀ y, y 0 = y 1 → h y = 0) :
    |(1 / (p : ℝ) ^ (n + 2) * (1 / (p : ℝ) ^ (m + 2))) * ∑ x, ∑ y, f x * rectKernel ς x y * h y| ≤
      (2 / p) * Real.sqrt ((1 / (p : ℝ) ^ (n + 2)) * ∑ x, f x ^ 2) *
        Real.sqrt ((1 / (p : ℝ) ^ (m + 2)) * ∑ y, h y ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hb := normalized_counting hDLK hp2 hς f h hf hh
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs : ∀ (k : ℕ) (S : ℝ), Real.sqrt ((1 / (p : ℝ) ^ k) * S) =
      (1 / Real.sqrt p ^ k) * Real.sqrt S := by
    intro k S
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ (by positivity), Real.sqrt_one,
      sqrt_pow_eq hp0.le]
  rw [hs, hs, abs_mul, abs_of_pos (by positivity)]
  have alg : ∀ s : ℝ, 0 < s → ∀ A B : ℝ, 1 / (s ^ 2) ^ (n + 2) * (1 / (s ^ 2) ^ (m + 2)) *
      (2 * s ^ 2 * s ^ n * s ^ m * A * B) =
      2 / s ^ 2 * (1 / s ^ (n + 2) * A) * (1 / s ^ (m + 2) * B) := by
    intro s hs A B
    field_simp
    ring
  calc 1 / (p : ℝ) ^ (n + 2) * (1 / (p : ℝ) ^ (m + 2)) * |∑ x, ∑ y, f x * rectKernel ς x y * h y|
      ≤ 1 / (p : ℝ) ^ (n + 2) * (1 / (p : ℝ) ^ (m + 2)) *
          (2 * (p : ℝ) * Real.sqrt p ^ n * Real.sqrt p ^ m * Real.sqrt (∑ x, f x ^ 2) *
            Real.sqrt (∑ y, h y ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 / p * (1 / Real.sqrt p ^ (n + 2) * Real.sqrt (∑ x, f x ^ 2)) *
          (1 / Real.sqrt p ^ (m + 2) * Real.sqrt (∑ y, h y ^ 2)) := by
        have := alg (Real.sqrt p) hs0 (Real.sqrt (∑ x, f x ^ 2)) (Real.sqrt (∑ y, h y ^ 2))
        rw [hsq] at this
        rw [← this]

/-- **`cor:dl:normalized`(b)** for all `a = n + 2`, `b = m + 2`, from `thm:dl:K`: let
`ν₁ ≥ 0` on `𝔽_p^a` vanish where `x₀ = x₁`, with density relative to uniform probability at most
`D₁` (`p^a ν₁ ≤ D₁`), and likewise `ν₂` on `𝔽_p^b` with `D₂`. Then
`|∑_{x,y} ν₁(x) f(x) K(x, y) ν₂(y) h(y)| ≤ (2/p) √(D₁ D₂) (∑ ν₁ f²)^{1/2} (∑ ν₂ h²)^{1/2}`,
i.e. `|E_{x∼ν₁, y∼ν₂} f K h| ≤ (2/p) √(D₁D₂) ‖f‖_{ν₁} ‖h‖_{ν₂}`. The mass of `ν_i` is not used. -/
theorem normalized_density (hDLK : Target.FourCycle) (hp2 : p ≠ 2) {n m : ℕ}
    {ς : Fin (n + 2) → Fin (m + 2) → ZMod p} (hς : ∀ i j, ς i j = 1 ∨ ς i j = -1)
    (ν₁ : (Fin (n + 2) → ZMod p) → ℝ) (ν₂ : (Fin (m + 2) → ZMod p) → ℝ)
    (hν₁ : ∀ x, 0 ≤ ν₁ x) (hν₂ : ∀ y, 0 ≤ ν₂ y)
    (hd₁ : ∀ x, x 0 = x 1 → ν₁ x = 0) (hd₂ : ∀ y, y 0 = y 1 → ν₂ y = 0) {D₁ D₂ : ℝ}
    (hD₁ : ∀ x, (p : ℝ) ^ (n + 2) * ν₁ x ≤ D₁) (hD₂ : ∀ y, (p : ℝ) ^ (m + 2) * ν₂ y ≤ D₂)
    (f : (Fin (n + 2) → ZMod p) → ℝ) (h : (Fin (m + 2) → ZMod p) → ℝ) :
    |∑ x, ∑ y, ν₁ x * f x * rectKernel ς x y * (ν₂ y * h y)| ≤
      (2 / p) * Real.sqrt (D₁ * D₂) * Real.sqrt (∑ x, ν₁ x * f x ^ 2) *
        Real.sqrt (∑ y, ν₂ y * h y ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hb := normalized_counting hDLK hp2 hς (fun x => ν₁ x * f x) (fun y => ν₂ y * h y)
    (fun x hx => by simp [hd₁ x hx]) (fun y hy => by simp [hd₂ y hy])
  have hsq : ∀ {X : Type} [Fintype X] (ν : X → ℝ) (k : ℕ) (D : ℝ) (g : X → ℝ), (∀ x, 0 ≤ ν x) →
      (∀ x, (p : ℝ) ^ k * ν x ≤ D) →
      ∑ x, (ν x * g x) ^ 2 ≤ (D / (p : ℝ) ^ k) * ∑ x, ν x * g x ^ 2 := by
    intro X _ ν k D g hν hD
    rw [mul_sum]
    refine sum_le_sum fun x _ => ?_
    have h1 : ν x ≤ D / (p : ℝ) ^ k := by
      rw [le_div_iff₀ (by positivity)]; linarith [hD x]
    have h2 : 0 ≤ ν x * g x ^ 2 := mul_nonneg (hν x) (sq_nonneg _)
    calc (ν x * g x) ^ 2 = ν x * (ν x * g x ^ 2) := by ring
      _ ≤ D / (p : ℝ) ^ k * (ν x * g x ^ 2) := mul_le_mul_of_nonneg_right h1 h2
  have hD₁0 : 0 ≤ D₁ := by
    have := hD₁ 0; have := hν₁ 0; have : (0 : ℝ) ≤ (p : ℝ) ^ (n + 2) := by positivity
    nlinarith
  have hD₂0 : 0 ≤ D₂ := by
    have := hD₂ 0; have := hν₂ 0; have : (0 : ℝ) ≤ (p : ℝ) ^ (m + 2) := by positivity
    nlinarith
  have s1 := Real.sqrt_le_sqrt (hsq ν₁ (n + 2) D₁ f hν₁ hD₁)
  have s2 := Real.sqrt_le_sqrt (hsq ν₂ (m + 2) D₂ h hν₂ hD₂)
  have e : ∀ (k : ℕ) (D S : ℝ), 0 ≤ D → 0 ≤ S →
      Real.sqrt (D / (p : ℝ) ^ k * S) = (1 / Real.sqrt p ^ k) * Real.sqrt D * Real.sqrt S := by
    intro k D S hD hS
    rw [Real.sqrt_mul (div_nonneg hD (by positivity)), Real.sqrt_div' _ (by positivity),
      sqrt_pow_eq hp0.le]
    ring
  rw [e (n + 2) D₁ _ hD₁0 (sum_nonneg fun x _ => mul_nonneg (hν₁ x) (sq_nonneg _))] at s1
  rw [e (m + 2) D₂ _ hD₂0 (sum_nonneg fun x _ => mul_nonneg (hν₂ x) (sq_nonneg _))] at s2
  have e2 : ∑ x, ∑ y, ν₁ x * f x * rectKernel ς x y * (ν₂ y * h y) =
      ∑ x, ∑ y, (ν₁ x * f x) * rectKernel ς x y * (ν₂ y * h y) := rfl
  rw [e2]
  refine hb.trans ?_
  rw [Real.sqrt_mul hD₁0]
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hB : 0 ≤ Real.sqrt (∑ y, (ν₂ y * h y) ^ 2) := Real.sqrt_nonneg _
  have hc : 0 ≤ 2 * (p : ℝ) * Real.sqrt p ^ n * Real.sqrt p ^ m := by positivity
  calc 2 * (p : ℝ) * Real.sqrt p ^ n * Real.sqrt p ^ m * Real.sqrt (∑ x, (ν₁ x * f x) ^ 2) *
        Real.sqrt (∑ y, (ν₂ y * h y) ^ 2)
      ≤ 2 * (p : ℝ) * Real.sqrt p ^ n * Real.sqrt p ^ m *
          ((1 / Real.sqrt p ^ (n + 2)) * Real.sqrt D₁ * Real.sqrt (∑ x, ν₁ x * f x ^ 2)) *
          ((1 / Real.sqrt p ^ (m + 2)) * Real.sqrt D₂ * Real.sqrt (∑ y, ν₂ y * h y ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left s1 hc) s2 hB (by positivity)
    _ = 2 / p * (Real.sqrt D₁ * Real.sqrt D₂) * Real.sqrt (∑ x, ν₁ x * f x ^ 2) *
          Real.sqrt (∑ y, ν₂ y * h y ^ 2) := by
        have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
        have alg : ∀ s : ℝ, 0 < s → ∀ A B C E : ℝ, 2 * s ^ 2 * s ^ n * s ^ m *
            (1 / s ^ (n + 2) * A * B) * (1 / s ^ (m + 2) * C * E) =
            2 / s ^ 2 * (A * C) * B * E := by
          intro s hs A B C E
          field_simp
          ring
        have := alg (Real.sqrt p) hs0 (Real.sqrt D₁) (Real.sqrt (∑ x, ν₁ x * f x ^ 2))
          (Real.sqrt D₂) (Real.sqrt (∑ y, ν₂ y * h y ^ 2))
        rw [hsq] at this
        exact this

end Sarkozy.DLK
