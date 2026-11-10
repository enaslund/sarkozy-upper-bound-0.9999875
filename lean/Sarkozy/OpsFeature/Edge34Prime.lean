module

public import Sarkozy.MiddleRecords.ActualFeatures
public import Sarkozy.Envelopes.FeatureCert

@[expose] public section

/-!
# The edge `34` at one prime (`lem:oct24:feature-block`(a), proof Step 4, the prime bound)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`, proof Step 4: fix `x₁ = y` at one
prime; the conditional maximal correlation of `x₀` and `x₂` given `x₁ = y` under the actual fold law
`m₀ ∝ oldW` is at most
`[√p/(p-4) + (p-5)/((p-3)(p-4)) + 4/(p-4)²]/(1 - 2/(p-4)) ≤ ϱ₃₄(p)`.

Here the statement is the bilinear form of that bound, for the unnormalized conditional weight
`W(u, w) = oldW(u, y, w)` with the conditional marginal weights `W₀(u) = ∑_w W(u, w)` and
`W₂(w) = ∑_u W(u, w)`: for `W₀`-centred `f` and `W₂`-centred `g`,
`|∑ W f g| ≤ ϱ₃₄(1/p, p^{-1/2}) √(∑ W₀ f²) √(∑ W₂ g²)` (**`edge34_prime`**).

**Proof (the paper's, with the centring made explicit).**
* `W₀(u) = (p - 3)(p - 4 + 2a(u))/4` and `W₂(w) = (p - 3)(p - 4 - 2a(w))/4` off `y`, with
  `a(t) = χ(t - y)`, and both vanish at `y` (`W0_eq`, `W2_eq`): the marginal densities
  `1 ± μ a` of the paper, `μ = 2/(p - 4)`.
* `4W(u, w) = (1 + χ(w - u))(p - 5 + a(u) - a(w)) - [u = w](p - 5)` off `y` (`four_oldW`). For
  functions `φ, ψ` vanishing at `y` and centred in the base (uniform) law of the other `p - 1`
  labels, this gives `4∑ W φ ψ = (p - 5)B(φ, ψ) + B(aφ, ψ) - B(φ, aψ) - (p - 5)⟨φ, ψ⟩`
  (`four_sum_centred`), with the Paley form `B(φ, ψ) = ∑ χ(w - u) φ(u) ψ(w)`.
* `B(φ, ψ)² ≤ p ‖φ‖² ‖ψ‖²` (`paleyForm_sq_le`: `∑_u (∑_w χ(w - u) ψ(w))² = p‖ψ‖² - (∑ψ)²`, the
  compressed Paley operator of `lem:square-shift`(c), on all labels).
* Re-centring (`f = φ + α` off `y`): `∑ W f g = ∑ W φ ψ - αβZ`, the covariance correction
  `μ²⟨χ, f⟩⟨χ, g⟩` of the paper, bounded by `(p - 3)/(p - 4) ‖φ‖ ‖ψ‖`.
* `W₀, W₂ ≥ (p - 3)(p - 6)/4` off `y` (the lower bounds `1 - μ` of the marginal densities), and
  centring lowers the base norm.

The constant obtained, `[(p-3)√p + (p-5) + 4(p-3)/(p-4)]/((p-3)(p-6))`, is the paper's, and it
is at most `ϱ₃₄(1/p, p^{-1/2}) = (√p + 1 + 4/(p-4))/(p-6)` (`kappa_le_rho34`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.MiddleRecords Sarkozy.TraceMixing Sarkozy.Envelopes

section Prime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-! ## The Paley form -/

/-- The Paley bilinear form `B(φ, ψ) = ∑_{u,w} χ(w - u) φ(u) ψ(w)`. -/
noncomputable def paleyForm (φ ψ : F → ℝ) : ℝ := ∑ u, ∑ w, (χ (w - u) : ℝ) * φ u * ψ w

theorem sum_chi_mul_chi_R (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (w w' : F) :
    ∑ u, (χ (w - u) : ℝ) * (χ (w' - u) : ℝ) = (if w = w' then qF else 0) - 1 := by
  have h := sum_chi_mul_chi hF w w'
  have e : ∀ u, (χ (w - u) : ℝ) * (χ (w' - u) : ℝ) = ((χ (u - w) * χ (u - w') : ℤ) : ℝ) := by
    intro u
    rw [chi_swap h3 w u, chi_swap h3 w' u]
    push_cast
    ring
  simp only [e]
  rw [← Int.cast_sum, h]
  split_ifs <;> push_cast <;> ring

theorem chi_sq_le_one (x : F) : (χ x : ℝ) ^ 2 ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  · rcases quadraticChar_dichotomy hx with h | h <;> rw [h] <;> norm_num

/-- **The compressed Paley bound**: `B(φ, ψ)² ≤ p ‖φ‖² ‖ψ‖²`. -/
theorem paleyForm_sq_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (φ ψ : F → ℝ) :
    paleyForm φ ψ ^ 2 ≤ qF * (∑ u, φ u ^ 2) * (∑ w, ψ w ^ 2) := by
  set Q : F → ℝ := fun u => ∑ w, (χ (w - u) : ℝ) * ψ w with hQ
  have e1 : paleyForm φ ψ = ∑ u, φ u * Q u := by
    unfold paleyForm
    refine sum_congr rfl fun u _ => ?_
    simp only [hQ, mul_sum]
    exact sum_congr rfl fun w _ => by ring
  have e2 : ∑ u, Q u ^ 2 = qF * ∑ w, ψ w ^ 2 - (∑ w, ψ w) ^ 2 := by
    have e3 : ∀ u, Q u ^ 2 =
        ∑ w, ∑ w', ψ w * ψ w' * ((χ (w - u) : ℝ) * (χ (w' - u) : ℝ)) := by
      intro u
      simp only [hQ, sq, sum_mul_sum]
      exact sum_congr rfl fun w _ => sum_congr rfl fun w' _ => by ring
    simp only [e3]
    rw [sum_comm]
    have e4 : ∀ w, ∑ u, ∑ w', ψ w * ψ w' * ((χ (w - u) : ℝ) * (χ (w' - u) : ℝ)) =
        ∑ w', ψ w * ψ w' * ((if w = w' then qF else 0) - 1) := by
      intro w
      rw [sum_comm]
      refine sum_congr rfl fun w' _ => ?_
      rw [← mul_sum, sum_chi_mul_chi_R hF h3]
    simp only [e4, mul_sub, mul_one, sum_sub_distrib, mul_ite, mul_zero, sum_ite_eq, mem_univ,
      ↓reduceIte]
    rw [sq, sum_mul_sum, mul_sum]
    congr 1
    exact sum_congr rfl fun w _ => by ring
  have hcs := sum_mul_sq_le_sq_mul_sq univ φ Q
  rw [e1]
  have hψ : 0 ≤ (∑ w, ψ w) ^ 2 := sq_nonneg _
  have hφ : 0 ≤ ∑ u, φ u ^ 2 := sum_nonneg fun u _ => sq_nonneg _
  calc (∑ u, φ u * Q u) ^ 2 ≤ (∑ u, φ u ^ 2) * ∑ u, Q u ^ 2 := hcs
    _ ≤ (∑ u, φ u ^ 2) * (qF * ∑ w, ψ w ^ 2) := by
        rw [e2]; exact mul_le_mul_of_nonneg_left (by linarith) hφ
    _ = qF * (∑ u, φ u ^ 2) * (∑ w, ψ w ^ 2) := by ring

theorem abs_paleyForm_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (φ ψ : F → ℝ) :
    |paleyForm φ ψ| ≤
      Real.sqrt qF * (Real.sqrt (∑ u, φ u ^ 2) * Real.sqrt (∑ w, ψ w ^ 2)) := by
  have h := paleyForm_sq_le hF h3 φ ψ
  have hq : 0 ≤ qF := Nat.cast_nonneg _
  have hφ : 0 ≤ ∑ u, φ u ^ 2 := sum_nonneg fun u _ => sq_nonneg _
  rw [← Real.sqrt_mul hφ, ← Real.sqrt_mul hq, ← mul_assoc]
  exact Real.abs_le_sqrt h

omit [Field F] [DecidableEq F] in
theorem abs_sum_mul_le (φ ψ : F → ℝ) :
    |∑ u, φ u * ψ u| ≤ Real.sqrt (∑ u, φ u ^ 2) * Real.sqrt (∑ u, ψ u ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq univ φ ψ
  rw [← Real.sqrt_mul (sum_nonneg fun u _ => sq_nonneg _)]
  exact Real.abs_le_sqrt h

/-! ## The conditional weight given `x₁ = y` -/

/-- The indicator `N(t) = [t ≠ y]`. -/
noncomputable def offY (y t : F) : ℝ := if t = y then 0 else 1

/-- `a(t) = χ(t - y)`. -/
noncomputable def aY (y t : F) : ℝ := (χ (t - y) : ℝ)

omit [Field F] in
theorem sum_offY (y : F) : ∑ t, offY y t = qF - 1 := by
  have e : ∀ t, offY y t = 1 - (if t = y then 1 else 0) := by
    intro t; unfold offY; split_ifs <;> ring
  simp only [e, sum_sub_distrib, sum_ite_eq', mem_univ, ↓reduceIte, sum_const, card_univ,
    nsmul_eq_mul, mul_one]

theorem sum_aY (hF : ringChar F ≠ 2) (y : F) : ∑ t, aY y t = 0 := by
  unfold aY
  have h : ∑ t, (χ t : ℝ) = 0 := by exact_mod_cast quadraticChar_sum_zero hF
  rw [← h]
  exact Equiv.sum_comp (Equiv.subRight y) (fun t => (χ t : ℝ))

theorem aY_self (y : F) : aY y y = 0 := by simp [aY]

theorem aY_sq_le (y t : F) : aY y t ^ 2 ≤ 1 := chi_sq_le_one _

theorem aY_bounds (y t : F) : -1 ≤ aY y t ∧ aY y t ≤ 1 := by
  have h := aY_sq_le y t
  constructor <;> nlinarith [sq_nonneg (aY y t + 1), sq_nonneg (aY y t - 1)]

/-- **The `x₀`-marginal weight given `x₁ = y`**: `W₀(u) = [u ≠ y](p - 3)(p - 4 + 2a(u))/4`. -/
theorem W0_eq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (y u : F) :
    ∑ w, oldW u y w = offY y u * ((qF - 3) * (qF - 4 + 2 * aY y u) / 4) := by
  by_cases hu : u = y
  · subst hu
    simp only [oldW_diag_x2, sum_const_zero, offY, ↓reduceIte, zero_mul]
  · rw [sum_oldW_x2 hF h3 hu, offY, ite_eq_right hu, one_mul, aY, chi_swap h3 y u, Int.cast_neg]
    ring

/-- **The `x₂`-marginal weight given `x₁ = y`**: `W₂(w) = [w ≠ y](p - 3)(p - 4 - 2a(w))/4`. -/
theorem W2_eq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (y w : F) :
    ∑ u, oldW u y w = offY y w * ((qF - 3) * (qF - 4 - 2 * aY y w) / 4) := by
  by_cases hw : w = y
  · subst hw
    simp only [oldW_diag_x0, sum_const_zero, offY, ↓reduceIte, zero_mul]
  · rw [sum_oldW_x0 hF h3 (Ne.symm hw), offY, ite_eq_right hw, one_mul, aY]

/-- **The pointwise form of the conditional weight**: off `y`,
`4W(u, w) = (1 + χ(w - u))(p - 5 + a(u) - a(w)) - [u = w](p - 5)`. -/
theorem four_oldW (h3 : Fintype.card F % 4 = 3) (y u w : F) (hu : u ≠ y) (hw : w ≠ y) :
    4 * oldW u y w = (1 + (χ (w - u) : ℝ)) * (qF - 5 + aY y u - aY y w) -
      (if u = w then qF - 5 else 0) := by
  by_cases huw : u = w
  · subst huw
    simp [oldW_diag_x1]
  · rw [ite_eq_right huw]
    unfold oldW
    rw [ite_eq_left (show u ≠ y ∧ u ≠ w ∧ y ≠ w from ⟨hu, huw, Ne.symm hw⟩), aY, aY,
      chi_swap h3 y u, Int.cast_neg]
    ring

/-- **The expansion for base-centred functions vanishing at `y`**:
`4∑ W φ ψ = (p - 5)B(φ, ψ) + B(aφ, ψ) - B(φ, aψ) - (p - 5)⟨φ, ψ⟩`. -/
theorem four_sum_centred (h3 : Fintype.card F % 4 = 3) (y : F) (φ ψ : F → ℝ) (hφy : φ y = 0)
    (hψy : ψ y = 0) (hφ : ∑ u, φ u = 0) (hψ : ∑ w, ψ w = 0) :
    4 * ∑ u, ∑ w, oldW u y w * φ u * ψ w =
      (qF - 5) * paleyForm φ ψ + paleyForm (fun u => aY y u * φ u) ψ -
        paleyForm φ (fun w => aY y w * ψ w) - (qF - 5) * ∑ u, φ u * ψ u := by
  have key : ∀ u w, 4 * (oldW u y w * φ u * ψ w) =
      (qF - 5) * (φ u * ψ w) + (aY y u * φ u) * ψ w - φ u * (aY y w * ψ w) +
      (qF - 5) * ((χ (w - u) : ℝ) * φ u * ψ w) + (χ (w - u) : ℝ) * (aY y u * φ u) * ψ w -
      (χ (w - u) : ℝ) * φ u * (aY y w * ψ w) -
      (if u = w then (qF - 5) * (φ u * ψ w) else 0) := by
    intro u w
    by_cases hu : u = y
    · subst hu; rw [hφy]; split_ifs <;> ring
    by_cases hw : w = y
    · subst hw; rw [hψy]; split_ifs; ring
    have h4 := four_oldW h3 y u w hu hw
    calc 4 * (oldW u y w * φ u * ψ w) = (4 * oldW u y w) * (φ u * ψ w) := by ring
      _ = _ := by rw [h4]; split_ifs <;> ring
  have hsum : 4 * ∑ u, ∑ w, oldW u y w * φ u * ψ w =
      ∑ u, ∑ w, ((qF - 5) * (φ u * ψ w) + (aY y u * φ u) * ψ w - φ u * (aY y w * ψ w) +
      (qF - 5) * ((χ (w - u) : ℝ) * φ u * ψ w) + (χ (w - u) : ℝ) * (aY y u * φ u) * ψ w -
      (χ (w - u) : ℝ) * φ u * (aY y w * ψ w) -
      (if u = w then (qF - 5) * (φ u * ψ w) else 0)) := by
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by rw [mul_sum]; exact sum_congr rfl fun w _ => key u w
  rw [hsum]
  simp only [sum_sub_distrib, sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
  have z1 : ∑ u, ∑ w, (qF - 5) * (φ u * ψ w) = 0 := by
    simp only [← mul_sum, hψ, mul_zero, sum_const_zero]
  have z2 : ∑ u, ∑ w, aY y u * φ u * ψ w = 0 := by
    simp only [← mul_sum, hψ, mul_zero, sum_const_zero]
  have z3 : ∑ u, ∑ w, φ u * (aY y w * ψ w) = 0 := by
    simp only [← sum_mul_sum, hφ, zero_mul]
  have p1 : ∑ u, ∑ w, (qF - 5) * ((χ (w - u) : ℝ) * φ u * ψ w) = (qF - 5) * paleyForm φ ψ := by
    unfold paleyForm; simp only [mul_sum]
  have p2 : ∑ u, ∑ w, (χ (w - u) : ℝ) * (aY y u * φ u) * ψ w =
      paleyForm (fun u => aY y u * φ u) ψ := rfl
  have p3 : ∑ u, ∑ w, (χ (w - u) : ℝ) * φ u * (aY y w * ψ w) =
      paleyForm φ (fun w => aY y w * ψ w) := rfl
  have p4 : ∑ u, (qF - 5) * (φ u * ψ u) = (qF - 5) * ∑ u, φ u * ψ u := by rw [mul_sum]
  rw [z1, z2, z3, p1, p2, p3, p4]
  ring

/-- **The bound for base-centred functions vanishing at `y`**:
`|4∑ W φ ψ| ≤ ((p - 3)√p + (p - 5)) ‖φ‖ ‖ψ‖`. -/
theorem abs_four_sum_centred (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h7 : 7 ≤ qF) (y : F) (φ ψ : F → ℝ) (hφy : φ y = 0) (hψy : ψ y = 0) (hφ : ∑ u, φ u = 0)
    (hψ : ∑ w, ψ w = 0) :
    |4 * ∑ u, ∑ w, oldW u y w * φ u * ψ w| ≤
      ((qF - 3) * Real.sqrt qF + (qF - 5)) *
        (Real.sqrt (∑ u, φ u ^ 2) * Real.sqrt (∑ w, ψ w ^ 2)) := by
  rw [four_sum_centred h3 y φ ψ hφy hψy hφ hψ]
  set Nφ := Real.sqrt (∑ u, φ u ^ 2) with hNφ
  set Nψ := Real.sqrt (∑ w, ψ w ^ 2) with hNψ
  set s := Real.sqrt qF with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hNφ0 : 0 ≤ Nφ := Real.sqrt_nonneg _
  have hNψ0 : 0 ≤ Nψ := Real.sqrt_nonneg _
  have haφ : Real.sqrt (∑ u, (aY y u * φ u) ^ 2) ≤ Nφ :=
    Real.sqrt_le_sqrt (sum_le_sum fun u _ => by
      rw [mul_pow]; nlinarith [aY_sq_le y u, sq_nonneg (φ u)])
  have haψ : Real.sqrt (∑ w, (aY y w * ψ w) ^ 2) ≤ Nψ :=
    Real.sqrt_le_sqrt (sum_le_sum fun w _ => by
      rw [mul_pow]; nlinarith [aY_sq_le y w, sq_nonneg (ψ w)])
  have b1 := abs_le.mp (abs_paleyForm_le hF h3 φ ψ)
  have b2 : |paleyForm (fun u => aY y u * φ u) ψ| ≤ s * (Nφ * Nψ) :=
    (abs_paleyForm_le hF h3 _ ψ).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haφ hNψ0) hs0)
  have b3 : |paleyForm φ (fun w => aY y w * ψ w)| ≤ s * (Nφ * Nψ) :=
    (abs_paleyForm_le hF h3 φ _).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haψ hNφ0) hs0)
  have b4 := abs_le.mp (abs_sum_mul_le φ ψ)
  have b2' := abs_le.mp b2
  have b3' := abs_le.mp b3
  have hc : 0 ≤ qF - 5 := by linarith
  have c1 := mul_le_mul_of_nonneg_left b1.2 hc
  have c2 := mul_le_mul_of_nonneg_left b1.1 hc
  have c3 := mul_le_mul_of_nonneg_left b4.2 hc
  have c4 := mul_le_mul_of_nonneg_left b4.1 hc
  have e : ((qF - 3) * s + (qF - 5)) * (Nφ * Nψ) =
      (qF - 5) * (s * (Nφ * Nψ)) + s * (Nφ * Nψ) + s * (Nφ * Nψ) + (qF - 5) * (Nφ * Nψ) := by
    ring
  rw [e, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The square of the conditional coordinate: `a(t)² = [t ≠ y]`. -/
theorem aY_sq (y t : F) : aY y t ^ 2 = offY y t := by
  by_cases ht : t = y
  · subst ht; simp [aY, offY]
  · rw [offY, ite_eq_right ht, aY]
    exact chi_sq_one (Ne.symm ht)

omit [Field F] [Fintype F] in
theorem offY_mul_self (y t : F) : offY y t * offY y t = offY y t := by
  unfold offY; split_ifs <;> ring

/-- **`ϱ₃₄` at a prime**: `ϱ₃₄(1/p, p^{-1/2}) = (√p + 1 + 4/(p - 4))/(p - 6)`. -/
theorem rho34_prime_eq {x : ℝ} (hx : 7 ≤ x) :
    rho34 (1 / x) (1 / Real.sqrt x) = (Real.sqrt x + 1 + 4 / (x - 4)) / (x - 6) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ x = s ^ 2 :=
    ⟨Real.sqrt x, Real.sqrt_pos.2 hx0, (Real.sq_sqrt hx0.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  have h4 : s ^ 2 - 4 ≠ 0 := by intro h; linarith
  have h6 : s ^ 2 - 6 ≠ 0 := by intro h; linarith
  have h4' : 1 - 4 * (1 / s ^ 2) ≠ 0 := by
    rw [show 1 - 4 * (1 / s ^ 2) = (s ^ 2 - 4) / s ^ 2 by field_simp]
    exact div_ne_zero h4 (by positivity)
  have h6' : 1 - 6 * (1 / s ^ 2) ≠ 0 := by
    rw [show 1 - 6 * (1 / s ^ 2) = (s ^ 2 - 6) / s ^ 2 by field_simp]
    exact div_ne_zero h6 (by positivity)
  unfold rho34
  rw [div_eq_div_iff h6' h6]
  field_simp

/-- **The constant of the paper is at most `ϱ₃₄`**: with `M = ((p-3)√p + (p-5))/4 + (p-3)/(p-4)`
and `D = (p-3)(p-6)/4`, `M ≤ ϱ₃₄(1/p, p^{-1/2}) D`. -/
theorem kappa_le_rho34 {x : ℝ} (hx : 7 ≤ x) :
    ((x - 3) * Real.sqrt x + (x - 5)) / 4 + (x - 3) / (x - 4) ≤
      rho34 (1 / x) (1 / Real.sqrt x) * ((x - 3) * (x - 6) / 4) := by
  rw [rho34_prime_eq hx]
  have h4 : x - 4 ≠ 0 := by intro h; linarith
  have h6 : x - 6 ≠ 0 := by intro h; linarith
  have e : (Real.sqrt x + 1 + 4 / (x - 4)) / (x - 6) * ((x - 3) * (x - 6) / 4) =
      ((x - 3) * Real.sqrt x + (x - 5)) / 4 + (x - 3) / (x - 4) + 1 / 2 := by
    field_simp
    ring
  rw [e]
  linarith

/-! ## Re-centring -/

/-- The base mean of `f` over the labels other than `y`. -/
noncomputable def meanOff (y : F) (f : F → ℝ) : ℝ := (∑ u, offY y u * f u) / (qF - 1)

/-- The base-centred version of `f`, vanishing at `y`. -/
noncomputable def cenF (y : F) (f : F → ℝ) (u : F) : ℝ := offY y u * (f u - meanOff y f)

omit [Field F] in
theorem cenF_self (y : F) (f : F → ℝ) : cenF y f y = 0 := by simp [cenF, offY]

omit [Field F] in
theorem sum_cenF (h7 : 7 ≤ qF) (y : F) (f : F → ℝ) : ∑ u, cenF y f u = 0 := by
  have hq1 : qF - 1 ≠ 0 := by intro h; linarith
  simp only [cenF, mul_sub, sum_sub_distrib, ← sum_mul, sum_offY, meanOff]
  field_simp
  ring

omit [Field F] in
theorem offY_cenF (y : F) (f : F → ℝ) (u : F) : offY y u * cenF y f u = cenF y f u := by
  simp only [cenF, ← mul_assoc, offY_mul_self]

theorem oldW_mul_left (y u w : F) (f : F → ℝ) :
    oldW u y w * f u = oldW u y w * (cenF y f u + meanOff y f) := by
  by_cases hu : u = y
  · subst hu; simp [oldW_diag_x2]
  · simp only [cenF, offY, hu, ↓reduceIte, one_mul, sub_add_cancel]

theorem oldW_mul_right (y u w : F) (g : F → ℝ) :
    oldW u y w * g w = oldW u y w * (cenF y g w + meanOff y g) := by
  by_cases hw : w = y
  · subst hw; simp [oldW_diag_x0]
  · simp only [cenF, offY, hw, ↓reduceIte, one_mul, sub_add_cancel]

omit [Field F] in
/-- Centring lowers the base norm: `∑ φ² ≤ ∑_{u ≠ y} f²`. -/
theorem sum_sq_cenF_le (h7 : 7 ≤ qF) (y : F) (f : F → ℝ) :
    ∑ u, cenF y f u ^ 2 ≤ ∑ u, offY y u * f u ^ 2 := by
  have hq1 : qF - 1 ≠ 0 := by intro h; linarith
  set α := meanOff y f with hα
  have e1 : ∀ u, cenF y f u ^ 2 = offY y u * f u ^ 2 - 2 * α * (offY y u * f u) +
      α ^ 2 * offY y u := by
    intro u
    have := offY_mul_self y u
    calc cenF y f u ^ 2 = (offY y u * offY y u) * (f u - α) ^ 2 := by simp only [cenF]; ring
      _ = _ := by rw [this]; ring
  have hs : ∑ u, offY y u * f u = α * (qF - 1) := by
    rw [hα, meanOff]; field_simp
  simp only [e1, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_offY, hs]
  nlinarith [sq_nonneg α]

/-- The lower bound `1 - μ` of the marginal density of `x₀`: `W₀(u) ≥ [u ≠ y](p-3)(p-6)/4`. -/
theorem W0_sq_lower (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (y : F)
    (f : F → ℝ) :
    (qF - 3) * (qF - 6) / 4 * ∑ u, offY y u * f u ^ 2 ≤ ∑ u, (∑ w, oldW u y w) * f u ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun u _ => ?_
  rw [W0_eq hF h3 y u]
  have hb := (aY_bounds y u).1
  have hoff : 0 ≤ offY y u := by unfold offY; split_ifs <;> norm_num
  have hq3 : 0 ≤ qF - 3 := by linarith
  have h : (qF - 3) * (qF - 6) / 4 ≤ (qF - 3) * (qF - 4 + 2 * aY y u) / 4 := by nlinarith
  have := mul_le_mul_of_nonneg_right h (mul_nonneg hoff (sq_nonneg (f u)))
  linarith

/-- The lower bound `1 - μ` of the marginal density of `x₂`: `W₂(w) ≥ [w ≠ y](p-3)(p-6)/4`. -/
theorem W2_sq_lower (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (y : F)
    (g : F → ℝ) :
    (qF - 3) * (qF - 6) / 4 * ∑ w, offY y w * g w ^ 2 ≤ ∑ w, (∑ u, oldW u y w) * g w ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun w _ => ?_
  rw [W2_eq hF h3 y w]
  have hb := (aY_bounds y w).2
  have hoff : 0 ≤ offY y w := by unfold offY; split_ifs <;> norm_num
  have hq3 : 0 ≤ qF - 3 := by linarith
  have h : (qF - 3) * (qF - 6) / 4 ≤ (qF - 3) * (qF - 4 - 2 * aY y w) / 4 := by nlinarith
  have := mul_le_mul_of_nonneg_right h (mul_nonneg hoff (sq_nonneg (g w)))
  linarith

theorem sum_W0_cenF (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (y : F)
    (f : F → ℝ) :
    ∑ u, (∑ w, oldW u y w) * cenF y f u = (qF - 3) / 2 * ∑ u, aY y u * cenF y f u := by
  have e : ∀ u, (∑ w, oldW u y w) * cenF y f u =
      (qF - 3) * (qF - 4) / 4 * cenF y f u + (qF - 3) / 2 * (aY y u * cenF y f u) := by
    intro u
    rw [W0_eq hF h3 y u]
    calc offY y u * ((qF - 3) * (qF - 4 + 2 * aY y u) / 4) * cenF y f u
        = ((qF - 3) * (qF - 4 + 2 * aY y u) / 4) * (offY y u * cenF y f u) := by ring
      _ = _ := by rw [offY_cenF]; ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_cenF h7, mul_zero, zero_add]

theorem sum_W2_cenF (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (y : F)
    (g : F → ℝ) :
    ∑ w, (∑ u, oldW u y w) * cenF y g w = -((qF - 3) / 2 * ∑ w, aY y w * cenF y g w) := by
  have e : ∀ w, (∑ u, oldW u y w) * cenF y g w =
      (qF - 3) * (qF - 4) / 4 * cenF y g w - (qF - 3) / 2 * (aY y w * cenF y g w) := by
    intro w
    rw [W2_eq hF h3 y w]
    calc offY y w * ((qF - 3) * (qF - 4 - 2 * aY y w) / 4) * cenF y g w
        = ((qF - 3) * (qF - 4 - 2 * aY y w) / 4) * (offY y w * cenF y g w) := by ring
      _ = _ := by rw [offY_cenF]; ring
  simp only [e, sum_sub_distrib, ← mul_sum, sum_cenF h7, mul_zero, zero_sub]

/-- The total conditional weight `Z = (p - 1)(p - 3)(p - 4)/4`. -/
theorem sum_W0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (y : F) :
    ∑ u, ∑ w, oldW u y w = (qF - 1) * (qF - 3) * (qF - 4) / 4 := by
  have e : ∀ u, ∑ w, oldW u y w = (qF - 3) * (qF - 4) / 4 * offY y u + (qF - 3) / 2 * aY y u := by
    intro u
    have ha : offY y u * aY y u = aY y u := by
      by_cases hu : u = y
      · subst hu; simp [aY_self]
      · simp [offY, hu]
    rw [W0_eq hF h3 y u]
    calc offY y u * ((qF - 3) * (qF - 4 + 2 * aY y u) / 4)
        = (qF - 3) * (qF - 4) / 4 * offY y u + (qF - 3) / 2 * (offY y u * aY y u) := by ring
      _ = _ := by rw [ha]
  simp only [e, sum_add_distrib, ← mul_sum, sum_offY, sum_aY hF y, mul_zero, add_zero]
  ring

/-- **The re-centring identity**: `∑ W f g = ∑ W φ ψ + β ∑ W₀ φ + α ∑ W₂ ψ + αβ Z`. -/
theorem sum_oldW_split (y : F) (f g : F → ℝ) :
    ∑ u, ∑ w, oldW u y w * f u * g w =
      ∑ u, ∑ w, oldW u y w * cenF y f u * cenF y g w +
        meanOff y g * ∑ u, (∑ w, oldW u y w) * cenF y f u +
        meanOff y f * ∑ w, (∑ u, oldW u y w) * cenF y g w +
        meanOff y f * meanOff y g * ∑ u, ∑ w, oldW u y w := by
  set α := meanOff y f
  set β := meanOff y g
  have e1 : ∀ u w, oldW u y w * f u * g w =
      oldW u y w * cenF y f u * cenF y g w + β * (oldW u y w * cenF y f u) +
        α * (oldW u y w * cenF y g w) + α * β * oldW u y w := by
    intro u w
    have h1 := oldW_mul_left y u w f
    have h2 := oldW_mul_right y u w g
    calc oldW u y w * f u * g w = (oldW u y w * f u) * g w := rfl
      _ = (cenF y f u + α) * (oldW u y w * g w) := by rw [h1]; ring
      _ = (cenF y f u + α) * (oldW u y w * (cenF y g w + β)) := by rw [h2]
      _ = _ := by ring
  simp only [e1, sum_add_distrib]
  have s2 : ∑ u, ∑ w, β * (oldW u y w * cenF y f u) = β * ∑ u, (∑ w, oldW u y w) * cenF y f u := by
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by rw [sum_mul, mul_sum]
  have s3 : ∑ u, ∑ w, α * (oldW u y w * cenF y g w) = α * ∑ w, (∑ u, oldW u y w) * cenF y g w := by
    rw [sum_comm, mul_sum]
    exact sum_congr rfl fun w _ => by rw [sum_mul, mul_sum]
  have s4 : ∑ u, ∑ w, α * β * oldW u y w = α * β * ∑ u, ∑ w, oldW u y w := by
    simp only [mul_sum]
  rw [s2, s3, s4]

/-- **The covariance correction**: for `W₀`-centred `f` and `W₂`-centred `g`,
`∑ W f g = ∑ W φ ψ + (p-3)/((p-1)(p-4)) (∑ a φ)(∑ a ψ)`. -/
theorem sum_oldW_centred (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (y : F) (f g : F → ℝ) (hf : ∑ u, (∑ w, oldW u y w) * f u = 0)
    (hg : ∑ w, (∑ u, oldW u y w) * g w = 0) :
    ∑ u, ∑ w, oldW u y w * f u * g w =
      ∑ u, ∑ w, oldW u y w * cenF y f u * cenF y g w +
        (qF - 3) / ((qF - 1) * (qF - 4)) *
          ((∑ u, aY y u * cenF y f u) * (∑ w, aY y w * cenF y g w)) := by
  set α := meanOff y f
  set β := meanOff y g
  set Z := ∑ u, ∑ w, oldW u y w with hZ
  have hZv : Z = (qF - 1) * (qF - 3) * (qF - 4) / 4 := sum_W0 hF h3 y
  have hZ0 : Z ≠ 0 := by
    rw [hZv]
    have : 0 < qF - 4 := by linarith
    have : 0 < qF - 3 := by linarith
    have : 0 < qF - 1 := by linarith
    positivity
  -- centrings
  have hcf : ∑ u, (∑ w, oldW u y w) * cenF y f u = -(α * Z) := by
    have e : ∀ u, (∑ w, oldW u y w) * f u = (∑ w, oldW u y w) * cenF y f u +
        α * ∑ w, oldW u y w := by
      intro u
      rw [sum_mul, sum_mul, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun w _ => by rw [oldW_mul_left y u w f]; ring
    simp only [e, sum_add_distrib, ← mul_sum] at hf
    linarith
  have hcg : ∑ w, (∑ u, oldW u y w) * cenF y g w = -(β * Z) := by
    have e : ∀ w, (∑ u, oldW u y w) * g w = (∑ u, oldW u y w) * cenF y g w +
        β * ∑ u, oldW u y w := by
      intro w
      rw [sum_mul, sum_mul, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun u _ => by rw [oldW_mul_right y u w g]; ring
    simp only [e, sum_add_distrib, ← mul_sum] at hg
    have hZ2 : ∑ w, ∑ u, oldW u y w = Z := by rw [hZ]; exact sum_comm
    rw [hZ2] at hg
    linarith
  have hαZ := sum_W0_cenF hF h3 h7 y f
  have hβZ := sum_W2_cenF hF h3 h7 y g
  rw [hcf] at hαZ
  rw [hcg] at hβZ
  rw [sum_oldW_split, hcf, hcg, ← hZ]
  have key : α * β * Z = -((qF - 3) / ((qF - 1) * (qF - 4))) *
      ((∑ u, aY y u * cenF y f u) * (∑ w, aY y w * cenF y g w)) := by
    have e : α * β * Z = (α * Z) * (β * Z) / Z := by field_simp
    rw [e, show α * Z = -((qF - 3) / 2 * ∑ u, aY y u * cenF y f u) by linarith,
      show β * Z = (qF - 3) / 2 * ∑ w, aY y w * cenF y g w by linarith, hZv]
    have : 0 < qF - 4 := by linarith
    have : 0 < qF - 3 := by linarith
    have : 0 < qF - 1 := by linarith
    field_simp
    ring
  linear_combination (-1 : ℝ) * key

/-- **`lem:oct24:feature-block`(a), proof Step 4, the prime bound**: given `x₁ = y`, for
`f` centred in the conditional law of `x₀` and `g` centred in that of `x₂` (unnormalized weights
`W₀(u) = ∑_w oldW(u, y, w)`, `W₂(w) = ∑_u oldW(u, y, w)`),
`|∑_{u,w} oldW(u, y, w) f(u) g(w)| ≤ ϱ₃₄(1/p, p^{-1/2}) √(∑ W₀ f²) √(∑ W₂ g²)`: the conditional
maximal correlation of `x₀` and `x₂` given `x₁` is at most `ϱ₃₄(p)`. -/
theorem edge34_prime (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (y : F)
    (f g : F → ℝ) (hf : ∑ u, (∑ w, oldW u y w) * f u = 0)
    (hg : ∑ w, (∑ u, oldW u y w) * g w = 0) :
    |∑ u, ∑ w, oldW u y w * f u * g w| ≤
      rho34 (1 / qF) (1 / Real.sqrt qF) *
        (Real.sqrt (∑ u, (∑ w, oldW u y w) * f u ^ 2) *
          Real.sqrt (∑ w, (∑ u, oldW u y w) * g w ^ 2)) := by
  set φ := cenF y f
  set ψ := cenF y g
  set Nφ := Real.sqrt (∑ u, φ u ^ 2) with hNφ
  set Nψ := Real.sqrt (∑ w, ψ w ^ 2) with hNψ
  have hNφ0 : 0 ≤ Nφ := Real.sqrt_nonneg _
  have hNψ0 : 0 ≤ Nψ := Real.sqrt_nonneg _
  have hq1' : 0 ≤ qF - 1 := by linarith
  have h4 : 0 < qF - 4 := by linarith
  -- the correction term
  have hsum_a : ∑ u, aY y u ^ 2 = qF - 1 := by simp only [aY_sq, sum_offY]
  have hSa : |∑ u, aY y u * φ u| ≤ Real.sqrt (qF - 1) * Nφ := by
    have h := abs_sum_mul_le (aY y) φ
    rwa [hsum_a] at h
  have hSb : |∑ w, aY y w * ψ w| ≤ Real.sqrt (qF - 1) * Nψ := by
    have h := abs_sum_mul_le (aY y) ψ
    rwa [hsum_a] at h
  have hc0 : 0 ≤ (qF - 3) / ((qF - 1) * (qF - 4)) := by
    have : 0 < qF - 3 := by linarith
    have : 0 < qF - 1 := by linarith
    positivity
  have hcorr : |(qF - 3) / ((qF - 1) * (qF - 4)) *
      ((∑ u, aY y u * φ u) * (∑ w, aY y w * ψ w))| ≤ (qF - 3) / (qF - 4) * (Nφ * Nψ) := by
    rw [abs_mul, abs_of_nonneg hc0, abs_mul]
    have hprod : |∑ u, aY y u * φ u| * |∑ w, aY y w * ψ w| ≤ (qF - 1) * (Nφ * Nψ) := by
      have := mul_le_mul hSa hSb (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hNφ0)
      calc _ ≤ Real.sqrt (qF - 1) * Nφ * (Real.sqrt (qF - 1) * Nψ) := this
        _ = (Real.sqrt (qF - 1) * Real.sqrt (qF - 1)) * (Nφ * Nψ) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hq1']
    calc (qF - 3) / ((qF - 1) * (qF - 4)) * (|∑ u, aY y u * φ u| * |∑ w, aY y w * ψ w|)
        ≤ (qF - 3) / ((qF - 1) * (qF - 4)) * ((qF - 1) * (Nφ * Nψ)) :=
          mul_le_mul_of_nonneg_left hprod hc0
      _ = (qF - 3) / (qF - 4) * (Nφ * Nψ) := by
          have : qF - 1 ≠ 0 := by intro h; linarith
          field_simp
  -- the centred term
  have hcent := abs_four_sum_centred hF h3 h7 y φ ψ (cenF_self y f) (cenF_self y g)
    (sum_cenF h7 y f) (sum_cenF h7 y g)
  have h1 : |∑ u, ∑ w, oldW u y w * φ u * ψ w| ≤
      ((qF - 3) * Real.sqrt qF + (qF - 5)) / 4 * (Nφ * Nψ) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hcent
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  set M := ((qF - 3) * Real.sqrt qF + (qF - 5)) / 4 + (qF - 3) / (qF - 4) with hMd
  have hM : |∑ u, ∑ w, oldW u y w * f u * g w| ≤ M * (Nφ * Nψ) := by
    rw [sum_oldW_centred hF h3 h7 y f g hf hg]
    calc _ ≤ |∑ u, ∑ w, oldW u y w * φ u * ψ w| + |(qF - 3) / ((qF - 1) * (qF - 4)) *
          ((∑ u, aY y u * φ u) * (∑ w, aY y w * ψ w))| := abs_add_le _ _
      _ ≤ _ := by rw [hMd, add_mul]; exact add_le_add h1 hcorr
  -- the norms
  set D := (qF - 3) * (qF - 6) / 4 with hD
  have hD0 : 0 < D := by
    have : 0 < qF - 3 := by linarith
    have : 0 < qF - 6 := by linarith
    positivity
  have hnf : D * Nφ ^ 2 ≤ ∑ u, (∑ w, oldW u y w) * f u ^ 2 := by
    rw [hNφ, Real.sq_sqrt (sum_nonneg fun u _ => sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (sum_sq_cenF_le h7 y f) hD0.le).trans
      (W0_sq_lower hF h3 h7 y f)
  have hng : D * Nψ ^ 2 ≤ ∑ w, (∑ u, oldW u y w) * g w ^ 2 := by
    rw [hNψ, Real.sq_sqrt (sum_nonneg fun w _ => sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (sum_sq_cenF_le h7 y g) hD0.le).trans
      (W2_sq_lower hF h3 h7 y g)
  set A := Real.sqrt (∑ u, (∑ w, oldW u y w) * f u ^ 2) with hA
  set B := Real.sqrt (∑ w, (∑ u, oldW u y w) * g w ^ 2) with hB
  have hA' : Real.sqrt D * Nφ ≤ A := by
    rw [hA, ← Real.sqrt_sq hNφ0, ← Real.sqrt_mul hD0.le]
    exact Real.sqrt_le_sqrt hnf
  have hB' : Real.sqrt D * Nψ ≤ B := by
    rw [hB, ← Real.sqrt_sq hNψ0, ← Real.sqrt_mul hD0.le]
    exact Real.sqrt_le_sqrt hng
  have hκ := kappa_le_rho34 h7
  have hM0 : 0 ≤ M := by
    have : 0 ≤ (qF - 3) / (qF - 4) := div_nonneg (by linarith) h4.le
    have : 0 ≤ (qF - 3) * Real.sqrt qF := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have : 0 ≤ qF - 5 := by linarith
    positivity
  have hsD : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hD0.le
  have hsD0 : 0 < Real.sqrt D := Real.sqrt_pos.2 hD0
  calc |∑ u, ∑ w, oldW u y w * f u * g w| ≤ M * (Nφ * Nψ) := hM
    _ = M / D * ((Real.sqrt D * Nφ) * (Real.sqrt D * Nψ)) := by
        have e : (Real.sqrt D * Nφ) * (Real.sqrt D * Nψ) = D * (Nφ * Nψ) := by
          calc (Real.sqrt D * Nφ) * (Real.sqrt D * Nψ) = (Real.sqrt D * Real.sqrt D) * (Nφ * Nψ) :=
                by ring
            _ = D * (Nφ * Nψ) := by rw [hsD]
        rw [e]
        field_simp
    _ ≤ M / D * (A * B) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hM0 hD0.le)
        exact mul_le_mul hA' hB' (mul_nonneg hsD0.le hNψ0) (Real.sqrt_nonneg _)
    _ ≤ rho34 (1 / qF) (1 / Real.sqrt qF) * (A * B) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        rw [div_le_iff₀ hD0]
        exact hκ

end Prime

end Sarkozy.OpsFeature
