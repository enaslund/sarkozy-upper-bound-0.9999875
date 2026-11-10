module

public import Sarkozy.FiniteProbability
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Chi-square divergences of finite laws (the abstract steps of `lem:record:root-marginal`)

`paper/sections/22_variance.tex`, `lem:record:root-marginal` and its proof. The lemma compares,
at a fold chamber, the half law `ν_{L,p}` of the root with the fold law `λ_{F,p}` through the
density `dν/dλ` and the chi-square divergence `χ²(ν ‖ λ)`. This file proves the steps of that proof
that are statements about finite laws only; the counting and moment inputs are in
`Sarkozy.Variance.RootMarginal`.

Laws are weight functions on a finite type: the reference `λ` has positive weights of total one,
`ν` has total one. `chiSq ν λ = ∑ₓ (ν x - λ x)² / λ x`.

* `chiSq_eq`, `chiSq_eq_density`: `χ² = ∑ ν²/λ - 1 = E_λ (dν/dλ - 1)²`.
* `chiSq_density_range_of_counts` (**(i)**, the abstract step): a law with density proportional to
  a count `𝔑` whose values lie in `[c, R c]`, `c > 0`, has density in `[R⁻¹, R]`, and the supremum
  of the density is at most `R` times its infimum.
* `chiSq_le_of_density_range` (**(ii), first bound**): density in `[R⁻¹, R]` gives
  `E g² ≤ R + R⁻¹ - 1`, i.e. `χ² ≤ (R - 1)²/R`.
* `chiSq_le_of_sq_dev` (**(ii), second bound, last step**): for `ς` with `E_λ (ς - 1)² ≤ D²` and
  `E_λ ς ≥ L > 0`, the law `ν = ς λ / E_λ ς` has `χ²(ν ‖ λ) = Var(ς)/(E ς)² ≤ D²/L²`.
* `chiSq_prod` (**(iii)**): for product laws over a finite index type,
  `1 + χ²(⊗ν ‖ ⊗λ) = ∏ (1 + χ²(ν_i ‖ λ_i))`; `chiSq_prodWeight_density` (the product density is
  the product of the densities, so ranges multiply), and `chiSq_prod_le_pow`, `prod_le_pow_of_le`
  (the bounds `∏ R_i ≤ R̄ⁿ`, `∏ (1 + χ_i) - 1 ≤ (1 + χ̄)ⁿ - 1` for at most `n` factors).
-/

namespace Sarkozy.Variance

open Finset
open scoped BigOperators

section Single

variable {S : Type*} [Fintype S]

/-- The chi-square divergence `χ²(ν ‖ λ) = ∑ₓ (ν x - λ x)² / λ x` of finite weights. -/
noncomputable def chiSq (nu lam : S → ℝ) : ℝ := ∑ x, (nu x - lam x) ^ 2 / lam x

/-- `χ²(ν ‖ λ) = ∑ ν²/λ - 1` for weights of total one with `λ > 0`. -/
theorem chiSq_eq {nu lam : S → ℝ} (hlam : ∀ x, 0 < lam x) (hnu1 : ∑ x, nu x = 1)
    (hlam1 : ∑ x, lam x = 1) : chiSq nu lam = ∑ x, nu x ^ 2 / lam x - 1 := by
  unfold chiSq
  have h : ∀ x, (nu x - lam x) ^ 2 / lam x = nu x ^ 2 / lam x - 2 * nu x + lam x := by
    intro x
    have := (hlam x).ne'
    field_simp
    ring
  simp_rw [h]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hnu1, hlam1]
  ring

/-- `χ²(ν ‖ λ) = E_λ (g - 1)²` with the density `g = ν/λ`. -/
theorem chiSq_eq_density {nu lam : S → ℝ} (hlam : ∀ x, 0 < lam x) :
    chiSq nu lam = ∑ x, lam x * (nu x / lam x - 1) ^ 2 := by
  unfold chiSq
  apply sum_congr rfl
  intro x _
  have := (hlam x).ne'
  field_simp

theorem chiSq_nonneg {nu lam : S → ℝ} (hlam : ∀ x, 0 < lam x) : 0 ≤ chiSq nu lam :=
  sum_nonneg fun x _ => div_nonneg (sq_nonneg _) (hlam x).le

/-- **`lem:record:root-marginal`(i), the abstract step.** If `ν ∝ 𝔑 λ` and the count `𝔑` takes
its values in `[c, R c]` with `c > 0`, then the density `𝔑 / E_λ 𝔑` lies in `[R⁻¹, R]`, and its
value at any point is at most `R` times its value at any other point. -/
theorem chiSq_density_range_of_counts {lam N : S → ℝ} (hlam0 : ∀ x, 0 ≤ lam x)
    (hlam1 : ∑ x, lam x = 1) {c R : ℝ} (hc : 0 < c) (hlo : ∀ x, c ≤ N x)
    (hhi : ∀ x, N x ≤ R * c) :
    (∀ x, R⁻¹ ≤ N x / ∑ y, lam y * N y ∧ N x / ∑ y, lam y * N y ≤ R) ∧
      ∀ x y, N x / ∑ z, lam z * N z ≤ R * (N y / ∑ z, lam z * N z) := by
  have hmlo : c ≤ ∑ y, lam y * N y := by
    calc c = ∑ y, lam y * c := by rw [← sum_mul, hlam1, one_mul]
      _ ≤ ∑ y, lam y * N y := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hlo y) (hlam0 y)
  have hmhi : ∑ y, lam y * N y ≤ R * c := by
    calc ∑ y, lam y * N y ≤ ∑ y, lam y * (R * c) :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hhi y) (hlam0 y)
      _ = R * c := by rw [← sum_mul, hlam1, one_mul]
  set m := ∑ y, lam y * N y with hm
  have hm0 : 0 < m := lt_of_lt_of_le hc hmlo
  have hRc : 0 < R * c := lt_of_lt_of_le hm0 hmhi
  have hR : 0 < R := pos_of_mul_pos_left hRc hc.le
  refine ⟨fun x => ⟨?_, ?_⟩, fun x y => ?_⟩
  · rw [le_div_iff₀ hm0, inv_mul_eq_div, div_le_iff₀ hR]
    calc m ≤ R * c := hmhi
      _ ≤ R * N x := mul_le_mul_of_nonneg_left (hlo x) hR.le
      _ = N x * R := mul_comm _ _
  · rw [div_le_iff₀ hm0]
    calc N x ≤ R * c := hhi x
      _ ≤ R * m := mul_le_mul_of_nonneg_left hmlo hR.le
  · rw [mul_div_assoc', div_le_div_iff_of_pos_right hm0]
    calc N x ≤ R * c := hhi x
      _ ≤ R * N y := mul_le_mul_of_nonneg_left (hlo y) hR.le

/-- **`lem:record:root-marginal`(ii), first bound.** A density `g = ν/λ` with values in
`[R⁻¹, R]` satisfies `E_λ (g - R⁻¹)(R - g) ≥ 0`, i.e. `E_λ g² ≤ R + R⁻¹ - 1`; hence
`χ²(ν ‖ λ) ≤ (R - 1)²/R`. -/
theorem chiSq_le_of_density_range {nu lam : S → ℝ} (hlam : ∀ x, 0 < lam x)
    (hnu1 : ∑ x, nu x = 1) (hlam1 : ∑ x, lam x = 1) {R : ℝ} (hR : 0 < R)
    (hlo : ∀ x, R⁻¹ ≤ nu x / lam x) (hhi : ∀ x, nu x / lam x ≤ R) :
    chiSq nu lam ≤ (R - 1) ^ 2 / R := by
  have hg : ∀ x, lam x * (nu x / lam x) = nu x := fun x => by
    have := (hlam x).ne'
    field_simp
  have hg2 : ∀ x, lam x * (nu x / lam x) ^ 2 = nu x ^ 2 / lam x := fun x => by
    have := (hlam x).ne'
    field_simp
  have hpos : 0 ≤ ∑ x, lam x * ((nu x / lam x - R⁻¹) * (R - nu x / lam x)) :=
    sum_nonneg fun x _ => mul_nonneg (hlam x).le
      (mul_nonneg (sub_nonneg.mpr (hlo x)) (sub_nonneg.mpr (hhi x)))
  have hexp : ∑ x, lam x * ((nu x / lam x - R⁻¹) * (R - nu x / lam x)) =
      (R + R⁻¹) * ∑ x, lam x * (nu x / lam x) - ∑ x, lam x * (nu x / lam x) ^ 2 -
        ∑ x, lam x := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    have : R⁻¹ * R = 1 := inv_mul_cancel₀ hR.ne'
    linear_combination (-(lam x)) * this
  simp_rw [hg, hg2] at hexp
  rw [hnu1, hlam1] at hexp
  rw [chiSq_eq hlam hnu1 hlam1]
  have hR' : (R - 1) ^ 2 / R = R + R⁻¹ - 2 := by
    field_simp
    ring
  rw [hR']
  linarith

/-- **`lem:record:root-marginal`(ii), second bound, the last step.** For `ς` with
`E_λ (ς - 1)² ≤ D²` and `E_λ ς ≥ L > 0`, the law `ν = ς λ / E_λ ς` has
`χ²(ν ‖ λ) = Var_λ(ς)/(E_λ ς)² ≤ E_λ (ς - 1)²/(E_λ ς)² ≤ D²/L²`. -/
theorem chiSq_le_of_sq_dev {lam s : S → ℝ} (hlam : ∀ x, 0 < lam x) (hlam1 : ∑ x, lam x = 1)
    {D L : ℝ} (hL : 0 < L) (hmean : L ≤ ∑ x, lam x * s x)
    (hdev : ∑ x, lam x * (s x - 1) ^ 2 ≤ D ^ 2) :
    chiSq (fun x => lam x * s x / ∑ y, lam y * s y) lam ≤ D ^ 2 / L ^ 2 := by
  set m := ∑ y, lam y * s y with hm
  have hm0 : 0 < m := lt_of_lt_of_le hL hmean
  rw [chiSq_eq_density hlam]
  have h1 : ∀ x, lam x * ((lam x * s x / m) / lam x - 1) ^ 2 =
      lam x * (s x - m) ^ 2 / m ^ 2 := fun x => by
    have := (hlam x).ne'
    field_simp
  simp_rw [h1]
  rw [← sum_div]
  -- `E (ς - m)² = E (ς - 1)² - (m - 1)²`
  have hvar : ∑ x, lam x * (s x - m) ^ 2 = ∑ x, lam x * (s x - 1) ^ 2 - (m - 1) ^ 2 := by
    have e1 : ∑ x, lam x * (s x - m) ^ 2 =
        ∑ x, lam x * (s x - 1) ^ 2 - 2 * (m - 1) * ∑ x, lam x * s x +
          (m ^ 2 - 1) * ∑ x, lam x := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro x _
      ring
    rw [e1, ← hm, hlam1]
    ring
  have hnum : ∑ x, lam x * (s x - m) ^ 2 ≤ D ^ 2 := by
    rw [hvar]
    nlinarith [sq_nonneg (m - 1)]
  have hnum0 : 0 ≤ ∑ x, lam x * (s x - m) ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (hlam x).le (sq_nonneg _)
  calc (∑ x, lam x * (s x - m) ^ 2) / m ^ 2 ≤ D ^ 2 / m ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg m)
    _ ≤ D ^ 2 / L ^ 2 := by
        apply div_le_div_of_nonneg_left (le_trans hnum0 hnum) (pow_pos hL 2)
        exact pow_le_pow_left₀ hL.le hmean 2

end Single

section Product

variable {I : Type*} [Fintype I] [DecidableEq I] {S : I → Type*} [∀ i, Fintype (S i)]

/-- The product weight `(⊗ w)(x) = ∏ᵢ wᵢ(xᵢ)` on `∏ᵢ Sᵢ`. -/
noncomputable def prodWeight (w : ∀ i, S i → ℝ) (x : ∀ i, S i) : ℝ := ∏ i, w i (x i)

theorem chiSq_sum_prodWeight (w : ∀ i, S i → ℝ) :
    ∑ x, prodWeight w x = ∏ i, ∑ y, w i y := by
  rw [Fintype.prod_sum]
  rfl

omit [DecidableEq I] [∀ i, Fintype (S i)] in
theorem chiSq_prodWeight_pos {w : ∀ i, S i → ℝ} (hw : ∀ i y, 0 < w i y) (x : ∀ i, S i) :
    0 < prodWeight w x :=
  prod_pos fun i _ => hw i (x i)

/-- **`lem:record:root-marginal`(iii), the product identity**:
`1 + χ²(⊗ν ‖ ⊗λ) = ∏ᵢ (1 + χ²(νᵢ ‖ λᵢ))` for laws of total one with `λᵢ > 0`. -/
theorem chiSq_prod {nu lam : ∀ i, S i → ℝ} (hlam : ∀ i y, 0 < lam i y)
    (hnu1 : ∀ i, ∑ y, nu i y = 1) (hlam1 : ∀ i, ∑ y, lam i y = 1) :
    1 + chiSq (prodWeight nu) (prodWeight lam) = ∏ i, (1 + chiSq (nu i) (lam i)) := by
  have hN : ∑ x, prodWeight nu x = 1 := by
    rw [chiSq_sum_prodWeight]
    exact prod_eq_one fun i _ => hnu1 i
  have hL : ∑ x, prodWeight lam x = 1 := by
    rw [chiSq_sum_prodWeight]
    exact prod_eq_one fun i _ => hlam1 i
  rw [chiSq_eq (chiSq_prodWeight_pos hlam) hN hL]
  have hfac : ∀ i, 1 + chiSq (nu i) (lam i) = ∑ y, nu i y ^ 2 / lam i y := fun i => by
    rw [chiSq_eq (hlam i) (hnu1 i) (hlam1 i)]
    ring
  simp_rw [hfac]
  rw [Fintype.prod_sum]
  have hterm : ∀ x : ∀ i, S i, prodWeight nu x ^ 2 / prodWeight lam x =
      ∏ i, nu i (x i) ^ 2 / lam i (x i) := fun x => by
    unfold prodWeight
    rw [← prod_pow, ← prod_div_distrib]
  simp_rw [hterm]
  ring

omit [DecidableEq I] [∀ i, Fintype (S i)] in
/-- **The product density is the product of the densities**:
`d(⊗ν)/d(⊗λ) = ∏ᵢ dνᵢ/dλᵢ`. -/
theorem chiSq_prodWeight_density (nu lam : ∀ i, S i → ℝ) (x : ∀ i, S i) :
    prodWeight nu x / prodWeight lam x = ∏ i, nu i (x i) / lam i (x i) := by
  unfold prodWeight
  rw [prod_div_distrib]

omit [DecidableEq I] [∀ i, Fintype (S i)] in
/-- Ranges multiply: if every factor density lies in `[Rᵢ⁻¹, Rᵢ]`, the product density lies in
`[(∏ Rᵢ)⁻¹, ∏ Rᵢ]`. -/
theorem chiSq_prod_density_range {nu lam : ∀ i, S i → ℝ} {R : I → ℝ} (hR : ∀ i, 0 < R i)
    (hlo : ∀ i y, (R i)⁻¹ ≤ nu i y / lam i y) (hhi : ∀ i y, nu i y / lam i y ≤ R i)
    (x : ∀ i, S i) :
    (∏ i, R i)⁻¹ ≤ prodWeight nu x / prodWeight lam x ∧
      prodWeight nu x / prodWeight lam x ≤ ∏ i, R i := by
  rw [chiSq_prodWeight_density]
  refine ⟨?_, ?_⟩
  · rw [← prod_inv_distrib]
    exact prod_le_prod₀ (fun i _ => (inv_pos.mpr (hR i)).le) fun i _ => hlo i (x i)
  · exact prod_le_prod₀ (fun i _ => (inv_pos.mpr (hR i)).le.trans (hlo i (x i)))
      fun i _ => hhi i (x i)

omit [DecidableEq I] in
/-- `∏ᵢ aᵢ ≤ Āⁿ` for at most `n` factors with `1 ≤ aᵢ ≤ Ā` and `1 ≤ Ā`. -/
theorem prod_le_pow_of_le {a : I → ℝ} {A : ℝ} {n : ℕ} (h1 : ∀ i, 1 ≤ a i) (hA : ∀ i, a i ≤ A)
    (hA1 : 1 ≤ A) (hn : Fintype.card I ≤ n) : ∏ i, a i ≤ A ^ n := by
  calc ∏ i, a i ≤ ∏ _i : I, A :=
        prod_le_prod₀ (fun i _ => zero_le_one.trans (h1 i)) fun i _ => hA i
    _ = A ^ Fintype.card I := by rw [prod_const, card_univ]
    _ ≤ A ^ n := pow_le_pow_right₀ hA1 hn

omit [DecidableEq I] in
/-- **`lem:record:root-marginal`(iii), the bounds**: if `0 ≤ χᵢ ≤ χ̄` for at most `n` factors,
then `∏ (1 + χᵢ) - 1 ≤ (1 + χ̄)ⁿ - 1`. -/
theorem chiSq_prod_le_pow {χ : I → ℝ} {χbar : ℝ} {n : ℕ} (h0 : ∀ i, 0 ≤ χ i)
    (hle : ∀ i, χ i ≤ χbar) (hbar : 0 ≤ χbar) (hn : Fintype.card I ≤ n) :
    ∏ i, (1 + χ i) - 1 ≤ (1 + χbar) ^ n - 1 := by
  have := prod_le_pow_of_le (a := fun i => 1 + χ i) (A := 1 + χbar)
    (fun i => by linarith [h0 i]) (fun i => by linarith [hle i]) (by linarith) hn
  linarith

end Product

end Sarkozy.Variance
