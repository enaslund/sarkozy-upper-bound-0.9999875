module

public import Sarkozy.Interpolation.StrongFInputs

/-!
# The sharp `L²` endpoint in class three (`lem:density:strong-F`)

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:strong-F`: "For a strict
Paley edge in class three, centered interpolation at `4/3` gives bilinear norm
`(p+1)^{3/4}/(p−1) ≤ 2p^{-1/4}`."

For `p ≡ 3 (mod 4)` the Paley operator is skew (`TraceMixing.paleyOp_adjoint`), so on mean-zero
functions `‖−g + c p P g‖₂² = (1 + p) ‖g‖₂²`. Hence the centred form of either class law has
`L² × L²` norm at most `√(p+1)/(p−1)` (`class_L2_tournament`), sharper than the general
`(√p+1)/(p−1)` of `class_L2`. With `L = (p+1)/(p−1)`, interpolation at `t = 1/2` gives exactly
the paper's `L^{1/2} ρ^{1/2} = (p+1)^{3/4}/(p−1)` (`class_interp_four_thirds_tournament`), and
`(p+1)^{3/4}/(p−1) ≤ 2p^{-1/4}` for `p ≥ 3` (`tournament_numeric`).

The Lean chain does not need this file: `StrongFInputs.class_interp_four_thirds` already gives
the bound `2p^{-1/4}` from the general `L²` endpoint. This file checks the paper's sentence as
written.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Interpolation

open Sarkozy.InvariantPair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

/-- `∑_a χ(b − a) = 0`. -/
theorem sum_chi_sub_left (hp2 : p ≠ 2) (b : ZMod p) : ∑ a, (χ (b - a) : ℝ) = 0 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := Equiv.sum_comp (Equiv.subLeft b) (fun x => (χ x : ℝ))
  simp only [Equiv.subLeft_apply] at h
  rw [h]
  exact_mod_cast quadraticChar_sum_zero hF

/-- `∑_b χ(b − a) = 0`. -/
theorem sum_chi_sub_right (hp2 : p ≠ 2) (a : ZMod p) : ∑ b, (χ (b - a) : ℝ) = 0 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  exact_mod_cast TraceMixing.sum_chi_shift hF a

/-- **The sharp `L²` endpoint in class three**: for `p ≡ 3 (mod 4)` the centred form of either
class law has `L² × L²` norm at most `√(p+1)/(p−1)`. -/
theorem class_L2_tournament (hp2 : p ≠ 2) (h3 : p % 4 = 3) {c : ℤ} (hc : c = 1 ∨ c = -1)
    (f g : ZMod p → ℝ) :
    |centredForm (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight f g| ≤
      (Real.sqrt ((p : ℝ) + 1) / ((p : ℝ) - 1)) * DensityUpgrade.conditioningNorm 2 f *
        DensityUpgrade.conditioningNorm 2 g := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h3' : Fintype.card (ZMod p) % 4 = 3 := by rw [ZMod.card]; exact h3
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := hp.out.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  rw [class_centredForm hp2 hc, conditioningNorm_two, conditioningNorm_two, ZMod.card]
  set n : ℝ := (p : ℝ) with hn_def
  have hn0 : 0 < n := by linarith
  set mf := (∑ b, f b) / n with hmf
  set mg := (∑ b, g b) / n with hmg
  set f₀ : ZMod p → ℝ := fun a => f a - mf with hf₀
  set g₀ : ZMod p → ℝ := fun a => g a - mg with hg₀
  have hf₀s : ∑ a, f₀ a = 0 := by
    simp only [hf₀, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, hmf]
    field_simp
    ring
  have hg₀s : ∑ a, g₀ a = 0 := by
    simp only [hg₀, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, hmg]
    field_simp
    ring
  -- the operator form `T₀(a) = ∑_b χ(b − a) g₀(b) = n · P g₀ (a)`
  set T₀ : ZMod p → ℝ := fun a => ∑ b, (χ (b - a) : ℝ) * g₀ b with hT₀
  have hT : ∀ a, ∑ b, (χ (b - a) : ℝ) * g b = T₀ a := by
    intro a
    have : ∀ b, (χ (b - a) : ℝ) * g b = (χ (b - a) : ℝ) * g₀ b + mg * (χ (b - a) : ℝ) :=
      fun b => by simp only [hg₀]; ring
    rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_chi_sub_right hp2 a, mul_zero, add_zero]
  have hT₀sum : ∑ a, T₀ a = 0 := by
    simp only [hT₀]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ a, (χ (b - a) : ℝ) * g₀ b = 0 := fun b => by
      rw [← Finset.sum_mul, sum_chi_sub_left hp2 b, zero_mul]
    exact Finset.sum_eq_zero fun b _ => this b
  have hTP : ∀ a, T₀ a = n * TraceMixing.paleyOp g₀ a := by
    intro a
    unfold TraceMixing.paleyOp
    rw [ZMod.card, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
  -- the numerator as `∑ f₀ h`
  set h : ZMod p → ℝ := fun a => -g₀ a + c * T₀ a with hh
  have hnum : -(∑ a, (f a - mf) * g a) + c * ∑ a, f a * ∑ b, (χ (b - a) : ℝ) * g b =
      ∑ a, f₀ a * h a := by
    have e1 : ∑ a, (f a - mf) * g a = ∑ a, f₀ a * g₀ a := by
      have : ∀ a, (f a - mf) * g a = f₀ a * g₀ a + mg * f₀ a := fun a => by
        simp only [hf₀, hg₀]; ring
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, ← Finset.mul_sum,
        hf₀s, mul_zero, add_zero]
    have e2 : ∑ a, f a * ∑ b, (χ (b - a) : ℝ) * g b = ∑ a, f₀ a * T₀ a := by
      have : ∀ a, f a * ∑ b, (χ (b - a) : ℝ) * g b = f₀ a * T₀ a + mf * T₀ a := fun a => by
        rw [hT a]; simp only [hf₀]; ring
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, ← Finset.mul_sum,
        hT₀sum, mul_zero, add_zero]
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hh]
    ring
  -- `∑ h² = (1 + n) ∑ g₀²`
  have hskew : ∑ a, g₀ a * TraceMixing.paleyOp g₀ a = 0 := by
    have := TraceMixing.paleyOp_adjoint h3' g₀ g₀
    have hcomm : ∑ s, TraceMixing.paleyOp g₀ s * g₀ s = ∑ s, g₀ s * TraceMixing.paleyOp g₀ s :=
      Finset.sum_congr rfl fun s _ => mul_comm _ _
    rw [hcomm] at this
    linarith
  have hPsum : ∑ a, TraceMixing.paleyOp g₀ a ^ 2 = n⁻¹ * ∑ a, g₀ a ^ 2 := by
    have h1 := TraceMixing.norm_paleyOp hF g₀
    rw [ZMod.card, hg₀s, mul_zero, zero_pow two_ne_zero, sub_zero] at h1
    exact mul_left_cancel₀ (inv_ne_zero hn0.ne') h1
  have hc2 : (c : ℝ) ^ 2 = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hhsum : ∑ a, h a ^ 2 = (1 + n) * ∑ a, g₀ a ^ 2 := by
    have : ∀ a, h a ^ 2 = g₀ a ^ 2 - 2 * c * n * (g₀ a * TraceMixing.paleyOp g₀ a) +
        (c : ℝ) ^ 2 * n ^ 2 * TraceMixing.paleyOp g₀ a ^ 2 := fun a => by
      simp only [hh, hTP a]; ring
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hskew, hPsum, hc2]
    field_simp
    ring
  -- Cauchy–Schwarz
  set A := ∑ a, f a ^ 2 with hA_def
  set G := ∑ a, g a ^ 2 with hG_def
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hf₀A : ∑ a, f₀ a ^ 2 ≤ A := sum_centred_sq_le (p := p) f
  have hg₀G : ∑ a, g₀ a ^ 2 ≤ G := sum_centred_sq_le (p := p) g
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ f₀ h
  have hsq : (∑ a, f₀ a * h a) ^ 2 ≤ (1 + n) * (A * G) := by
    rw [hhsum] at hcs
    have hg0 : 0 ≤ ∑ a, g₀ a ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hf0 : 0 ≤ ∑ a, f₀ a ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (∑ a, f₀ a * h a) ^ 2 ≤ (∑ a, f₀ a ^ 2) * ((1 + n) * ∑ a, g₀ a ^ 2) := hcs
      _ ≤ A * ((1 + n) * G) := mul_le_mul hf₀A (mul_le_mul_of_nonneg_left hg₀G (by linarith))
          (by positivity) hA
      _ = (1 + n) * (A * G) := by ring
  -- square roots
  set a := Real.sqrt A
  set b := Real.sqrt G
  set s := Real.sqrt n with hs_def
  set q := Real.sqrt (n + 1) with hq_def
  have ha2 : a ^ 2 = A := Real.sq_sqrt hA
  have hb2 : b ^ 2 = G := Real.sq_sqrt hG
  have hs2 : s ^ 2 = n := Real.sq_sqrt hn0.le
  have hq2 : q ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 hn0
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hnumle : |∑ a, f₀ a * h a| ≤ q * (a * b) := by
    have : |∑ a, f₀ a * h a| ^ 2 ≤ (q * (a * b)) ^ 2 := by
      rw [sq_abs, mul_pow, mul_pow, ha2, hb2, hq2, add_comm n 1]
      exact hsq
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp this
  rw [Real.sqrt_div' _ hn0.le, Real.sqrt_div' _ hn0.le, ← hs_def, hnum]
  have hden : 0 < n * (n - 1) := by nlinarith
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  refine hnumle.trans (le_of_eq ?_)
  have hn1 : n - 1 ≠ 0 := by linarith
  rw [← hs2] at hn1 ⊢
  field_simp
  rfl

/-- `(p+1)^{3/4}/(p−1) ≤ 2 p^{-1/4}` for `p ≥ 3`. -/
theorem tournament_numeric {x : ℝ} (hx : 3 ≤ x) :
    (x + 1) ^ (3 / 4 : ℝ) / (x - 1) ≤ 2 * x ^ (-(1 / 4 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  rw [div_le_iff₀ hx1, Real.rpow_neg hx0.le, mul_assoc, mul_comm (x ^ (1 / 4 : ℝ))⁻¹,
    ← div_eq_mul_inv, ← mul_div_assoc, le_div_iff₀ (Real.rpow_pos_of_pos hx0 _)]
  -- `(x+1)^{3/4} x^{1/4} ≤ 2 (x − 1)`, by fourth powers
  have hl : 0 ≤ (x + 1) ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by positivity
  have hr : 0 ≤ 2 * (x - 1) := by linarith
  have h4 : ((x + 1) ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) ^ 4 = (x + 1) ^ 3 * x := by
    rw [mul_pow, ← Real.rpow_natCast ((x + 1) ^ (3 / 4 : ℝ)), ← Real.rpow_natCast (x ^ _),
      ← Real.rpow_mul (by linarith), ← Real.rpow_mul hx0.le]
    norm_num
  have hpoly : (x + 1) ^ 3 * x ≤ (2 * (x - 1)) ^ 4 := by
    have hq : 0 ≤ x - 3 := by linarith
    nlinarith [mul_nonneg hq hq, mul_nonneg (mul_nonneg hq hq) hq,
      mul_nonneg (mul_nonneg (mul_nonneg hq hq) hq) hq]
  have : ((x + 1) ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) ^ 4 ≤ (2 * (x - 1)) ^ 4 := by
    rw [h4]
    exact hpoly
  have hle := (pow_le_pow_iff_left₀ hl hr (by norm_num : (4 : ℕ) ≠ 0)).mp this
  linarith

/-- **`lem:density:strong-F`, the Paley-edge interpolation as written in the paper**: for
`p ≡ 3 (mod 4)`, either class law and mean-zero `f, g`,
`|E f(x₀) g(x₁)| ≤ (p+1)^{3/4}/(p−1) · ‖f‖_{4/3} ‖g‖_{4/3}`, and `(p+1)^{3/4}/(p−1) ≤ 2p^{-1/4}`. -/
theorem class_interp_four_thirds_tournament (hp2 : p ≠ 2) (h3 : p % 4 = 3) {c : ℤ}
    (hc : c = 1 ∨ c = -1) :
    (∀ f g : ZMod p → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight x *
          (f (x 0) * g (x 1))| ≤
        ((p : ℝ) + 1) ^ (3 / 4 : ℝ) / ((p : ℝ) - 1) * DensityUpgrade.conditioningNorm (4 / 3) f *
          DensityUpgrade.conditioningNorm (4 / 3) g) ∧
      ((p : ℝ) + 1) ^ (3 / 4 : ℝ) / ((p : ℝ) - 1) ≤ 2 * (p : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := hp.out.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  refine ⟨fun f g hf _ => ?_, tournament_numeric hp3⟩
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hL : (0 : ℝ) ≤ ((p : ℝ) + 1) / ((p : ℝ) - 1) := div_nonneg (by linarith) hp1.le
  have hρ : (0 : ℝ) ≤ Real.sqrt ((p : ℝ) + 1) / ((p : ℝ) - 1) :=
    div_nonneg (Real.sqrt_nonneg _) hp1.le
  have key := centred_interp _ (t := 1 / 2) (r := 4 / 3) hL hρ (by norm_num) (by norm_num)
    (by norm_num) (class_L1 hp2 hc) (class_L2_tournament hp2 h3 hc) f g
  rw [centredForm_of_mean_zero _ g hf] at key
  have hconst : (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (1 - 1 / 2 : ℝ) *
      (Real.sqrt ((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (1 / 2 : ℝ) =
        ((p : ℝ) + 1) ^ (3 / 4 : ℝ) / ((p : ℝ) - 1) := by
    have hp0 : (0 : ℝ) ≤ (p : ℝ) + 1 := by linarith
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.mul_rpow hL hρ, div_mul_div_comm,
      Real.sqrt_eq_rpow, ← Real.rpow_one_add' hp0 (by norm_num),
      Real.div_rpow (Real.rpow_nonneg hp0 _) (by positivity), ← Real.rpow_mul hp0, ← sq,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hp1.le]
    norm_num
  rwa [hconst] at key

end Sarkozy.Interpolation
