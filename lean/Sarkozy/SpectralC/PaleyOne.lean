module

public import Sarkozy.SpectralC.PaleyStars
public import Sarkozy.Labellings.Extension

@[expose] public section

/-!
# Class-one Paley terms (`lem:spec2:paley-one`, `lem:spec2:parity-transfer`)

`paper/sections/14_spectral.tex`, `subsec:advance:parity`. The two estimates of the proofs:

* `isolated_vertex_avg` (proof of `lem:spec2:paley-one`): if `j ∈ J` is isolated in `G⁺[J]`, then
  under the uniform completion `x_j` is uniform on the `p − m` values outside the other labels
  `X` (`|X| = m = |J| − 1`), and by the two-root identity `eq:two-root`
  (`Sarkozy.Labellings.two_root`) the average of `S_J` over these values is at most
  `(m + 1)/(p − m)` in modulus;
* `density_transfer`: a density ratio `w/E w ∈ [1/R, R]` changes the mean of `|S| ≤ r` by at
  most `(R − 1) r`;
* `L2_transfer` (proof of `lem:spec2:parity-transfer`): `|E_{m_p} S − E_μ S| ≤ ‖ϱ − 1‖_μ r` for
  `m_p = ϱ μ` and `|S| ≤ r` (Cauchy–Schwarz).

`paley_one_bound` and `parity_transfer_bound` combine them. The law of `x_J` under `ν` is taken
as the hypothesis of `lem:graphs:vertex`(subset) (a density `w` with respect to `u_cons`, ratio at
most `R`), and the conditional law of `x_j` under `u_cons` as uniform on the unused values; both
are stated explicitly.

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- The two-root identity, complex form: `∑_t χ((a − t)(b − t)) = −1` for `a ≠ b`. -/
lemma sum_chiC_two_root (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    ∑ t, chiC p (a - t) * chiC p (b - t) = -1 := by
  have h := Sarkozy.Labellings.two_root (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n]) hab
  unfold Sarkozy.Labellings.rootSum at h
  have h2 : ∑ t : ZMod p, chiC p (a - t) * chiC p (b - t) =
      ((∑ t : ZMod p, quadraticChar (ZMod p) (∏ c ∈ ({a, b} : Finset (ZMod p)), (t - c)) : ℤ) : ℂ) := by
    push_cast
    apply sum_congr rfl
    intro t _
    rw [prod_pair hab, ← map_mul, chiC_apply]
    congr 2
    ring
  rw [h2, h]
  simp

/-- **The isolated-vertex average** (proof of `lem:spec2:paley-one`): for `|g| ≤ 1` and a set `X`
of `m < p` excluded values, with `S(t) = E_{a,b} χ(b − a) χ(a − t) χ(b − t) g(a) g(b)`,
`|∑_{t ∉ X} S(t)| ≤ m + 1`; so the average over the `p − m` values `t ∉ X` is at most
`(m + 1)/(p − m)`. -/
theorem isolated_vertex_avg (hp2 : p ≠ 2) (g : ZMod p → ℂ) (hg : ∀ a, ‖g a‖ ≤ 1)
    (X : Finset (ZMod p)) :
    ‖∑ t ∈ univ \ X, (p : ℂ)⁻¹ * (p : ℂ)⁻¹ *
        ∑ a, ∑ b, chiC p (b - a) * chiC p (a - t) * chiC p (b - t) * conj (g a) * g b‖ ≤
      (X.card : ℝ) + 1 := by
  -- exchange the sums
  have hex : ∑ t ∈ univ \ X, (p : ℂ)⁻¹ * (p : ℂ)⁻¹ *
      ∑ a, ∑ b, chiC p (b - a) * chiC p (a - t) * chiC p (b - t) * conj (g a) * g b =
      (p : ℂ)⁻¹ * (p : ℂ)⁻¹ * ∑ a, ∑ b, chiC p (b - a) * conj (g a) * g b *
        ∑ t ∈ univ \ X, chiC p (a - t) * chiC p (b - t) := by
    rw [← mul_sum]
    congr 1
    rw [sum_comm]
    apply sum_congr rfl; intro a _
    rw [sum_comm]
    apply sum_congr rfl; intro b _
    rw [mul_sum]
    apply sum_congr rfl; intro t _
    ring
  rw [hex]
  -- the inner sums
  have hin : ∀ a b, ‖chiC p (b - a) * conj (g a) * g b *
      ∑ t ∈ univ \ X, chiC p (a - t) * chiC p (b - t)‖ ≤ (X.card : ℝ) + 1 := by
    intro a b
    by_cases hab : a = b
    · rw [hab, sub_self, chiC_zero]; simp; positivity
    · have hsplit : ∑ t ∈ univ \ X, chiC p (a - t) * chiC p (b - t) =
          -1 - ∑ t ∈ X, chiC p (a - t) * chiC p (b - t) := by
        rw [← sum_chiC_two_root hp2 hab, ← sum_sdiff (subset_univ X)]
        ring
      have hX : ‖∑ t ∈ X, chiC p (a - t) * chiC p (b - t)‖ ≤ X.card := by
        refine (norm_sum_le _ _).trans ?_
        have : ∀ t ∈ X, ‖chiC p (a - t) * chiC p (b - t)‖ ≤ 1 := by
          intro t _
          rw [norm_mul]
          have h1 : ‖chiC p (a - t)‖ ≤ 1 := by
            by_cases h : a - t = 0
            · rw [h, chiC_zero, norm_zero]; exact zero_le_one
            · rw [norm_chiC h]
          have h2 : ‖chiC p (b - t)‖ ≤ 1 := by
            by_cases h : b - t = 0
            · rw [h, chiC_zero, norm_zero]; exact zero_le_one
            · rw [norm_chiC h]
          nlinarith [norm_nonneg (chiC p (a - t)), norm_nonneg (chiC p (b - t))]
        calc ∑ t ∈ X, ‖chiC p (a - t) * chiC p (b - t)‖ ≤ ∑ _t ∈ X, (1 : ℝ) := sum_le_sum this
          _ = X.card := by simp
      have hd : b - a ≠ 0 := fun h => hab (sub_eq_zero.mp h).symm
      rw [norm_mul, norm_mul, norm_mul, norm_chiC hd, hsplit, Complex.norm_conj]
      have hg1 := hg a
      have hg2 := hg b
      have hn : ‖-1 - ∑ t ∈ X, chiC p (a - t) * chiC p (b - t)‖ ≤ X.card + 1 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg, norm_one]
        linarith
      calc 1 * ‖g a‖ * ‖g b‖ * ‖-1 - ∑ t ∈ X, chiC p (a - t) * chiC p (b - t)‖
          ≤ 1 * 1 * 1 * ((X.card : ℝ) + 1) := by
            apply mul_le_mul _ hn (norm_nonneg _) (by positivity)
            apply mul_le_mul _ hg2 (norm_nonneg _) (by positivity)
            linarith
        _ = (X.card : ℝ) + 1 := by ring
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  calc (p : ℝ)⁻¹ * (p : ℝ)⁻¹ * ‖∑ a, ∑ b, chiC p (b - a) * conj (g a) * g b *
        ∑ t ∈ univ \ X, chiC p (a - t) * chiC p (b - t)‖
      ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ * ∑ _a : ZMod p, ∑ _b : ZMod p, ((X.card : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (norm_sum_le _ _).trans ?_
        apply sum_le_sum; intro a _
        refine (norm_sum_le _ _).trans ?_
        apply sum_le_sum; intro b _
        exact hin a b
    _ = (X.card : ℝ) + 1 := by
        simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
        field_simp

/-- **Density transfer** (proof of `lem:spec2:paley-one`): if `R⁻¹ u ≤ ρ ≤ R u` (the density
`w/E_u w` of `ρ` with respect to `u` lies in `[1/R, R]`) and `|S| ≤ r`, then
`|E_ρ S − E_u S| ≤ (R − 1) r`. -/
theorem density_transfer {Ω : Type*} [Fintype Ω] (u ρ : Ω → ℝ) (S : Ω → ℂ) {R r : ℝ}
    (hR : 1 ≤ R) (hu : ∀ x, 0 ≤ u x) (hu1 : ∑ x, u x = 1)
    (hρ : ∀ x, R⁻¹ * u x ≤ ρ x ∧ ρ x ≤ R * u x) (hS : ∀ x, ‖S x‖ ≤ r) :
    ‖∑ x, (ρ x : ℂ) * S x - ∑ x, (u x : ℂ) * S x‖ ≤ (R - 1) * r := by
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := u)
    (by rw [hu1]; exact one_ne_zero)
  have hr : 0 ≤ r := (norm_nonneg _).trans (hS x₀)
  have hR0 : 0 < R := by linarith
  have hdev : ∀ x, |ρ x - u x| ≤ (R - 1) * u x := by
    intro x
    obtain ⟨h1, h2⟩ := hρ x
    have hux := hu x
    have h3 : (1 - R⁻¹) * u x ≤ (R - 1) * u x := by
      apply mul_le_mul_of_nonneg_right _ hux
      have hinv1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
      have hprod : 0 ≤ (R - 1) * (1 - R⁻¹) := mul_nonneg (by linarith) (by linarith)
      have e : (R - 1) * (1 - R⁻¹) = R + R⁻¹ - 2 := by
        field_simp
        ring
      linarith
    rw [abs_le]
    constructor <;> nlinarith
  rw [← sum_sub_distrib]
  calc ‖∑ x, ((ρ x : ℂ) * S x - (u x : ℂ) * S x)‖
      ≤ ∑ x, |ρ x - u x| * ‖S x‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        apply sum_congr rfl; intro x _
        rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ x, ((R - 1) * u x) * r := by
        apply sum_le_sum; intro x _
        exact mul_le_mul (hdev x) (hS x) (norm_nonneg _) (by have := hu x; nlinarith)
    _ = (R - 1) * r := by
        rw [← sum_mul, ← mul_sum, hu1, mul_one]

/-- **The `L²` transfer** (proof of `lem:spec2:parity-transfer`): for `m_p = ϱ μ` and `|S| ≤ r`,
`|E_{m_p} S − E_μ S| = |E_μ[(ϱ − 1) S]| ≤ ‖ϱ − 1‖_μ r`. -/
theorem L2_transfer {Ω : Type*} [Fintype Ω] (μ ϱ : Ω → ℝ) (S : Ω → ℂ) {r : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hS : ∀ x, ‖S x‖ ≤ r) :
    ‖∑ x, ((μ x * ϱ x : ℝ) : ℂ) * S x - ∑ x, (μ x : ℂ) * S x‖ ≤
      Real.sqrt (∑ x, μ x * (ϱ x - 1) ^ 2) * r := by
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := μ)
    (by rw [hμ1]; exact one_ne_zero)
  have hr : 0 ≤ r := (norm_nonneg _).trans (hS x₀)
  rw [← sum_sub_distrib]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun x => Real.sqrt (μ x) * |ϱ x - 1|)
    (fun x => Real.sqrt (μ x) * ‖S x‖)
  have h1 : ∀ x, (Real.sqrt (μ x) * |ϱ x - 1|) ^ 2 = μ x * (ϱ x - 1) ^ 2 := by
    intro x; rw [mul_pow, Real.sq_sqrt (hμ x), sq_abs]
  have h2 : ∀ x, (Real.sqrt (μ x) * ‖S x‖) ^ 2 ≤ μ x * r ^ 2 := by
    intro x
    rw [mul_pow, Real.sq_sqrt (hμ x)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hS x) 2) (hμ x)
  simp only [h1] at hcs
  have h3 : Real.sqrt (∑ x, (Real.sqrt (μ x) * ‖S x‖) ^ 2) ≤ r := by
    calc Real.sqrt (∑ x, (Real.sqrt (μ x) * ‖S x‖) ^ 2) ≤ Real.sqrt (∑ x, μ x * r ^ 2) :=
          Real.sqrt_le_sqrt (sum_le_sum fun x _ => h2 x)
      _ = r := by rw [← sum_mul, hμ1, one_mul, Real.sqrt_sq hr]
  calc ‖∑ x, (((μ x * ϱ x : ℝ) : ℂ) * S x - (μ x : ℂ) * S x)‖
      ≤ ∑ x, Real.sqrt (μ x) * |ϱ x - 1| * (Real.sqrt (μ x) * ‖S x‖) := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        apply sum_congr rfl; intro x _
        rw [show ((μ x * ϱ x : ℝ) : ℂ) * S x - (μ x : ℂ) * S x =
          ((μ x * (ϱ x - 1) : ℝ) : ℂ) * S x by push_cast; ring]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hμ x),
          show Real.sqrt (μ x) * |ϱ x - 1| * (Real.sqrt (μ x) * ‖S x‖) =
            (Real.sqrt (μ x) * Real.sqrt (μ x)) * |ϱ x - 1| * ‖S x‖ by ring,
          Real.mul_self_sqrt (hμ x)]
    _ ≤ Real.sqrt (∑ x, μ x * (ϱ x - 1) ^ 2) * Real.sqrt (∑ x, (Real.sqrt (μ x) * ‖S x‖) ^ 2) :=
        hcs
    _ ≤ Real.sqrt (∑ x, μ x * (ϱ x - 1) ^ 2) * r :=
        mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)

/-! ## The class-one bounds -/

/-- `|⟨f, Cf⟩| ≤ r` for `|f| ≤ 1`. -/
lemma norm_ip_gaussOp_le (hp2 : p ≠ 2) (f : ZMod p → ℂ) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖ip f (gaussOp f)‖ ≤ rp p := by
  have hg : l2sq f ≤ 1 := by
    unfold l2sq
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    calc (p : ℝ)⁻¹ * ∑ a, ‖f a‖ ^ 2 ≤ (p : ℝ)⁻¹ * ∑ _a : ZMod p, (1 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_le_sum; intro a _
          have := hf a
          nlinarith [norm_nonneg (f a)]
      _ = 1 := by
          rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
          exact inv_mul_cancel₀ hp.ne'
  have hC := l2sq_gaussOp_le hp2 f
  have hr : 0 ≤ rp p := by unfold rp; positivity
  have hsq : Real.sqrt (l2sq (gaussOp f)) ≤ rp p * Real.sqrt (l2sq f) := by
    rw [← Real.sqrt_sq hr, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hC
  have h0 := l2sq_nonneg f
  calc ‖ip f (gaussOp f)‖ ≤ Real.sqrt (l2sq f) * Real.sqrt (l2sq (gaussOp f)) := norm_ip_le _ _
    _ ≤ Real.sqrt (l2sq f) * (rp p * Real.sqrt (l2sq f)) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    _ = rp p * l2sq f := by rw [mul_left_comm, Real.mul_self_sqrt h0]
    _ ≤ rp p * 1 := mul_le_mul_of_nonneg_left hg hr
    _ = rp p := mul_one _

/-- `S_J` with the isolated label `t`: `S(y, t) = ⟨χ(· − t) g_y, C(χ(· − t) g_y)⟩`. -/
noncomputable def isoS (g : ZMod p → ℂ) (t : ZMod p) : ℂ :=
  ip (fun a => chiC p (a - t) * g a) (gaussOp (fun a => chiC p (a - t) * g a))

lemma isoS_eq (g : ZMod p → ℂ) (t : ZMod p) :
    isoS g t = (p : ℂ)⁻¹ * (p : ℂ)⁻¹ *
      ∑ a, ∑ b, chiC p (b - a) * chiC p (a - t) * chiC p (b - t) * conj (g a) * g b := by
  unfold isoS ip gaussOp
  simp only [mul_sum]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  rw [map_mul, conj_chiC]
  ring

/-- **`lem:spec2:paley-one`, the isolated-vertex bound.** Let `j ∈ J` be isolated in `G⁺[J]`, with
`y` the labels of `J ∖ {j}` and `g_y = g_{J∖{j}}(·; y)` (`|g_y| ≤ 1`), so that
`S_J = isoS g_y x_j`. Let `u_cons(y, t) = u'(y) [t ∉ X(y)]/(p − m)` (given `y`, `x_j` is uniform
on the `p − m` unused values, `|X(y)| = m`), and let the law `ρ` of `x_J` under `ν` satisfy
`R⁻¹ u_cons ≤ ρ ≤ R u_cons` (`lem:graphs:vertex`(subset) with the density bound (i) of the
coupling data, `R = R_ν R_full`). Then `|t_J| = |E_ρ S_J| ≤ (R − 1) r + (m + 1)/(p − m)`. -/
theorem paley_one_bound (hp2 : p ≠ 2) {Y : Type*} [Fintype Y] (u' : Y → ℝ)
    (hu' : ∀ y, 0 ≤ u' y) (hu'1 : ∑ y, u' y = 1) (X : Y → Finset (ZMod p)) (m : ℕ)
    (hX : ∀ y, (X y).card = m) (hm : m < p) (g : Y → ZMod p → ℂ) (hg : ∀ y a, ‖g y a‖ ≤ 1)
    (ρ : Y × ZMod p → ℝ) {R : ℝ} (hR : 1 ≤ R)
    (hρ : ∀ z : Y × ZMod p,
      R⁻¹ * (u' z.1 * (if z.2 ∉ X z.1 then ((p : ℝ) - m)⁻¹ else 0)) ≤ ρ z ∧
        ρ z ≤ R * (u' z.1 * (if z.2 ∉ X z.1 then ((p : ℝ) - m)⁻¹ else 0))) :
    ‖∑ z, (ρ z : ℂ) * isoS (g z.1) z.2‖ ≤ (R - 1) * rp p + ((m : ℝ) + 1) / ((p : ℝ) - m) := by
  have hpm : (0 : ℝ) < (p : ℝ) - m := by
    have : (m : ℝ) < p := by exact_mod_cast hm
    linarith
  set u : Y × ZMod p → ℝ := fun z => u' z.1 * (if z.2 ∉ X z.1 then ((p : ℝ) - m)⁻¹ else 0)
    with hudef
  have hu0 : ∀ z, 0 ≤ u z := by
    intro z
    simp only [hudef]
    apply mul_nonneg (hu' z.1)
    split_ifs <;> positivity
  have hu1 : ∑ z, u z = 1 := by
    simp only [hudef]
    rw [Fintype.sum_prod_type]
    have h1 : ∀ y, ∑ t, u' y * (if t ∉ X y then ((p : ℝ) - m)⁻¹ else 0) = u' y := by
      intro y
      rw [← mul_sum]
      have hf : univ.filter (fun t => t ∉ X y) = univ \ X y := by ext t; simp
      have h2 : ∑ t, (if t ∉ X y then ((p : ℝ) - m)⁻¹ else 0) =
          ((univ \ X y).card : ℝ) * ((p : ℝ) - m)⁻¹ := by
        rw [← sum_filter, sum_const, nsmul_eq_mul, hf]
      rw [h2, card_univ_sdiff, ZMod.card, hX y]
      rw [Nat.cast_sub hm.le]
      field_simp
    simp_rw [h1]
    exact hu'1
  have hS : ∀ z : Y × ZMod p, ‖isoS (g z.1) z.2‖ ≤ rp p := by
    intro z
    apply norm_ip_gaussOp_le hp2
    intro a
    rw [norm_mul]
    have h1 : ‖chiC p (a - z.2)‖ ≤ 1 := by
      by_cases h : a - z.2 = 0
      · rw [h, chiC_zero, norm_zero]; exact zero_le_one
      · rw [norm_chiC h]
    have := hg z.1 a
    nlinarith [norm_nonneg (chiC p (a - z.2)), norm_nonneg (g z.1 a)]
  have htr := density_transfer u ρ (fun z => isoS (g z.1) z.2) hR hu0 hu1 hρ hS
  -- the uniform completion
  have hucons : ‖∑ z, (u z : ℂ) * isoS (g z.1) z.2‖ ≤ ((m : ℝ) + 1) / ((p : ℝ) - m) := by
    simp only [hudef]
    rw [Fintype.sum_prod_type]
    have h1 : ∀ y, ∑ t, ((u' y * (if t ∉ X y then ((p : ℝ) - m)⁻¹ else 0) : ℝ) : ℂ) *
        isoS (g y) t = (u' y : ℂ) * ((((p : ℝ) - m)⁻¹ : ℝ) : ℂ) *
          ∑ t ∈ univ \ X y, isoS (g y) t := by
      intro y
      rw [mul_sum, ← sum_filter_add_sum_filter_not univ (fun t => t ∉ X y)]
      have h0 : ∑ t ∈ univ.filter (fun t => ¬ t ∉ X y),
          ((u' y * (if t ∉ X y then ((p : ℝ) - m)⁻¹ else 0) : ℝ) : ℂ) * isoS (g y) t = 0 := by
        apply sum_eq_zero; intro t ht
        rw [mem_filter] at ht
        rw [ite_eq_right ht.2]; simp
      rw [h0, add_zero]
      have hf : univ.filter (fun t => t ∉ X y) = univ \ X y := by ext t; simp
      rw [hf]
      apply sum_congr rfl; intro t ht
      rw [mem_sdiff] at ht
      rw [ite_eq_left ht.2]
      push_cast
      ring
    simp_rw [h1]
    calc ‖∑ y, (u' y : ℂ) * ((((p : ℝ) - m)⁻¹ : ℝ) : ℂ) * ∑ t ∈ univ \ X y, isoS (g y) t‖
        ≤ ∑ y, u' y * (((p : ℝ) - m)⁻¹ * ((m : ℝ) + 1)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun y _ => ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (hu' y), Real.norm_of_nonneg (by positivity)]
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (hu' y)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := isolated_vertex_avg hp2 (g y) (hg y) (X y)
          simp_rw [← isoS_eq] at this
          rw [hX y] at this
          exact this
      _ = ((m : ℝ) + 1) / ((p : ℝ) - m) := by
          rw [← sum_mul, hu'1, one_mul, div_eq_inv_mul]
  calc ‖∑ z, (ρ z : ℂ) * isoS (g z.1) z.2‖
      ≤ ‖∑ z, (ρ z : ℂ) * isoS (g z.1) z.2 - ∑ z, (u z : ℂ) * isoS (g z.1) z.2‖ +
          ‖∑ z, (u z : ℂ) * isoS (g z.1) z.2‖ := by
        have := norm_add_le (∑ z, (ρ z : ℂ) * isoS (g z.1) z.2 -
          ∑ z, (u z : ℂ) * isoS (g z.1) z.2) (∑ z, (u z : ℂ) * isoS (g z.1) z.2)
        rwa [sub_add_cancel] at this
    _ ≤ (R - 1) * rp p + ((m : ℝ) + 1) / ((p : ℝ) - m) := add_le_add htr hucons

/-- **`lem:spec2:parity-transfer`.** In instance (A), `t_J = E_{m_p} S_J` with `m_p = ϱ μ`. If
`|S_J| ≤ r`, `‖ϱ − 1‖_μ ≤ ε_ϱ` and the isolated-vertex bound for `ν = μ` holds,
`|E_μ S_J| ≤ (R_full − 1 + n/((p − n) r)) r` (`paley_one_bound` with `R = R_full`), then
`|t_J|/r ≤ R_full − 1 + n/((p − n) r) + ε_ϱ`. -/
theorem parity_transfer_bound {Ω : Type*} [Fintype Ω] (μ ϱ : Ω → ℝ) (S : Ω → ℂ)
    {r B ε : ℝ} (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hS : ∀ x, ‖S x‖ ≤ r)
    (hϱ : Real.sqrt (∑ x, μ x * (ϱ x - 1) ^ 2) ≤ ε)
    (hB : ‖∑ x, (μ x : ℂ) * S x‖ ≤ B * r) :
    ‖∑ x, ((μ x * ϱ x : ℝ) : ℂ) * S x‖ ≤ (B + ε) * r := by
  obtain ⟨x₀, -, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ) (f := μ)
    (by rw [hμ1]; exact one_ne_zero)
  have hr : 0 ≤ r := (norm_nonneg _).trans (hS x₀)
  have h := L2_transfer μ ϱ S hμ hμ1 hS
  calc ‖∑ x, ((μ x * ϱ x : ℝ) : ℂ) * S x‖
      ≤ ‖∑ x, ((μ x * ϱ x : ℝ) : ℂ) * S x - ∑ x, (μ x : ℂ) * S x‖ +
          ‖∑ x, (μ x : ℂ) * S x‖ := by
        have := norm_add_le (∑ x, ((μ x * ϱ x : ℝ) : ℂ) * S x - ∑ x, (μ x : ℂ) * S x)
          (∑ x, (μ x : ℂ) * S x)
        rwa [sub_add_cancel] at this
    _ ≤ ε * r + B * r := add_le_add (h.trans (mul_le_mul_of_nonneg_right hϱ hr)) hB
    _ = (B + ε) * r := by ring

end Sarkozy.SpectralC
