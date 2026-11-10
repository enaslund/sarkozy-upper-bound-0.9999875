module

public import Sarkozy.JointRows.PaleyAllPrimes
public import Sarkozy.DLK.RawPair
public import Sarkozy.Cuts.Swapped
public import Sarkozy.SpectralC.CondExp

/-! Two-label character maps used in coherent covariance products. -/

@[expose] public section

namespace Sarkozy.SpectralC.TwoLabel

open Finset Sarkozy.Cuts
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def fieldLaw (p : ℕ) [Fact p.Prime] : FiniteLaw (ZMod p) :=
  FiniteLaw.uniform (ZMod p)

noncomputable def characterMap (h : ZMod p → ℝ) (a : ZMod p) : ℝ :=
  (fieldLaw p).expect (fun u => chiRe (u - a) * h u)

theorem character_sum_sq_le (hp : p ≠ 2) (h : ZMod p → ℝ) :
    (∑ a, (∑ u, chiRe (u - a) * h u) ^ 2) ≤ (p : ℝ) * ∑ u, h u ^ 2 := by
  have he : ∀ a : ZMod p, (∑ u, chiRe (u - a) * h u) ^ 2 =
      ∑ u, ∑ v, h u * h v * (chiRe (u - a) * chiRe (v - a)) := by
    intro a
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by ring
  simp_rw [he]
  rw [sum_comm]
  have hs : ∀ u : ZMod p, (∑ a, ∑ v, h u * h v * (chiRe (u - a) * chiRe (v - a))) =
      ∑ v, h u * h v * ((p : ℝ) * (if u = v then 1 else 0) - 1) := by
    intro u
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    rw [← mul_sum]
    exact congrArg (h u * h v * ·) (SecondOrder.sum_chi_mul_chi hp u v)
  simp_rw [hs]
  have htotal : (∑ u, ∑ v, h u * h v * ((p : ℝ) * (if u = v then 1 else 0) - 1)) =
      (p : ℝ) * ∑ u, h u ^ 2 - (∑ u, h u) ^ 2 := by
    simp only [mul_sub, mul_one, mul_ite, mul_zero, sum_sub_distrib, sum_ite_eq,
      mem_univ, ite_true]
    rw [sq, sum_mul_sum, mul_sum]
    congr 1
    exact sum_congr rfl fun u _ => by ring
  rw [htotal]
  exact sub_le_self _ (sq_nonneg _)

theorem characterMap_sq (hp : p ≠ 2) (h : ZMod p → ℝ) :
    (fieldLaw p).expect (fun a => characterMap h a ^ 2) ≤
      (p : ℝ)⁻¹ * (fieldLaw p).expect (fun u => h u ^ 2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hsum := character_sum_sq_le hp h
  simp only [characterMap, fieldLaw, FiniteLaw.expect_uniform, ZMod.card]
  simp only [div_pow, ← sum_div]
  calc
    _ ≤ ((p : ℝ) * ∑ u, h u ^ 2) / (p : ℝ) ^ 2 / p :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hsum (sq_nonneg _)) hp0.le
    _ = _ := by field_simp

/-- An optional common factor includes the nested-support case. -/
noncomputable def distinctMap (shared : Bool) (F : ZMod p → ZMod p → ℝ)
    (a b : ZMod p) : ℝ :=
  (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v =>
    chiRe (u - a) * (if shared then chiRe (u - b) else 1) * chiRe (v - b) * F u v))

theorem distinctMap_sq (hp : p ≠ 2) (shared : Bool) (F : ZMod p → ZMod p → ℝ) :
    (fieldLaw p).expect (fun a => (fieldLaw p).expect (fun b => distinctMap shared F a b ^ 2)) ≤
      (p : ℝ)⁻¹ ^ 2 * (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v => F u v ^ 2)) := by
  let G := fun u b => characterMap (F u) b
  let m := fun (u b : ZMod p) => if shared then chiRe (u - b) else (1 : ℝ)
  have hm (u b : ZMod p) : m u b ^ 2 ≤ 1 := by
    dsimp [m]
    cases shared
    · norm_num
    · exact (sq_le_one_iff_abs_le_one _).mpr (abs_chiRe_le _)
  have he (a b : ZMod p) : distinctMap shared F a b =
      characterMap (fun u => m u b * G u b) a := by
    unfold distinctMap characterMap
    apply FiniteLaw.expect_congr
    intro u
    dsimp [m, G, characterMap]
    rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_const_mul]
    apply FiniteLaw.expect_congr
    intro v
    ring
  have hcol (b : ZMod p) :
      (fieldLaw p).expect (fun a => distinctMap shared F a b ^ 2) ≤
        (p : ℝ)⁻¹ * (fieldLaw p).expect (fun u => G u b ^ 2) := by
    simp_rw [he]
    refine (characterMap_sq hp (fun u => m u b * G u b)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply FiniteLaw.expect_mono
    intro u
    rw [mul_pow]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hm u b) (sq_nonneg (G u b))
  calc
    _ = (fieldLaw p).expect (fun b => (fieldLaw p).expect
        (fun a => distinctMap shared F a b ^ 2)) := Cuts.expect_comm _ _ _
    _ ≤ (fieldLaw p).expect (fun b => (p : ℝ)⁻¹ *
        (fieldLaw p).expect (fun u => G u b ^ 2)) := FiniteLaw.expect_mono _ hcol
    _ = (p : ℝ)⁻¹ * (fieldLaw p).expect (fun u =>
        (fieldLaw p).expect (fun b => G u b ^ 2)) := by
      rw [FiniteLaw.expect_const_mul, Cuts.expect_comm]
    _ ≤ (p : ℝ)⁻¹ * (fieldLaw p).expect (fun u =>
        (p : ℝ)⁻¹ * (fieldLaw p).expect (fun v => F u v ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact FiniteLaw.expect_mono _ fun u => characterMap_sq hp (F u)
    _ = _ := by rw [FiniteLaw.expect_const_mul]; ring

/-- Equal supports use the off-diagonal four-cycle map on two output labels. -/
noncomputable def equalMap (F : ZMod p → ZMod p → ℝ) (a b : ZMod p) : ℝ :=
  if a = b then 0 else
    (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v =>
      chiRe (u - a) * chiRe (u - b) * (chiRe (v - a) * chiRe (v - b)) * F u v))

theorem equalMap_sq (hDLK : Target.FourCycle) (hp : p ≠ 2)
    (F : ZMod p → ZMod p → ℝ) (hF : ∀ u, F u u = 0) :
    (fieldLaw p).expect (fun a => (fieldLaw p).expect (fun b => equalMap F a b ^ 2)) ≤
      4 * (p : ℝ)⁻¹ ^ 2 *
        (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v => F u v ^ 2)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  let V := fun (a b : ZMod p) => (1 / (p : ℝ) ^ 2) * ∑ u, ∑ v,
    chiRe (u - a) * chiRe (u - b) * (chiRe (v - a) * chiRe (v - b)) * F u v
  have he (a b : ZMod p) : equalMap F a b = if a = b then 0 else V a b := by
    unfold equalMap V
    simp only [fieldLaw, FiniteLaw.expect_uniform, ZMod.card, ← sum_div]
    rw [div_div]
    congr 1
    ring
  have hsum : (∑ a, ∑ b, equalMap F a b ^ 2) =
      ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2), V y.1 y.2 ^ 2 := by
    rw [sum_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rw [he]
    by_cases hab : a = b <;> simp only [hab, ne_eq, not_true_eq_false, not_false_eq_true,
      ite_true, ite_false, zero_pow, OfNat.ofNat_ne_zero]
  have h := DLK.raw_pair_offdiag hDLK hp F hF
  change 1 / ((p : ℝ) * (p - 1)) *
    (∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2), V y.1 y.2 ^ 2) ≤ _ at h
  have hc : 0 ≤ ((p : ℝ) - 1) / p := by positivity
  have hb := mul_le_mul_of_nonneg_left h hc
  simp only [fieldLaw, FiniteLaw.expect_uniform, ZMod.card, ← sum_div, div_div]
  rw [hsum]
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  convert hb using 1 <;> field_simp [hp0, hpm]

end Sarkozy.SpectralC.TwoLabel
