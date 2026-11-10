module

public import Sarkozy.NormBoundsPaper4.EFinal

@[expose] public section

/-!
# `𝖢𝖣` on the singleton features (`lem:record:e-orthogonal`(a),(b); FD)

`paper/sections/21_middle_records.tex`, `lem:record:e-orthogonal`: "(a) The pair-star map
`𝒯_E g(x) = E_t χ(t − x₁)χ(t − x₀)g(t)` … for independent labels its norm there is exactly
`(q(1 − 2q))^{1/2}` … (b) On mean-zero functions `𝖢𝖣V₀ = 𝖢𝖣V₁ = −u𝒯_E` and
`𝖢𝖣V₂ = 2𝒯_E/((p − 1)(p − 2))`. Hence … `‖𝖢𝖣H‖ ≤ e_E`."

Unnormalized, through NB3's pair reduction:
* `red_lift`: `red (V c)(b) = [b₀ ≠ b₁](f(b₀) + g(b₁))`, `f = (p − 2)c₀ − c₂`, `g = (p − 2)c₁ − c₂`;
* `chi_corr'`: `∑_s χ(t − s)χ(t' − s) = p[t = t'] − 1`; `sum_chi`: `∑_b χ(b − a) = 0`;
* `TE`, **`TE_sq`**: `∑_a 𝒯φ(a)² = p(p − 2)∑ φ²` for mean-zero `φ` (on all pairs; (a));
* **`CH_lift`**: `∑_b red(V c)(b) 𝖢𝖣(a, b) = −𝒯(f + g)(a)` ((b));
* **`ePrime_cd`**: the field `cd` of `EPrimeInputs`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3
open Sarkozy.NormBoundsPaper2 (off chC chH)
open Sarkozy.JointRows.PaleyGauss (chiR chiR_neg chiR_zero chiR_sq sum_chi_shift ringChar_ne_two)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

local notation "T3" => (ZMod p × ZMod p) × ZMod p

/-! ## Character sums -/

theorem sum_chi (h3 : p % 4 = 3) (a : ZMod p) : ∑ b, chiR p (b - a) = 0 := by
  have e : ∑ b, chiR p (b - a) = ∑ b, chiR p b :=
    Fintype.sum_equiv (Equiv.subRight a) _ _ (fun b => rfl)
  rw [e]
  unfold chiR
  have := quadraticChar_sum_zero (ringChar_ne_two h3)
  have h2 : ((∑ b : ZMod p, quadraticChar (ZMod p) b : ℤ) : ℝ) = 0 := by rw [this]; simp
  push_cast at h2
  exact h2

theorem chi_corr' (h3 : p % 4 = 3) (t t' : ZMod p) :
    ∑ s, chiR p (t - s) * chiR p (t' - s) = (if t = t' then (p : ℝ) else 0) - 1 := by
  by_cases htt : t = t'
  · subst htt
    simp only [↓reduceIte]
    have h : ∀ s, chiR p (t - s) * chiR p (t - s) = 1 - (if s = t then 1 else 0) := by
      intro s
      by_cases hs : s = t
      · subst hs; simp [chiR_zero]
      · simp only [hs, ↓reduceIte, sub_zero]
        exact chiR_sq (sub_ne_zero.mpr (Ne.symm hs))
    rw [sum_congr rfl fun s _ => h s, sum_sub_distrib]
    simp
  · simp only [htt, ↓reduceIte, zero_sub]
    have h := sum_chi_shift h3 (Ne.symm htt) (p := p)
    have e : ∀ s, chiR p (t - s) * chiR p (t' - s) = -(chiR p (s - t') * chiR p (t - s)) := by
      intro s
      rw [show t' - s = -(s - t') by ring, chiR_neg h3]
      ring
    rw [sum_congr rfl fun s _ => e s, sum_neg_distrib, h]

/-! ## The pair-star map -/

/-- `𝒯φ(a) = ∑_t φ(t)χ(t − a₁)χ(t − a₀)` (unnormalized). -/
noncomputable def TE (φ : ZMod p → ℝ) (a : ZMod p × ZMod p) : ℝ :=
  ∑ t, φ t * (chiR p (t - a.2) * chiR p (t - a.1))

/-- **`lem:record:e-orthogonal`(a)** for independent labels: `∑_a 𝒯φ(a)² = p(p − 2)∑ φ²`. -/
theorem TE_sq (h3 : p % 4 = 3) (φ : ZMod p → ℝ) (hφ : ∑ t, φ t = 0) :
    ∑ a, TE φ a ^ 2 = (p : ℝ) * ((p : ℝ) - 2) * ∑ t, φ t ^ 2 := by
  have e1 : ∀ a : ZMod p × ZMod p, TE φ a ^ 2 =
      ∑ t, ∑ t', φ t * φ t' * ((chiR p (t - a.2) * chiR p (t' - a.2)) *
        (chiR p (t - a.1) * chiR p (t' - a.1))) := fun a => by
    unfold TE
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun t _ => sum_congr rfl fun t' _ => by ring
  simp only [e1]
  rw [Fintype.sum_prod_type]
  have e2 : ∀ a1, ∑ a2, ∑ t, ∑ t', φ t * φ t' * ((chiR p (t - (a1, a2).2) *
      chiR p (t' - (a1, a2).2)) * (chiR p (t - (a1, a2).1) * chiR p (t' - (a1, a2).1))) =
      ∑ t, ∑ t', φ t * φ t' * (chiR p (t - a1) * chiR p (t' - a1)) *
        ((if t = t' then (p : ℝ) else 0) - 1) := fun a1 => by
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t' _ => ?_
    rw [← chi_corr' h3 t t', mul_sum]
    exact sum_congr rfl fun a2 _ => by ring
  simp only [e2]
  rw [sum_comm]
  have e3 : ∀ t, ∑ a1, ∑ t', φ t * φ t' * (chiR p (t - a1) * chiR p (t' - a1)) *
      ((if t = t' then (p : ℝ) else 0) - 1) =
      ∑ t', φ t * φ t' * ((if t = t' then (p : ℝ) else 0) - 1) ^ 2 := fun t => by
    rw [sum_comm]
    refine sum_congr rfl fun t' _ => ?_
    rw [sq, ← chi_corr' h3 t t', mul_sum, mul_sum]
    refine sum_congr rfl fun a1 _ => ?_
    ring
  simp only [e3]
  have e4 : ∀ t, ∑ t', φ t * φ t' * ((if t = t' then (p : ℝ) else 0) - 1) ^ 2 =
      ((p : ℝ) ^ 2 - 2 * p) * φ t ^ 2 + φ t * ∑ t', φ t' := fun t => by
    have : ∀ t', φ t * φ t' * ((if t = t' then (p : ℝ) else 0) - 1) ^ 2 =
        (if t = t' then ((p : ℝ) ^ 2 - 2 * p) * (φ t * φ t') else 0) + φ t * φ t' := fun t' => by
      split_ifs <;> ring
    rw [sum_congr rfl fun t' _ => this t', sum_add_distrib, sum_ite_eq, mul_sum]
    simp only [mem_univ, ↓reduceIte]
    ring
  simp only [e4, hφ, mul_zero, add_zero, ← mul_sum]
  ring

/-! ## `𝖢𝖣` on `V(H₀³)` -/

theorem red_lift (c : Fin 3 → ZMod p → ℝ) (hc : ∀ i, ∑ t, c i t = 0) (b : ZMod p × ZMod p) :
    red (lift c) b = off b * ((((p : ℝ) - 2) * c 0 b.1 - c 2 b.1) +
      (((p : ℝ) - 2) * c 1 b.2 - c 2 b.2)) := by
  unfold red lift
  simp only [Fin.sum_univ_three]
  change ∑ x, ind3 (b, x) * (c 0 b.1 + c 1 b.2 + c 2 x) = _
  by_cases hb : b.1 = b.2
  · simp [ind3_diag b _ hb, off, hb]
  · simp only [ind3_fib b _ hb]
    have e : ∀ x, (1 - (if x = b.1 then (1 : ℝ) else 0) - (if x = b.2 then 1 else 0)) *
        (c 0 b.1 + c 1 b.2 + c 2 x) = (c 0 b.1 + c 1 b.2 + c 2 x) -
        (if x = b.1 then c 0 b.1 + c 1 b.2 + c 2 b.1 else 0) -
        (if x = b.2 then c 0 b.1 + c 1 b.2 + c 2 b.2 else 0) := fun x => by
      split_ifs with h1 h2 h2
      · exact absurd (h1.symm.trans h2) hb
      · rw [h1]; ring
      · rw [h2]; ring
      · ring
    rw [sum_congr rfl fun x _ => e x, sum_sub_distrib, sum_sub_distrib, sum_ite_eq', sum_ite_eq',
      sum_add_distrib, sum_add_distrib, hc 2]
    simp only [mem_univ, ↓reduceIte, sum_const, card_univ, ZMod.card, nsmul_eq_mul, off, hb]
    ring

/-- **`lem:record:e-orthogonal`(b)**: `∑_b red(V c)(b)𝖢𝖣(a, b) = −𝒯(f + g)(a)`. -/
theorem CH_lift (h3 : p % 4 = 3) (c : Fin 3 → ZMod p → ℝ) (hc : ∀ i, ∑ t, c i t = 0)
    (a : ZMod p × ZMod p) :
    ∑ b, red (lift c) b * (chC a b * chH a b) =
      -TE (fun t => ((p : ℝ) - 2) * (c 0 t + c 1 t) - 2 * c 2 t) a := by
  set f : ZMod p → ℝ := fun t => ((p : ℝ) - 2) * c 0 t - c 2 t
  set g : ZMod p → ℝ := fun t => ((p : ℝ) - 2) * c 1 t - c 2 t
  have e1 : ∀ b : ZMod p × ZMod p, red (lift c) b * (chC a b * chH a b) =
      (f b.1 + g b.2) * (chiR p (b.1 - a.2) * chiR p (b.2 - a.1)) -
      (if b.1 = b.2 then (f b.1 + g b.2) * (chiR p (b.1 - a.2) * chiR p (b.2 - a.1)) else 0) :=
    fun b => by
      rw [red_lift c hc b]
      unfold off chC chH
      split_ifs <;> simp [f, g]
  rw [sum_congr rfl fun b _ => e1 b, sum_sub_distrib, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  have e2 : ∀ b1 : ZMod p, ∑ b2, (f (b1, b2).1 + g (b1, b2).2) *
      (chiR p ((b1, b2).1 - a.2) * chiR p ((b1, b2).2 - a.1)) =
      f b1 * chiR p (b1 - a.2) * ∑ b2, chiR p (b2 - a.1) +
        ∑ b2, g b2 * chiR p (b2 - a.1) * chiR p (b1 - a.2) := fun b1 => by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun b2 _ => by simp only; ring
  have e3 : ∀ b1 : ZMod p, ∑ b2, (if (b1, b2).1 = (b1, b2).2 then (f (b1, b2).1 + g (b1, b2).2) *
      (chiR p ((b1, b2).1 - a.2) * chiR p ((b1, b2).2 - a.1)) else 0) =
      (f b1 + g b1) * (chiR p (b1 - a.2) * chiR p (b1 - a.1)) := fun b1 => by
    simp only
    rw [sum_ite_eq]
    simp
  simp only [e2, e3, sum_chi h3, mul_zero, zero_add]
  rw [sum_comm]
  have e4 : ∀ b2 : ZMod p, ∑ b1, g b2 * chiR p (b2 - a.1) * chiR p (b1 - a.2) = 0 := fun b2 => by
    rw [← mul_sum, sum_chi h3, mul_zero]
  simp only [e4, sum_const_zero, zero_sub]
  unfold TE
  rw [neg_inj]
  refine sum_congr rfl fun t _ => ?_
  simp only [f, g]
  ring

theorem n2_TE_le (h3 : p % 4 = 3) (hp : 3 ≤ p) (c : Fin 3 → ZMod p → ℝ)
    (hc : ∀ i, ∑ t, c i t = 0) :
    ∑ a, TE (fun t => ((p : ℝ) - 2) * (c 0 t + c 1 t) - 2 * c 2 t) a ^ 2 ≤
      (p : ℝ) * ((p : ℝ) - 2) * ((2 * ((p : ℝ) - 2) ^ 2 + 4) * ∑ i, n1 (c i)) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hφ : ∑ t, (((p : ℝ) - 2) * (c 0 t + c 1 t) - 2 * c 2 t) = 0 := by
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_add_distrib, hc 0, hc 1, hc 2]; ring
  rw [TE_sq h3 _ hφ]
  have hpp : 0 ≤ (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
  refine mul_le_mul_of_nonneg_left ?_ hpp
  simp only [Fin.sum_univ_three, n1, mul_add, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun t _ => ?_
  set k := (p : ℝ) - 2
  nlinarith [sq_nonneg (k * c 1 t - k * c 0 t), sq_nonneg (k * c 2 t + 2 * c 0 t),
    sq_nonneg (k * c 2 t + 2 * c 1 t)]

/-- **The field `cd` of `EPrimeInputs`** (`lem:record:e-orthogonal`(b)). -/
theorem ePrime_cd (h3 : p % 4 = 3) (hp : 7 ≤ p) (c : Fin 3 → ZMod p → ℝ)
    (hc : ∀ i, ∑ t, c i t = 0) (w : T3 → ℝ) :
    |CHf w (lift c)| ≤ eK p * Real.sqrt (Nq w) * Real.sqrt (Nq (lift c)) := by
  have hp' : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have hp3 : 3 ≤ p := by omega
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h3' : (0 : ℝ) < (p : ℝ) - 3 := by linarith
  set φ : ZMod p → ℝ := fun t => ((p : ℝ) - 2) * (c 0 t + c 1 t) - 2 * c 2 t
  have e : CHf w (lift c) = -∑ a, red w a * TE φ a := by
    unfold CHf
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    have : ∑ b, red w a * red (lift c) b * (chC a b * chH a b) =
        red w a * ∑ b, red (lift c) b * (chC a b * chH a b) := by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    rw [this, CH_lift h3 c hc a]
    ring
  rw [e, abs_neg]
  set S := ∑ i, n1 (c i)
  have hS0 : 0 ≤ S := sum_nonneg fun i _ => sum_nonneg fun t _ => sq_nonneg _
  have hNh : ((p : ℝ) - 2) * ((p : ℝ) - 3) * S ≤ Nq (lift c) := Nq_lift_ge hp3 c hc
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun a => |red w a|) (fun a => |TE φ a|)
  simp only [sq_abs] at hcs
  have h1 : |∑ a, red w a * TE φ a| ≤ Real.sqrt (n2 (red w)) * Real.sqrt (∑ a, TE φ a ^ 2) :=
    (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun a _ => le_of_eq (abs_mul _ _)).trans hcs)
  have h2' : Real.sqrt (n2 (red w)) ≤ Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq w) := by
    rw [← Real.sqrt_mul h2.le]; exact Real.sqrt_le_sqrt (red_sq hp3 w)
  have h3'' : Real.sqrt (∑ a, TE φ a ^ 2) ≤
      Real.sqrt ((p : ℝ) * ((p : ℝ) - 2) * (2 * ((p : ℝ) - 2) ^ 2 + 4)) * Real.sqrt S := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ((n2_TE_le h3 hp3 c hc).trans (le_of_eq ?_))
    ring
  -- `S ≤ Nq (V c)/((p − 2)(p − 3))`
  have hS : Real.sqrt S ≤ Real.sqrt (Nq (lift c)) / Real.sqrt (((p : ℝ) - 2) * ((p : ℝ) - 3)) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)), ← Real.sqrt_mul hS0]
    refine Real.sqrt_le_sqrt ?_
    linarith [hNh, show S * (((p : ℝ) - 2) * ((p : ℝ) - 3)) = ((p : ℝ) - 2) * ((p : ℝ) - 3) * S
      by ring]
  calc |∑ a, red w a * TE φ a|
      ≤ Real.sqrt (n2 (red w)) * Real.sqrt (∑ a, TE φ a ^ 2) := h1
    _ ≤ (Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq w)) *
        (Real.sqrt ((p : ℝ) * ((p : ℝ) - 2) * (2 * ((p : ℝ) - 2) ^ 2 + 4)) *
          (Real.sqrt (Nq (lift c)) / Real.sqrt (((p : ℝ) - 2) * ((p : ℝ) - 3)))) := by
        gcongr
        exact h3''.trans (mul_le_mul_of_nonneg_left hS (Real.sqrt_nonneg _))
    _ = eK p * Real.sqrt (Nq w) * Real.sqrt (Nq (lift c)) := by
        unfold eK
        have hA : 0 ≤ ((p : ℝ) - 2) := h2.le
        have hB : 0 ≤ (p : ℝ) := by linarith
        have hC : 0 ≤ 2 * ((p : ℝ) - 2) ^ 2 + 4 := by positivity
        have hD : 0 < ((p : ℝ) - 2) * ((p : ℝ) - 3) := by positivity
        rw [Real.sqrt_div' _ hD.le, Real.sqrt_mul (mul_nonneg hB hA), Real.sqrt_mul hB]
        have hsA : Real.sqrt ((p : ℝ) - 2) * Real.sqrt ((p : ℝ) - 2) = (p : ℝ) - 2 :=
          Real.mul_self_sqrt hA
        linear_combination (Real.sqrt p * (Real.sqrt (2 * ((p : ℝ) - 2) ^ 2 + 4) /
          Real.sqrt (((p : ℝ) - 2) * ((p : ℝ) - 3))) * Real.sqrt (Nq w) *
          Real.sqrt (Nq (lift c))) * hsA

end Sarkozy.NormBoundsPaper4
