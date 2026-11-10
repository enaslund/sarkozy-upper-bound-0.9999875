module

public import Sarkozy.Target
public import Sarkozy.Labellings.TargetBridge

/-!
# Moving-root traces and uniform constants (`lem:moving-root-trace`(b), `cor:moving-root-uniform`)

`paper/sections/15_second_order.tex`, with `τ_S` the function `Sarkozy.Target.tau` and the
literature inputs of `Sarkozy/Target.lean`.

* `abs_tau_le_of_not_mem`: `lem:moving-root-trace`(b) off the roots, `|τ_S(x)| ≤ h(s) r` for
  `x ∉ S`. The paper proves it through the purity of the sheaf of `y² = f_S(x)(x - z)`; here it
  follows from **Weil's bound alone** (`Target.Weil`): the sum is a complete character sum over
  the `s + 1` distinct roots `S ∪ {x}`, and Weil (a) (for `s` even) or (b) (for `s` odd) gives
  exactly `h(s)√p`.
* `moving_root_uniform`: `cor:moving-root-uniform` from `Target.MovingRoot` (H5): for
  `2 ≤ |S|, |T| ≤ 11` and `|A| ≤ 10`,
  `|E_x χ_A τ_S τ_T - [S = T, A = ∅]/p| ≤ 6000 r³` with `r = p^{-1/2}`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target Sarkozy.Labellings

variable {p : ℕ} [hp : Fact p.Prime]

theorem tau_eq_rootSum_insert (S : Finset (ZMod p)) {x : ZMod p} (hx : x ∉ S) :
    tau p S x =
      (1 / (p : ℝ)) * (((rootSum (insert x S) : ℤ) : ℝ) + if Odd S.card then 1 else 0) := by
  unfold tau rootSum
  congr 2
  push_cast
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [prod_insert hx, mul_comm]

theorem gam_even {s : ℕ} (he : Even s) : (gam s : ℝ) = s := by
  obtain ⟨k, rfl⟩ := he
  have : (k + k) / 2 = k := by omega
  simp only [gam, this]
  push_cast
  ring

theorem gam_odd {s : ℕ} (ho : Odd s) : (gam s : ℝ) = s - 1 := by
  obtain ⟨k, rfl⟩ := ho
  have : (2 * k + 1) / 2 = k := by omega
  simp only [gam, this]
  push_cast
  ring

/-- **`lem:moving-root-trace`(b), off the roots**, from Weil's bound: `|τ_S(x)| ≤ h(s) r`. -/
theorem abs_tau_le_of_not_mem (hW : Target.Weil) (hp2 : p ≠ 2) (S : Finset (ZMod p))
    {x : ZMod p} (hx : x ∉ S) :
    |tau p S x| ≤ (gam S.card : ℝ) * (1 / Real.sqrt p) := by
  have hWB := weilBound_of_target hW p hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsq0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hcard : (insert x S).card = S.card + 1 := card_insert_of_notMem hx
  have hmain : |((rootSum (insert x S) : ℤ) : ℝ) + (if Odd S.card then 1 else 0)| ≤
      (gam S.card : ℝ) * Real.sqrt p := by
    rcases Nat.even_or_odd S.card with he | ho
    · have hodd : ¬ Odd S.card := Nat.not_odd_iff_even.mpr he
      simp only [hodd, ↓reduceIte, add_zero]
      have hb := hWB (insert x S) (insert_nonempty x S)
      rw [hcard, ZMod.card] at hb
      push_cast at hb
      rw [gam_even he]
      linarith
    · simp only [ho, ↓reduceIte]
      have heven : Even (insert x S).card := by rw [hcard]; exact ho.add_one
      have h2 : 2 ≤ (insert x S).card := by
        rw [hcard]; have := ho.pos; omega
      have hb := weil_even hWB heven h2
      rw [hcard, ZMod.card] at hb
      push_cast at hb
      rw [gam_odd ho]
      linarith
  rw [tau_eq_rootSum_insert S hx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)]
  calc 1 / (p : ℝ) * |((rootSum (insert x S) : ℤ) : ℝ) + (if Odd S.card then 1 else 0)|
      ≤ 1 / (p : ℝ) * ((gam S.card : ℝ) * Real.sqrt p) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (gam S.card : ℝ) * (1 / Real.sqrt p) := by
        rw [show 1 / (p : ℝ) * ((gam S.card : ℝ) * Real.sqrt p) =
          (gam S.card : ℝ) * (Real.sqrt p / p) by ring, Real.sqrt_div_self']

/-- At a root `x ∈ S`, `f_S(y)(y - x) = (y - x)² f_{S∖{x}}(y)`, so the kernel sum is
`W_{S∖{x}} - χ(f_{S∖{x}}(x))`. -/
theorem kernelSum_eq_of_mem (S : Finset (ZMod p)) {x : ZMod p} (hx : x ∈ S) :
    (∑ y, quadraticChar (ZMod p) ((∏ a ∈ S, (y - a)) * (y - x)) : ℤ) =
      rootSum (S.erase x) - quadraticChar (ZMod p) (∏ a ∈ S.erase x, (x - a)) := by
  have hterm : ∀ y, quadraticChar (ZMod p) ((∏ a ∈ S, (y - a)) * (y - x)) =
      quadraticChar (ZMod p) (∏ a ∈ S.erase x, (y - a)) -
        (if y = x then quadraticChar (ZMod p) (∏ a ∈ S.erase x, (y - a)) else 0) := by
    intro y
    have hf : ∏ a ∈ S, (y - a) = (y - x) * ∏ a ∈ S.erase x, (y - a) :=
      (mul_prod_erase S (fun a => y - a) hx).symm
    rw [hf]
    by_cases h : y = x
    · subst h; simp
    · have hne : y - x ≠ 0 := sub_ne_zero.mpr h
      rw [show (y - x) * (∏ a ∈ S.erase x, (y - a)) * (y - x) =
        (y - x) ^ 2 * ∏ a ∈ S.erase x, (y - a) by ring, map_mul, quadraticChar_sq_one' hne,
        one_mul]
      simp only [h, ↓reduceIte, sub_zero]
  rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp only [mem_univ, ↓reduceIte, rootSum]

/-- **`lem:moving-root-trace`(b), at the roots**, from Weil's bound:
`|τ_S(x)| ≤ ((s - 2)√p + 2)/p ≤ s r` for `x ∈ S`. -/
theorem abs_tau_le_of_mem (hW : Target.Weil) (hp2 : p ≠ 2) (S : Finset (ZMod p))
    (hS2 : 2 ≤ S.card) {x : ZMod p} (hx : x ∈ S) :
    |tau p S x| ≤ (((S.card : ℝ) - 2) * Real.sqrt p + 2) / p ∧
      (((S.card : ℝ) - 2) * Real.sqrt p + 2) / p ≤ (S.card : ℝ) * (1 / Real.sqrt p) := by
  have hWB := weilBound_of_target hW p hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hsq1 : 1 ≤ Real.sqrt p := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp1
  have hcard : (S.erase x).card = S.card - 1 := card_erase_of_mem hx
  have hne : (S.erase x).Nonempty := card_pos.mp (by omega)
  have hb := hWB (S.erase x) hne
  rw [hcard, ZMod.card, Nat.cast_sub (by omega : 1 ≤ S.card), Nat.cast_one] at hb
  have hchi : |((quadraticChar (ZMod p) (∏ a ∈ S.erase x, (x - a)) : ℤ) : ℝ)| ≤ 1 := by
    rcases quadraticChar_isQuadratic (ZMod p) (∏ a ∈ S.erase x, (x - a)) with h | h | h <;>
      rw [h] <;> norm_num
  have hodd : |(if Odd S.card then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
  constructor
  · unfold tau
    rw [kernelSum_eq_of_mem S hx]
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / p)]
    have h1 := abs_le.mp hb
    have h2 := abs_le.mp hchi
    have h3 := abs_le.mp hodd
    have hsum : |(rootSum (S.erase x) : ℝ) -
        ((quadraticChar (ZMod p) (∏ a ∈ S.erase x, (x - a)) : ℤ) : ℝ) +
          (if Odd S.card then (1 : ℝ) else 0)| ≤ ((S.card : ℝ) - 2) * Real.sqrt p + 2 := by
      rw [abs_le]
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    calc 1 / (p : ℝ) * |(rootSum (S.erase x) : ℝ) -
          ((quadraticChar (ZMod p) (∏ a ∈ S.erase x, (x - a)) : ℤ) : ℝ) +
            (if Odd S.card then (1 : ℝ) else 0)|
        ≤ 1 / (p : ℝ) * (((S.card : ℝ) - 2) * Real.sqrt p + 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (((S.card : ℝ) - 2) * Real.sqrt p + 2) / p := by ring
  · rw [show (S.card : ℝ) * (1 / Real.sqrt p) = (S.card : ℝ) * Real.sqrt p / p by
      rw [mul_div_assoc, Real.sqrt_div_self']]
    apply div_le_div_of_nonneg_right _ hp0.le
    have : (S.card : ℝ) * Real.sqrt p - (((S.card : ℝ) - 2) * Real.sqrt p + 2) =
        2 * (Real.sqrt p - 1) := by ring
    linarith

/-- **`lem:moving-root-trace`(b), the uniform form**: `|τ_S| ≤ s r` on `𝔽_p` for `s ≥ 2`. -/
theorem abs_tau_le (hW : Target.Weil) (hp2 : p ≠ 2) (S : Finset (ZMod p)) (hS2 : 2 ≤ S.card)
    (x : ZMod p) : |tau p S x| ≤ (S.card : ℝ) * (1 / Real.sqrt p) := by
  by_cases hx : x ∈ S
  · obtain ⟨h1, h2⟩ := abs_tau_le_of_mem hW hp2 S hS2 hx
    exact h1.trans h2
  · refine (abs_tau_le_of_not_mem hW hp2 S hx).trans ?_
    have : gam S.card ≤ S.card := by unfold gam; omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (by positivity)

/-- **`cor:moving-root-uniform`** from the moving-root moments (H5). -/
theorem moving_root_uniform (hM : Target.MovingRoot) (hp2 : p ≠ 2) (S T A : Finset (ZMod p))
    (hS2 : 2 ≤ S.card) (hS : S.card ≤ 11) (hT2 : 2 ≤ T.card) (hT : T.card ≤ 11)
    (hA : A.card ≤ 10) :
    |(1 / (p : ℝ)) * (∑ x, chiA p A x * tau p S x * tau p T x) -
        (if S = T ∧ A = ∅ then 1 / (p : ℝ) else 0)| ≤ 6000 * (1 / Real.sqrt p) ^ 3 := by
  have h := (hM p hp2 S T A hS2 hT2).1
  refine h.trans ?_
  set r := 1 / Real.sqrt p
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := hp.out.two_le
    have : p ≠ 2 := hp2
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hr0 : 0 ≤ r := by positivity
  have hr : r ≤ 3 / 5 := by
    simp only [r]
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))]
    have : (5 / 3 : ℝ) ≤ Real.sqrt p := by
      rw [show (5 / 3 : ℝ) = Real.sqrt ((5 / 3) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  -- bounds on the integer parameters
  have hs : (S.card : ℝ) ≤ 11 := by exact_mod_cast hS
  have ht : (T.card : ℝ) ≤ 11 := by exact_mod_cast hT
  have hu : (A.card : ℝ) ≤ 10 := by exact_mod_cast hA
  have hs2 : (2 : ℝ) ≤ S.card := by exact_mod_cast hS2
  have ht2 : (2 : ℝ) ≤ T.card := by exact_mod_cast hT2
  have hu0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hgs : (gam S.card : ℝ) ≤ 10 := by
    have : gam S.card ≤ 10 := by unfold gam; omega
    exact_mod_cast this
  have hgt : (gam T.card : ℝ) ≤ 10 := by
    have : gam T.card ≤ 10 := by unfold gam; omega
    exact_mod_cast this
  have hgs0 : (0 : ℝ) ≤ gam S.card := Nat.cast_nonneg _
  have hgt0 : (0 : ℝ) ≤ gam T.card := Nat.cast_nonneg _
  have hbr : ((S.card : ℝ) + T.card + A.card - 1) * gam S.card * gam T.card + 1 +
      r * (S.card + T.card + A.card) * S.card * T.card ≤ 6000 := by
    have h1 : ((S.card : ℝ) + T.card + A.card - 1) * gam S.card * gam T.card ≤ 31 * 10 * 10 := by
      have hsum : 0 ≤ (S.card : ℝ) + T.card + A.card - 1 := by linarith
      have := mul_le_mul (mul_le_mul (by linarith : (S.card : ℝ) + T.card + A.card - 1 ≤ 31) hgs
        hgs0 (by norm_num)) hgt hgt0 (by norm_num)
      linarith [mul_nonneg (mul_nonneg hsum hgs0) hgt0]
    have h2 : r * ((S.card : ℝ) + T.card + A.card) * S.card * T.card ≤ (3 / 5) * 32 * 11 * 11 := by
      have hsum0 : 0 ≤ (S.card : ℝ) + T.card + A.card := by linarith
      have := mul_le_mul (mul_le_mul (mul_le_mul hr (by linarith :
        (S.card : ℝ) + T.card + A.card ≤ 32) hsum0 (by norm_num)) hs (by linarith) (by norm_num))
        ht (by linarith) (by norm_num)
      linarith
    linarith
  have hr3 : 0 ≤ r ^ 3 := by positivity
  calc r ^ 3 * (((S.card : ℝ) + T.card + A.card - 1) * gam S.card * gam T.card + 1 +
        r * (S.card + T.card + A.card) * S.card * T.card)
      ≤ r ^ 3 * 6000 := mul_le_mul_of_nonneg_left hbr hr3
    _ = 6000 * r ^ 3 := by ring

end Sarkozy.SecondOrder
