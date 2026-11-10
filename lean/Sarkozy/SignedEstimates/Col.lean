module

public import Sarkozy.SignedEstimates.Row

@[expose] public section

/-!
# The column sums of `U_{uv}` (`lem:signed-components`(b), columns) (E1)

`paper/sections/21_middle_records.tex`, `lem:signed-components`(b).

For a half `y = (c, e, f) ∈ H_F` the column sum `∑_{x ∈ H_F} U_{uv}(x, y)` is computed
**exactly** (`col_sum_eq`), with `s = 1 - t`, `n = p`:

  `S = R₀ (n - uv) + R₁ (u + v + uv W) + Q (1 + v)(1 + u χ(e - c))`,

where `R₀ = (n-1)(n-3)/2`, `R₁ = (1-s)(n-3)/2`, `Q = (n-1)(2 + s(n-1))/2` and
`W = ∑_a χ(a - c) χ(a - e) χ(a - f)`. The proof sums `x₁` (the in-neighbours of `y₀` other than
`x₀, x₂`), then `x₂` over the out-neighbours of `x₀`, then `x₀`.

The paper bounds the columns without a character sum, by `q R_col`; the exact value used here
contains `W` with the coefficient `t(n - 3)/2`, bounded by `thm:weil`(a). `col_poly_aux`:
`|S/|H_F| - 1| ≤ 10/p` for `p ≥ 2²⁴`, `0 ≤ t ≤ 1`, `|W| ≤ 2√p`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedEstimates

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- `2·1[χ(c - a) = 1] = 1 - [a = c] - χ(a - c)`. -/
theorem two_ind_in (h3 : Fintype.card F % 4 = 3) (c a : F) :
    2 * (if χ (c - a) = 1 then (1 : ℝ) else 0) = 1 - (if a = c then 1 else 0) - χ (a - c) := by
  by_cases h : a = c
  · subst h; simp
  · have hsw := chiR_swap h3 a c
    rcases quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm h)) with e | e <;>
      simp only [e, h, ↓reduceIte, hsw] <;> norm_num

/-- The column coefficient `R₀`. -/
noncomputable def Rc0 (n : ℝ) : ℝ := (n - 1) * (n - 3) / 2

/-- The column coefficient `R₁`. -/
noncomputable def Rc1 (n s : ℝ) : ℝ := (1 - s) * (n - 3) / 2

/-- The column coefficient `Q` (the coincidence `x₀ = y₀`). -/
noncomputable def Qc (n s : ℝ) : ℝ := (n - 1) * (2 + s * (n - 1)) / 2

/-- **The `(x₁, x₂)`-sum at `x₀ = a`.** -/
theorem inner_col (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a c : F) (s : ℝ) :
    ∑ z, (if χ (z - a) = 1 then (1 + s * χ (z - c)) *
      ((Fintype.card F : ℝ) - 3 + (if a = c then 1 else 0) + χ (a - c) +
        (if z = c then 1 else 0) + χ (z - c)) else 0) =
      Rc0 (Fintype.card F) + Rc1 (Fintype.card F) s * χ (a - c) +
        Qc (Fintype.card F) s * (if a = c then 1 else 0) := by
  set n : ℝ := (Fintype.card F : ℝ) with hn
  set E : ℝ := n - 3 + (if a = c then 1 else 0) + χ (a - c) with hE
  rw [sum_out]
  have eG : ∀ z, (1 + s * (χ (z - c) : ℝ)) * (E + (if z = c then 1 else 0) + χ (z - c)) =
      (E + s) + (1 - s) * (if c = z then 1 else 0) + (1 + s * E) * χ (z - c) := by
    intro z
    by_cases hz : z = c
    · subst hz; simp
    · have := chiR_sq_ne (sub_ne_zero.mpr hz)
      simp only [hz, Ne.symm hz, ↓reduceIte, mul_zero, add_zero]
      linear_combination s * this
  have eH : ∀ z, (χ (z - a) : ℝ) * ((E + s) + (1 - s) * (if c = z then 1 else 0) +
      (1 + s * E) * χ (z - c)) =
      (E + s) * χ (z - a) + (if c = z then (1 - s) * χ (c - a) else 0) +
        (1 + s * E) * (χ (z - a) * χ (z - c)) := by
    intro z
    by_cases hz : c = z
    · subst hz; simp; ring
    · simp only [hz, ↓reduceIte]; ring
  simp only [eG, eH, sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte, sum_const,
    card_univ, nsmul_eq_mul, mul_one, sumR_chi hR, sumR_chi_mul hR]
  unfold Rc0 Rc1 Qc
  by_cases hac : a = c
  · have e1 : (χ (c - a) : ℝ) = 0 := by rw [hac, sub_self, quadraticChar_zero, Int.cast_zero]
    have e2 : (χ (a - c) : ℝ) = 0 := by rw [hac, sub_self, quadraticChar_zero, Int.cast_zero]
    simp only [hE]
    rw [e1, e2]
    simp only [hac, ↓reduceIte]
    rw [← hn]
    ring
  · have h1 := chiR_sq_ne (sub_ne_zero.mpr hac)
    have h2 := chiR_swap h3 c a
    simp only [hE, hac, Ne.symm hac, ↓reduceIte]
    rw [h2, ← hn]
    linear_combination (-s / 2) * h1

/-- The second cubic character sum `W(c, e, f) = ∑_a χ(a - c) χ(a - e) χ(a - f)`. -/
theorem Wsum_def (c e f : F) : Wsum c e f = ∑ a, (χ (a - c) : ℝ) * χ (a - e) * χ (a - f) := rfl

/-- **The exact column sum of `U_{uv}`** at a half `y ∈ H_F` (`lem:signed-components`(b),
columns). -/
theorem col_sum_eq (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {y : Fin 3 → F}
    (hy : HF y) (t u v : ℝ) :
    ∑ x, Ukernel t u v (x, y) =
      Rc0 (Fintype.card F) * ((Fintype.card F : ℝ) - u * v) +
        Rc1 (Fintype.card F) (1 - t) * (u + v + u * v * Wsum (y 0) (y 1) (y 2)) +
        Qc (Fintype.card F) (1 - t) * (1 + v) * (1 + u * χ (y 1 - y 0)) := by
  obtain ⟨h01, h02, h12⟩ := HF_ne hy
  set n : ℝ := (Fintype.card F : ℝ) with hn
  set s : ℝ := 1 - t with hs
  set G : F → ℝ := fun a => (1 + u * χ (y 1 - a)) * (1 + v * χ (y 2 - a)) with hG
  have hU : ∀ x, Ukernel t u v (x, y) = if HF x then
      2 * (if χ (y 0 - x 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (x 2 - y 0)) *
        (1 + u * χ (y 1 - x 0)) * (1 + v * χ (y 2 - x 0)) else 0 := by
    intro x
    unfold Ukernel
    by_cases hx : HF x <;> simp [hx, hy, hs]
  rw [sum_congr rfl fun x _ => hU x, sumHF]
  have hw : ∀ a z, χ (z - a) = 1 → ∑ w, (if w ≠ a ∧ w ≠ z then
      2 * (if χ (y 0 - ![a, w, z] 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (![a, w, z] 2 - y 0)) *
        (1 + u * χ (y 1 - ![a, w, z] 0)) * (1 + v * χ (y 2 - ![a, w, z] 0)) else 0) =
      G a * ((1 + s * χ (z - y 0)) * (n - 3 + (if a = y 0 then 1 else 0) + χ (a - y 0) +
        (if z = y 0 then 1 else 0) + χ (z - y 0))) := by
    intro a z hz
    have e : ∀ w, 2 * (if χ (y 0 - ![a, w, z] 1) = 1 then (1 : ℝ) else 0) *
        (1 + s * χ (![a, w, z] 2 - y 0)) * (1 + u * χ (y 1 - ![a, w, z] 0)) *
        (1 + v * χ (y 2 - ![a, w, z] 0)) =
        (G a * (1 + s * χ (z - y 0))) * (2 * (if χ (y 0 - w) = 1 then (1 : ℝ) else 0)) := by
      intro w
      show 2 * (if χ (y 0 - w) = 1 then (1 : ℝ) else 0) * (1 + s * χ (z - y 0)) *
        (1 + u * χ (y 1 - a)) * (1 + v * χ (y 2 - a)) = _
      simp only [hG]
      ring
    simp only [e]
    rw [sum_excl2 (ne_of_chi_one hz).symm, two_ind_in h3, two_ind_in h3]
    have hsum : ∑ w, 2 * (if χ (y 0 - w) = 1 then (1 : ℝ) else 0) = n - 1 := by
      have := sum_in h3 (y 0) (fun _ => (2 : ℝ))
      simp only [sum_const, card_univ, nsmul_eq_mul, ← sum_mul, sumR_chi hR, zero_mul,
        sub_zero] at this
      rw [← hn] at this
      calc ∑ w, 2 * (if χ (y 0 - w) = 1 then (1 : ℝ) else 0) =
            ∑ w, (if χ (y 0 - w) = 1 then (2 : ℝ) else 0) :=
            sum_congr rfl fun w _ => by split_ifs <;> simp
        _ = n - 1 := by rw [this]; ring
    rw [hsum]
    ring
  have hz : ∀ a, ∑ z, (if χ (z - a) = 1 then ∑ w, (if w ≠ a ∧ w ≠ z then
      2 * (if χ (y 0 - ![a, w, z] 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (![a, w, z] 2 - y 0)) *
        (1 + u * χ (y 1 - ![a, w, z] 0)) * (1 + v * χ (y 2 - ![a, w, z] 0)) else 0) else 0) =
      G a * (Rc0 n + Rc1 n s * χ (a - y 0) + Qc n s * (if a = y 0 then 1 else 0)) := by
    intro a
    rw [sum_ite_congr (hw a), sum_ite_mul_left, inner_col hR h3]
  simp only [hz]
  have hf : (χ (y 2 - y 0) : ℝ) = 1 := by rw [hy.2]; simp
  have hc : ∀ a, G a * (Rc0 n + Rc1 n s * χ (a - y 0) + Qc n s * (if a = y 0 then 1 else 0)) =
      Rc0 n - (u * Rc0 n) * χ (a - y 1) - (v * Rc0 n) * χ (a - y 2) +
        (u * v * Rc0 n) * (χ (a - y 1) * χ (a - y 2)) + Rc1 n s * χ (a - y 0) -
        (u * Rc1 n s) * (χ (a - y 0) * χ (a - y 1)) - (v * Rc1 n s) * (χ (a - y 0) * χ (a - y 2)) +
        (u * v * Rc1 n s) * (χ (a - y 0) * χ (a - y 1) * χ (a - y 2)) +
        (if y 0 = a then Qc n s * (1 + v) * (1 + u * χ (y 1 - y 0)) else 0) := by
    intro a
    simp only [hG]
    rw [chiR_swap h3 (y 1) a, chiR_swap h3 (y 2) a]
    by_cases ha : a = y 0
    · rw [ha]
      simp only [sub_self, quadraticChar_zero, Int.cast_zero, ↓reduceIte]
      rw [chiR_swap h3 (y 0) (y 1), chiR_swap h3 (y 0) (y 2), hf]
      ring
    · simp only [ha, Ne.symm ha, ↓reduceIte]
      ring
  simp only [hc, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte,
    sum_const, card_univ, nsmul_eq_mul, sumR_chi hR, sumR_chi_mul_ne hR h12,
    sumR_chi_mul_ne hR h01, sumR_chi_mul_ne hR h02]
  unfold Wsum
  rw [← hn]
  ring

set_option maxHeartbeats 1000000 in
/-- **The polynomial inequality of the column bound** (exact column sum against `|H_F|`). -/
theorem col_poly_aux (n t u v κ W : ℝ) (hn : 16777216 ≤ n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hκ : κ = 1 ∨ κ = -1)
    (hW : |W| ≤ 2 * Real.sqrt n) :
    |Rc0 n * (n - u * v) + Rc1 n (1 - t) * (u + v + u * v * W) +
      Qc n (1 - t) * (1 + v) * (1 + u * κ) - n * (n - 1) * (n - 2) / 2| ≤
      5 * (n - 1) * (n - 2) := by
  have hW' := le_trans hW (two_sqrt_le hn)
  have hV : |t * W| ≤ n / 2048 := by
    rw [abs_mul, abs_of_nonneg ht0]
    nlinarith [abs_nonneg W]
  have e : Rc1 n (1 - t) * (u + v + u * v * W) =
      Rc1 n (1 - t) * (u + v) + (n - 3) / 2 * u * v * (t * W) := by unfold Rc1; ring
  rw [e]
  have hs0 : 0 ≤ 1 - t := by linarith
  have hs1 : 1 - t ≤ 1 := by linarith
  clear e hW hW'
  generalize t * W = V at hV ⊢
  unfold Rc0 Rc1 Qc
  generalize 1 - t = s at hs0 hs1 ⊢
  clear ht0 ht1
  have hV' := abs_le.mp hV
  clear hV
  have hn2 : 16777216 * n ≤ n * n := by nlinarith
  have hsn : 0 ≤ s * n := by positivity
  have hsn' : s * n ≤ n := by nlinarith
  have hsnn : 0 ≤ s * (n * n) := by positivity
  have hsnn' : s * (n * n) ≤ n * n := by nlinarith
  have hnV1 : n * V ≤ n * n / 2048 := by nlinarith
  have hnV2 : -(n * n / 2048) ≤ n * V := by nlinarith
  rw [abs_le]
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hκ with rfl | rfl <;>
    constructor <;> nlinarith

/-- **The column estimate of `lem:signed-components`(b)**: `|E_{x ∼ ν_F} U_{uv}(x, y) - 1| ≤ 10/p`
on `H_F`, for `p ≥ 2²⁴`, `0 ≤ t ≤ 1`, `u, v = ±1`, given the Weil bound `|W| ≤ 2√p` at the three
labels of `y` (`thm:weil`(a)). -/
theorem colMean_bound (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hn : (16777216 : ℝ) ≤ Fintype.card F) {t u v : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) {y : Fin 3 → F} (hy : HF y)
    (hW : |Wsum (y 0) (y 1) (y 2)| ≤ 2 * Real.sqrt (Fintype.card F)) :
    |colMean t u v y - 1| ≤ 10 / (Fintype.card F : ℝ) := by
  obtain ⟨h01, -, -⟩ := HF_ne hy
  unfold colMean
  rw [col_sum_eq hR h3 hy, Hcard_eq hR]
  have key := col_poly_aux (Fintype.card F) t u v _ _ hn ht0 ht1 hu hv
    (chiR_ne_cases (sub_ne_zero.mpr (Ne.symm h01))) hW
  set n : ℝ := (Fintype.card F : ℝ)
  have hH : 0 < n * (n - 1) * (n - 2) / 2 := by
    have : 0 < n - 2 := by linarith
    have : 0 < n - 1 := by linarith
    positivity
  rw [div_sub_one hH.ne', abs_div, abs_of_pos hH, div_le_div_iff₀ hH (by linarith)]
  calc _ ≤ 5 * (n - 1) * (n - 2) * n := mul_le_mul_of_nonneg_right key (by linarith)
    _ = 10 * (n * (n - 1) * (n - 2) / 2) := by ring

end Sarkozy.SignedEstimates
