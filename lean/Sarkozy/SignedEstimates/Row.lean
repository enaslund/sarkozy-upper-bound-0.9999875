module

public import Sarkozy.SignedEstimates.Sums

@[expose] public section

/-!
# The row sums of `U_{uv}` (`lem:signed-components`(b), rows) (E1)

`paper/sections/21_middle_records.tex`, `lem:signed-components`(b).

For a half `x = (a, b, d) ∈ H_F` the row sum `∑_{y ∈ H_F} U_{uv}(x, y)` is computed **exactly**
(`row_sum_eq`), with `s = 1 - t`, `n = p`:

  `S = P₀ (n + s) + P₁ (s - 1) - s P₁ W - (1 - s χ(b - d)) (P₀ + P₁ χ(b - a))`
  `    + (1 + χ(a - b)) (1 - s χ(a - d)) Q`,

where `P₀ = ((n-1)(n-2) - (n-3)uv - (n-2)v + u)/2`, `P₁ = -(n-2)(u+v)/2`,
`Q = (n(n-2)v - nu - 2uv)/2` and `W = ∑_c χ(c - a) χ(c - b) χ(c - d)` is the cubic character sum
that `thm:weil`(a) bounds by `2√p`. The proof sums `y₁` (`p - 2` labels), then `y₂` over the
out-neighbours of `y₀` (`sum_out`), then `y₀`, using only `lem:paley-triple`(b).

The paper bounds the same sum by `q R_row` term by term; the exact value is used here instead
(`row_poly`: `|S/|H_F| - 1| ≤ 10/p` for `p ≥ 2²⁴`, `0 ≤ t ≤ 1`, `|W| ≤ 2√p`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedEstimates

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- `2·1[χ(c - b) = 1] = 1 + χ(c - b)` for `c ≠ b`. -/
theorem two_ind_ne {c b : F} (h : c ≠ b) :
    2 * (if χ (c - b) = 1 then (1 : ℝ) else 0) = 1 + χ (c - b) := by
  rcases quadraticChar_dichotomy (sub_ne_zero.mpr h) with e | e <;> norm_num [e]

/-- The row coefficient `P₀`. -/
noncomputable def P0 (n u v : ℝ) : ℝ := ((n - 1) * (n - 2) - (n - 3) * u * v - (n - 2) * v + u) / 2

/-- The row coefficient `P₁`. -/
noncomputable def P1 (n u v : ℝ) : ℝ := -(n - 2) * (u + v) / 2

/-- The row coefficient `Q` (the coincidence `y₀ = x₀`). -/
noncomputable def Qr (n u v : ℝ) : ℝ := (n * (n - 2) * v - n * u - 2 * u * v) / 2

/-- **The `(y₁, y₂)`-sum at `y₀ = c`.** -/
theorem inner_row (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a c : F) (u v : ℝ) :
    ∑ z, (if χ (z - c) = 1 then (1 + v * χ (z - a)) *
      ((Fintype.card F : ℝ) - 2 - u * χ (c - a) - u * χ (z - a)) else 0) =
      P0 (Fintype.card F) u v + P1 (Fintype.card F) u v * χ (c - a) +
        Qr (Fintype.card F) u v * (if c = a then 1 else 0) := by
  set n : ℝ := (Fintype.card F : ℝ) with hn
  rw [sum_out]
  have eG : ∀ z, (1 + v * (χ (z - a) : ℝ)) * (n - 2 - u * χ (c - a) - u * χ (z - a)) =
      (n - 2 - u * χ (c - a) - u * v) + (v * (n - 2 - u * χ (c - a)) - u) * χ (z - a) +
        (u * v) * (if a = z then 1 else 0) := by
    intro z
    by_cases hz : z = a
    · subst hz; simp
    · have := chiR_sq_ne (sub_ne_zero.mpr hz)
      simp only [Ne.symm hz, ↓reduceIte, mul_zero, add_zero]
      linear_combination (-(u * v)) * this
  have eH : ∀ z, (χ (z - c) : ℝ) * ((n - 2 - u * χ (c - a) - u * v) +
      (v * (n - 2 - u * χ (c - a)) - u) * χ (z - a) + (u * v) * (if a = z then 1 else 0)) =
      (n - 2 - u * χ (c - a) - u * v) * χ (z - c) +
        (v * (n - 2 - u * χ (c - a)) - u) * (χ (z - c) * χ (z - a)) +
        (if a = z then u * v * χ (a - c) else 0) := by
    intro z
    by_cases hz : z = a
    · subst hz; simp; ring
    · simp only [Ne.symm hz, ↓reduceIte]; ring
  simp only [eG, eH, sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte, sum_const,
    card_univ, nsmul_eq_mul, mul_one, sumR_chi hR, sumR_chi_mul hR]
  unfold P0 P1 Qr
  by_cases hca : c = a
  · have e1 : (χ (c - a) : ℝ) = 0 := by rw [hca, sub_self, quadraticChar_zero, Int.cast_zero]
    have e2 : (χ (a - c) : ℝ) = 0 := by rw [hca, sub_self, quadraticChar_zero, Int.cast_zero]
    rw [e1, e2]
    simp only [hca, ↓reduceIte]
    rw [← hn]
    ring
  · have h1 := chiR_sq_ne (sub_ne_zero.mpr hca)
    have h2 := chiR_swap h3 a c
    simp only [hca, Ne.symm hca, ↓reduceIte]
    rw [h2, ← hn]
    linear_combination (u * v / 2) * h1

omit [Field F] [DecidableEq F] in
theorem sum_ite_mul_left {P : F → Prop} [DecidablePred P] (K : ℝ) (G : F → ℝ) :
    ∑ z, (if P z then K * G z else 0) = K * ∑ z, (if P z then G z else 0) := by
  rw [mul_sum]
  exact sum_congr rfl fun z _ => by split_ifs <;> simp

/-- The cubic character sum `W(a, b, d) = ∑_c χ(c - a) χ(c - b) χ(c - d)` (`thm:weil`(a)). -/
noncomputable def Wsum (a b d : F) : ℝ := ∑ c, (χ (c - a) : ℝ) * χ (c - b) * χ (c - d)

/-- **The exact row sum of `U_{uv}`** at a half `x ∈ H_F` (`lem:signed-components`(b), rows). -/
theorem row_sum_eq (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) {x : Fin 3 → F}
    (hx : HF x) (t u v : ℝ) :
    ∑ y, Ukernel t u v (x, y) =
      P0 (Fintype.card F) u v * ((Fintype.card F : ℝ) + (1 - t)) +
        P1 (Fintype.card F) u v * ((1 - t) - 1) -
        ((1 - t) * P1 (Fintype.card F) u v) * Wsum (x 0) (x 1) (x 2) -
        (1 - (1 - t) * χ (x 1 - x 2)) * (P0 (Fintype.card F) u v +
          P1 (Fintype.card F) u v * χ (x 1 - x 0)) +
        (1 + χ (x 0 - x 1)) * (1 - (1 - t) * χ (x 0 - x 2)) * Qr (Fintype.card F) u v := by
  obtain ⟨h01, h02, h12⟩ := HF_ne hx
  set n : ℝ := (Fintype.card F : ℝ) with hn
  set s : ℝ := 1 - t with hs
  set H : F → ℝ := fun c => 2 * (if χ (c - x 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (x 2 - c))
    with hH
  have hU : ∀ y, Ukernel t u v (x, y) = if HF y then
      2 * (if χ (y 0 - x 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (x 2 - y 0)) *
        (1 + u * χ (y 1 - x 0)) * (1 + v * χ (y 2 - x 0)) else 0 := by
    intro y
    unfold Ukernel
    by_cases hy : HF y <;> simp [hx, hy, hs]
  rw [sum_congr rfl fun y _ => hU y, sumHF]
  have hw : ∀ c z, χ (z - c) = 1 → ∑ w, (if w ≠ c ∧ w ≠ z then
      2 * (if χ (![c, w, z] 0 - x 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (x 2 - ![c, w, z] 0)) *
        (1 + u * χ (![c, w, z] 1 - x 0)) * (1 + v * χ (![c, w, z] 2 - x 0)) else 0) =
      H c * ((1 + v * χ (z - x 0)) * (n - 2 - u * χ (c - x 0) - u * χ (z - x 0))) := by
    intro c z hz
    have e : ∀ w, 2 * (if χ (![c, w, z] 0 - x 1) = 1 then (1 : ℝ) else 0) *
        (1 + s * χ (x 2 - ![c, w, z] 0)) * (1 + u * χ (![c, w, z] 1 - x 0)) *
        (1 + v * χ (![c, w, z] 2 - x 0)) =
        (H c * (1 + v * χ (z - x 0))) * (1 + u * χ (w - x 0)) := by
      intro w
      show 2 * (if χ (c - x 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (x 2 - c)) *
        (1 + u * χ (w - x 0)) * (1 + v * χ (z - x 0)) = _
      simp only [hH]
      ring
    simp only [e]
    rw [sum_excl2 (ne_of_chi_one hz).symm]
    simp only [sum_add_distrib, ← mul_sum, sumR_chi hR, sum_const, card_univ, nsmul_eq_mul,
      mul_one, mul_zero, add_zero]
    ring
  have hz : ∀ c, ∑ z, (if χ (z - c) = 1 then ∑ w, (if w ≠ c ∧ w ≠ z then
      2 * (if χ (![c, w, z] 0 - x 1) = 1 then (1 : ℝ) else 0) * (1 + s * χ (x 2 - ![c, w, z] 0)) *
        (1 + u * χ (![c, w, z] 1 - x 0)) * (1 + v * χ (![c, w, z] 2 - x 0)) else 0) else 0) =
      H c * (P0 n u v + P1 n u v * χ (c - x 0) + Qr n u v * (if c = x 0 then 1 else 0)) := by
    intro c
    rw [sum_ite_congr (hw c), sum_ite_mul_left, inner_row hR h3]
  simp only [hz]
  have hc : ∀ c, H c * (P0 n u v + P1 n u v * χ (c - x 0) + Qr n u v * (if c = x 0 then 1 else 0))
      = P0 n u v + P0 n u v * χ (c - x 1) - (s * P0 n u v) * χ (c - x 2) -
        (s * P0 n u v) * (χ (c - x 1) * χ (c - x 2)) + P1 n u v * χ (c - x 0) +
        P1 n u v * (χ (c - x 0) * χ (c - x 1)) - (s * P1 n u v) * (χ (c - x 0) * χ (c - x 2)) -
        (s * P1 n u v) * (χ (c - x 0) * χ (c - x 1) * χ (c - x 2)) -
        (if x 1 = c then (1 - s * χ (x 1 - x 2)) * (P0 n u v + P1 n u v * χ (x 1 - x 0)) else 0) +
        (if x 0 = c then (1 + χ (x 0 - x 1)) * (1 - s * χ (x 0 - x 2)) * Qr n u v else 0) := by
    intro c
    have hsw := chiR_swap h3 (x 2) c
    by_cases hb : c = x 1
    · rw [hb]
      simp only [hH, sub_self, quadraticChar_zero, Int.cast_zero, h01, Ne.symm h01, ↓reduceIte]
      rw [chiR_swap h3 (x 2) (x 1)]
      norm_num
      ring
    · by_cases ha : c = x 0
      · rw [ha]
        simp only [hH, sub_self, quadraticChar_zero, Int.cast_zero, Ne.symm h01, ↓reduceIte]
        rw [two_ind_ne h01, chiR_swap h3 (x 2) (x 0)]
        ring
      · simp only [hH, Ne.symm ha, Ne.symm hb, ha, ↓reduceIte]
        rw [two_ind_ne hb, hsw]
        ring
  simp only [hc, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte,
    sum_const, card_univ, nsmul_eq_mul, sumR_chi hR, sumR_chi_mul_ne hR h12,
    sumR_chi_mul_ne hR h01, sumR_chi_mul_ne hR h02]
  unfold Wsum
  rw [← hn]
  ring

/-- `2√n ≤ n/2048` for `n ≥ 2²⁴`. -/
theorem two_sqrt_le {n : ℝ} (hn : 16777216 ≤ n) : 2 * Real.sqrt n ≤ n / 2048 := by
  have h0 : (0 : ℝ) ≤ n := by linarith
  have hs : (4096 : ℝ) ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by norm_num) h0]; linarith
  have hsq := Real.mul_self_sqrt h0
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The polynomial inequality of the row bound** (exact row sum against `|H_F|`). -/
theorem row_poly_aux (n t u v ξ ζ W : ℝ) (hn : 16777216 ≤ n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) (hξ : ξ = 1 ∨ ξ = -1) (hζ : ζ = 1 ∨ ζ = -1)
    (hW : |W| ≤ 2 * Real.sqrt n) :
    |P0 n u v * (n + (1 - t)) + P1 n u v * ((1 - t) - 1) - ((1 - t) * P1 n u v) * W -
      (1 - (1 - t) * ζ) * (P0 n u v + P1 n u v * -ξ) + (1 + ξ) * (1 - (1 - t) * -1) * Qr n u v -
      n * (n - 1) * (n - 2) / 2| ≤ 5 * (n - 1) * (n - 2) := by
  have hW' := le_trans hW (two_sqrt_le hn)
  have e : ((1 - t) * P1 n u v) * W = P1 n u v * ((1 - t) * W) := by ring
  have hV : |(1 - t) * W| ≤ n / 2048 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
    nlinarith [abs_nonneg W]
  rw [e]
  have hs0 : 0 ≤ 1 - t := by linarith
  have hs1 : 1 - t ≤ 1 := by linarith
  clear e hW hW'
  generalize (1 - t) * W = V at hV ⊢
  generalize 1 - t = s at hs0 hs1 ⊢
  clear ht0 ht1
  unfold P0 P1 Qr
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
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hξ with rfl | rfl <;>
    rcases hζ with rfl | rfl <;> constructor <;> nlinarith

/-- **The row estimate of `lem:signed-components`(b)**: `|E_{y ∼ ν_F} U_{uv}(x, y) - 1| ≤ 10/p`
on `H_F`, for `p ≥ 2²⁴`, `0 ≤ t ≤ 1`, `u, v = ±1`, given the Weil bound `|W| ≤ 2√p` at the three
labels of `x` (`thm:weil`(a)). -/
theorem rowMean_bound (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hn : (16777216 : ℝ) ≤ Fintype.card F) {t u v : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) {x : Fin 3 → F} (hx : HF x)
    (hW : |Wsum (x 0) (x 1) (x 2)| ≤ 2 * Real.sqrt (Fintype.card F)) :
    |rowMean t u v x - 1| ≤ 10 / (Fintype.card F : ℝ) := by
  obtain ⟨h01, -, h12⟩ := HF_ne hx
  unfold rowMean
  rw [row_sum_eq hR h3 hx, Hcard_eq hR]
  have e1 : (χ (x 1 - x 0) : ℝ) = -χ (x 0 - x 1) := chiR_swap h3 _ _
  have e2 : (χ (x 0 - x 2) : ℝ) = -1 := by
    rw [chiR_swap h3, hx.2]; simp
  rw [e1, e2]
  have key := row_poly_aux (Fintype.card F) t u v _ _ _ hn ht0 ht1 hu hv
    (chiR_ne_cases (sub_ne_zero.mpr h01)) (chiR_ne_cases (sub_ne_zero.mpr h12)) hW
  set n : ℝ := (Fintype.card F : ℝ)
  have hH : 0 < n * (n - 1) * (n - 2) / 2 := by
    have : 0 < n - 2 := by linarith
    have : 0 < n - 1 := by linarith
    positivity
  rw [div_sub_one hH.ne', abs_div, abs_of_pos hH, div_le_div_iff₀ hH (by linarith)]
  calc _ ≤ 5 * (n - 1) * (n - 2) * n := mul_le_mul_of_nonneg_right key (by linarith)
    _ = 10 * (n * (n - 1) * (n - 2) / 2) := by ring

/-- **`|z_{uv} - 1| ≤ η` from the row estimate** (`lem:signed-components`(b): "averaging the row
estimate over `x`"). -/
theorem zMean_bound_of_row (hR : ringChar F ≠ 2) (h3n : 3 ≤ Fintype.card F) {t u v η : ℝ}
    (hrow : ∀ x : Fin 3 → F, HF x → |rowMean t u v x - 1| ≤ η) :
    |zMean (F := F) t u v - 1| ≤ η := by
  have hH : 0 < Hcard (F := F) := by
    rw [Hcard_eq hR]
    have : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast h3n
    have : 0 < (Fintype.card F : ℝ) - 2 := by linarith
    have : 0 < (Fintype.card F : ℝ) - 1 := by linarith
    have : 0 < (Fintype.card F : ℝ) := by linarith
    positivity
  have hc : Hcard (F := F) = ∑ x : Fin 3 → F, (if HF x then (1 : ℝ) else 0) := by
    unfold Hcard Hset
    rw [card_filter]
    push_cast
    rfl
  have hsum : ∑ p, Ukernel (F := F) t u v p =
      ∑ x : Fin 3 → F, (if HF x then rowMean t u v x * Hcard (F := F) else 0) := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    by_cases hx : HF x
    · simp only [hx, ↓reduceIte, rowMean]
      field_simp
    · simp only [hx, ↓reduceIte]
      exact sum_eq_zero fun y _ => by simp [Ukernel, hx]
  have hz : zMean (F := F) t u v - 1 =
      (∑ x : Fin 3 → F, (if HF x then rowMean t u v x - 1 else 0)) / Hcard (F := F) := by
    unfold zMean
    rw [hsum]
    have e : ∀ x : Fin 3 → F, (if HF x then rowMean t u v x - 1 else 0) =
        (if HF x then rowMean t u v x else 0) - (if HF x then (1 : ℝ) else 0) := by
      intro x; split_ifs <;> simp
    rw [sum_congr rfl fun x _ => e x, sum_sub_distrib, ← hc]
    have e2 : ∑ x : Fin 3 → F, (if HF x then rowMean t u v x * Hcard (F := F) else 0) =
        (∑ x : Fin 3 → F, (if HF x then rowMean t u v x else 0)) * Hcard (F := F) := by
      rw [sum_mul]; exact sum_congr rfl fun x _ => by split_ifs <;> simp
    rw [e2]
    field_simp
  rw [hz, abs_div, abs_of_pos hH, div_le_iff₀ hH, hc, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  by_cases hx : HF x
  · simp only [hx, ↓reduceIte, mul_one]; exact hrow x hx
  · simp [hx]

end Sarkozy.SignedEstimates
