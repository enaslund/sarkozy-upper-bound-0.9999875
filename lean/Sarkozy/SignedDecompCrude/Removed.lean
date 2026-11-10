module

public import Sarkozy.SignedDecompCrude.Reduce
public import Sarkozy.SignedDecomp.CompTools

@[expose] public section

/-!
# The removed query of the signed record by the Schur test, with a crude constant (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 2 ("For the removed
query ... By the Schur test the removed query has norm at most `k_col q`").

* **`E2_of_l2`**: an `ℓ²(𝔽_p³)` bound `|∑ G K H| ≤ c p² ‖G‖ ‖H‖` gives
  `|E_{ν⊗ν}[f K g]| ≤ (2c/Z) q ‖f‖_ν ‖g‖_ν`, `Z = (1 - q)(1 - 2q)` (`|H_F| = p(p-1)(p-2)/2`).
* **`krq_abs_le`**: `|K_rq| ≤ 4(2 - t) 1[y₀ = x₁]` (`|1 + (1 - t)𝖡| ≤ 2 - t`,
  `|1 + 𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣| ≤ 4`).
* **`removedBound_crude`**: rows and columns of `K_rq` have mass at most `4(2 - t)p²` (the paper's
  conditional means give `(9/4)` in place of `4(2 - t)`, relative to `p²`, after averaging), so
  by SD2's `schur_bound`, **`RemovedBound t (8(2 - t)/Z)`** for `0 ≤ t ≤ 1`. At `t = 127/500`
  this is `13.97/Z` against the paper's `k_col = 9/4`.
-/

open Finset Matrix

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.SignedEstimates Sarkozy.SignedComponents Sarkozy.SignedDecomp

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-- **From `ℓ²(𝔽_p³)` to `L²(ν_F)`**: if `|∑ G K H| ≤ c p² ‖G‖₂ ‖H‖₂` for all `G, H`, then
`|E_{ν⊗ν}[f K g]| ≤ (2c/((1 - q)(1 - 2q))) q ‖f‖_ν ‖g‖_ν`. -/
theorem E2_of_l2 (hR : ringChar F ≠ 2) (h19 : 19 ≤ Fintype.card F)
    (K : (Fin 3 → F) → (Fin 3 → F) → ℝ) {c : ℝ}
    (hK : ∀ G H : (Fin 3 → F) → ℝ, |∑ x, ∑ y, G x * K x y * H y| ≤
      c * qF ^ 2 * (√(∑ x, G x ^ 2) * √(∑ y, H y ^ 2)))
    (f g : (Fin 3 → F) → ℝ) :
    |E2 K f g| ≤ 2 * c / ((1 - qF⁻¹) * (1 - 2 * qF⁻¹)) * qF⁻¹ *
      (√(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2))) := by
  have hH := Hcard_pos (F := F) hR h19
  set H := Hcard (F := F) with hHdef
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have e : E2 K f g = (∑ x, ∑ y, (hfI x * f x) * K x y * (hfI y * g y)) / H ^ 2 := by
    unfold E2
    rw [sum_div]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    ring
  have hn : ∀ u : (Fin 3 → F) → ℝ, ∑ x, (hfI x * u x) ^ 2 = H * Enu (fun x => u x ^ 2) := by
    intro u
    unfold Enu
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_pow, sq (hfI x), hfI_sq, ← hHdef]
    field_simp
  have hb := hK (fun x => hfI x * f x) (fun y => hfI y * g y)
  rw [hn f, hn g, Real.sqrt_mul hH.le, Real.sqrt_mul hH.le] at hb
  have hsH : √H * √H = H := Real.mul_self_sqrt hH.le
  have hEf := Real.sqrt_nonneg (Enu (fun x => f x ^ 2))
  have hEg := Real.sqrt_nonneg (Enu (fun x => g x ^ 2))
  have hcoef : c * qF ^ 2 / H = 2 * c / ((1 - qF⁻¹) * (1 - 2 * qF⁻¹)) * qF⁻¹ := by
    rw [hHdef, Hcard_eq hR]
    have h0 : qF ≠ 0 := by intro h; rw [h] at h19'; norm_num at h19'
    have h1 : qF - 1 ≠ 0 := by intro h; linarith
    have h2 : qF - 2 ≠ 0 := by intro h; linarith
    have h1' : 1 - qF⁻¹ ≠ 0 := by
      rw [sub_ne_zero]; intro h; apply h1; field_simp at h; linarith
    have h2' : 1 - 2 * qF⁻¹ ≠ 0 := by
      rw [sub_ne_zero]; intro h; apply h2; field_simp at h; linarith
    field_simp
  rw [e, abs_div, abs_of_pos (pow_pos hH 2), div_le_iff₀ (pow_pos hH 2), ← hcoef]
  calc |∑ x, ∑ y, (hfI x * f x) * K x y * (hfI y * g y)|
      ≤ c * qF ^ 2 * (√H * √(Enu (fun x => f x ^ 2)) * (√H * √(Enu (fun x => g x ^ 2)))) := hb
    _ = c * qF ^ 2 / H * (√(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2))) * H ^ 2 := by
        field_simp
        rw [Real.sq_sqrt hH.le]
        ring

/-- **`|K_rq| ≤ 4(2 - t) 1[y₀ = x₁]`** for `0 ≤ t ≤ 1`. -/
theorem krq_abs_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x y : Fin 3 → F) :
    |Krq t x y| ≤ (if y 0 = x 1 then 1 else 0) * (4 * (2 - t)) := by
  have hA := abs_le.mp (chi_abs_le (y 2 - x 0))
  have hB := abs_le.mp (chi_abs_le (x 2 - y 0))
  have hD := abs_le.mp (chi_abs_le (y 1 - x 0))
  have h1 : |1 + (1 - t) * PrimeGram.chB x y| ≤ 2 - t := by
    unfold PrimeGram.chB
    rw [abs_le]
    constructor <;> nlinarith
  have h2 : |1 + chD x y + (1 + t) * PrimeGram.chA x y +
      (1 - t) * (PrimeGram.chA x y * chD x y)| ≤ 4 := by
    unfold PrimeGram.chA chD
    have hAD : |(χ (y 2 - x 0) : ℝ) * χ (y 1 - x 0)| ≤ 1 := by
      rw [abs_mul]
      have := chi_abs_le (y 2 - x 0)
      have := chi_abs_le (y 1 - x 0)
      nlinarith [abs_nonneg ((χ (y 2 - x 0) : ℝ)), abs_nonneg ((χ (y 1 - x 0) : ℝ))]
    have hAD' := abs_le.mp hAD
    rw [abs_le]
    constructor <;> nlinarith
  unfold Krq
  rw [abs_mul]
  by_cases h : y 0 = x 1
  · have h' : y 0 - x 1 = 0 := sub_eq_zero.mpr h
    have hl : (if y 0 - x 1 = 0 then (1 : ℝ) else 0) = 1 := by simp [h']
    have hr : (if y 0 = x 1 then (1 : ℝ) else 0) = 1 := by simp [h]
    rw [hl, hr, abs_one, one_mul, one_mul, abs_mul]
    calc _ ≤ (2 - t) * 4 := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
      _ = 4 * (2 - t) := by ring
  · have h' : ¬ (y 0 - x 1 = 0) := fun e => h (sub_eq_zero.mp e)
    have hl : (if y 0 - x 1 = 0 then (1 : ℝ) else 0) = 0 := by simp [h']
    have hr : (if y 0 = x 1 then (1 : ℝ) else 0) = 0 := by simp [h]
    rw [hl, hr, abs_zero, zero_mul, zero_mul]

/-- **The removed query, crude** (`prop:signed-bounds`(c), Step 2, by the Schur test with the
masses `4(2 - t)p²`): `RemovedBound t (8(2 - t)/((1 - q)(1 - 2q)))` for `0 ≤ t ≤ 1`. -/
theorem removedBound_crude (hR : ringChar F ≠ 2) (h19 : 19 ≤ Fintype.card F) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    RemovedBound (F := F) t (2 * (4 * (2 - t)) / ((1 - qF⁻¹) * (1 - 2 * qF⁻¹))) := by
  intro f g
  refine E2_of_l2 hR h19 (Krq t) (c := 4 * (2 - t)) ?_ f g
  intro G H
  have hb := krq_abs_le (F := F) ht0 ht1
  have hrow : ∀ x : Fin 3 → F, ∑ y, |Krq t x y| ≤ 4 * (2 - t) * qF ^ 2 := by
    intro x
    calc ∑ y, |Krq t x y| ≤ ∑ y, (if y 0 = x 1 then (1 : ℝ) else 0) * (4 * (2 - t)) :=
          sum_le_sum fun y _ => hb x y
      _ = 4 * (2 - t) * qF ^ 2 := by rw [← sum_mul, card_coord 0 (x 1)]; ring
  have hcol : ∀ y : Fin 3 → F, ∑ x, |Krq t x y| ≤ 4 * (2 - t) * qF ^ 2 := by
    intro y
    have e : ∀ x : Fin 3 → F, (if y 0 = x 1 then (1 : ℝ) else 0) =
        (if x 1 = y 0 then (1 : ℝ) else 0) := by
      intro x
      by_cases h : y 0 = x 1
      · simp [h]
      · have h' : ¬ x 1 = y 0 := fun e => h e.symm
        simp [h, h']
    calc ∑ x, |Krq t x y| ≤ ∑ x, (if y 0 = x 1 then (1 : ℝ) else 0) * (4 * (2 - t)) :=
          sum_le_sum fun x _ => hb x y
      _ = 4 * (2 - t) * qF ^ 2 := by
          simp only [e]
          rw [← sum_mul, card_coord 1 (y 0)]; ring
  have hR0 : 0 ≤ 4 * (2 - t) * qF ^ 2 := by
    have : 0 ≤ qF ^ 2 := sq_nonneg _
    nlinarith
  exact schur_bound (Krq t) hR0 hrow hcol G H

end Sarkozy.SignedDecompCrude
