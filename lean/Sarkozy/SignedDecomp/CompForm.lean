module

public import Sarkozy.SignedDecomp.CompTools
public import Sarkozy.SignedComponents.Components

@[expose] public section

/-!
# The bilinear forms of the unnormalized component kernel and of the query coupling (SD2)

`paper/sections/21_middle_records.tex`, `lem:signed-components`, `prop:signed-bounds`(c), Step 1.

B8's `Ukernel t u v = 1_{H_F} ⊗ 1_{H_F} · V`, with
`V = 2·1[x₁ → y₀](1 + (1 - t)𝖡)(1 + u𝖣)(1 + v𝖠)` (`Vk`). Since
`2·1[χ(c) = 1] = 1 + χ(c) - 1[c = 0]`,
`V = 1 + T_𝖡 + T_𝖣 + T_𝖠 + 𝖢 W' - 1[y₀ = x₁] W'` (`Vk_split`), with
`W' = (1 + (1 - t)𝖡)(1 + u𝖣)(1 + v𝖠)`, `T_𝖡 = (1 - t)𝖡(1 + u𝖣)(1 + v𝖠)`, `T_𝖣 = u𝖣(1 + v𝖠)`,
`T_𝖠 = v𝖠`. Each of the four channel terms has a separable cross character (`separable_bound`,
constants `4, 2, 1, 8`) and the coincidence term passes the Schur test (`8p²`), so
* **`Vk_form`**: `|∑ g V f - (∑ g)(∑ f)| ≤ (15√p + 8) p² ‖g‖ ‖f‖` (unnormalized `ℓ²`), for
  `0 ≤ t ≤ 1` and `|u|, |v| ≤ 1`;
* **`Jker_form`**: for B8's `J_C = 2p/(p - 1)·1[x₁ → y₀]`,
  `|∑ G J F - p/(p - 1)(∑ G)(∑ F)| ≤ p/(p - 1)(√p + 1) p² ‖G‖ ‖F‖`.
-/

open Finset

namespace Sarkozy.SignedDecomp

open Sarkozy.SignedComponents

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-- `V = 2·1[x₁ → y₀](1 + (1 - t)𝖡)(1 + u𝖣)(1 + v𝖠)`. -/
noncomputable def Vk (t u v : ℝ) (x y : Fin 3 → F) : ℝ :=
  2 * (if χ (y 0 - x 1) = 1 then 1 else 0) * (1 + (1 - t) * (χ (x 2 - y 0) : ℝ)) *
    (1 + u * (χ (y 1 - x 0) : ℝ)) * (1 + v * (χ (y 2 - x 0) : ℝ))

/-- `W' = (1 + (1 - t)𝖡)(1 + u𝖣)(1 + v𝖠)`. -/
noncomputable def Wp (t u v : ℝ) (x y : Fin 3 → F) : ℝ :=
  (1 + (1 - t) * (χ (x 2 - y 0) : ℝ)) * (1 + u * (χ (y 1 - x 0) : ℝ)) *
    (1 + v * (χ (y 2 - x 0) : ℝ))

theorem Ukernel_eq (t u v : ℝ) (x y : Fin 3 → F) :
    Ukernel t u v (x, y) = (if HF x ∧ HF y then 1 else 0) * Vk t u v x y := rfl

theorem one_add_chi_bound {s : ℝ} (hs : |s| ≤ 1) (a : F) : |1 + s * (χ a : ℝ)| ≤ 2 := by
  have := abs_le.mp hs
  rw [abs_le]
  rcases chi_cases a with h | h | h <;> rw [h] <;> push_cast <;> constructor <;> linarith

theorem chi_abs_le (a : F) : |(χ a : ℝ)| ≤ 1 := by
  rcases chi_cases a with h | h | h <;> rw [h] <;> norm_num

theorem Wp_bound {t u v : ℝ} (ht : |1 - t| ≤ 1) (hu : |u| ≤ 1) (hv : |v| ≤ 1) (x y : Fin 3 → F) :
    |Wp t u v x y| ≤ 8 := by
  unfold Wp
  rw [abs_mul, abs_mul]
  have h1 := one_add_chi_bound ht (x 2 - y 0)
  have h2 := one_add_chi_bound hu (y 1 - x 0)
  have h3 := one_add_chi_bound hv (y 2 - x 0)
  calc |1 + (1 - t) * (χ (x 2 - y 0) : ℝ)| * |1 + u * (χ (y 1 - x 0) : ℝ)| *
        |1 + v * (χ (y 2 - x 0) : ℝ)| ≤ 2 * 2 * 2 := by gcongr
    _ = 8 := by norm_num

/-- `2·1[χ(c) = 1] = 1 + χ(c) - 1[c = 0]`. -/
theorem two_ind (c : F) :
    2 * (if χ c = 1 then (1 : ℝ) else 0) = 1 + (χ c : ℝ) - (if c = 0 then 1 else 0) := by
  rcases chi_cases c with h | h | h
  · have hc : c = 0 := (quadraticChar_eq_zero_iff).mp h
    simp [hc]
  · have hc : c ≠ 0 := fun hc => by rw [hc, quadraticChar_zero] at h; norm_num at h
    simp [h, hc]; norm_num
  · have hc : c ≠ 0 := fun hc => by rw [hc, quadraticChar_zero] at h; norm_num at h
    simp [h, hc]

/-- **The split of `V`.** -/
theorem Vk_split (t u v : ℝ) (x y : Fin 3 → F) :
    Vk t u v x y = 1 + (1 - t) * (χ (x 2 - y 0) : ℝ) * ((1 + u * (χ (y 1 - x 0) : ℝ)) *
      (1 + v * (χ (y 2 - x 0) : ℝ))) + u * (χ (y 1 - x 0) : ℝ) * (1 + v * (χ (y 2 - x 0) : ℝ)) +
      v * (χ (y 2 - x 0) : ℝ) + (χ (y 0 - x 1) : ℝ) * Wp t u v x y -
      (if y 0 - x 1 = 0 then 1 else 0) * Wp t u v x y := by
  unfold Vk
  rw [two_ind]
  unfold Wp
  ring

/-- `#{y : y_i = c} = p²`. -/
theorem card_coord (i : Fin 3) (c : F) :
    ∑ y : Fin 3 → F, (if y i = c then (1 : ℝ) else 0) = qF ^ 2 := by
  classical
  have h := sum_update i (fun y : Fin 3 → F => if y i = c then (1 : ℝ) else 0)
  have e : ∀ y : Fin 3 → F, ∑ a : F, (if Function.update y i a i = c then (1 : ℝ) else 0) = 1 :=
    fun y => by simp only [Function.update_self]; simp
  rw [sum_congr rfl fun y _ => e y, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [Fintype.card_fun, Fintype.card_fin] at h
  have hq : (0 : ℝ) < qF := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  push_cast at h
  have : qF * (qF ^ 2 - ∑ y : Fin 3 → F, (if y i = c then (1 : ℝ) else 0)) = 0 := by
    rw [mul_sub, ← h]; ring
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hq.ne'
  · linarith

section Bounds

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)

/-- The norm `√(∑ g²)`. -/
noncomputable abbrev nrm {α : Type} [Fintype α] (g : α → ℝ) : ℝ := √(∑ x, g x ^ 2)

include hR h3 in
/-- **The form of `V`** (unnormalized `ℓ²`). -/
theorem Vk_form {t u v : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (g f : (Fin 3 → F) → ℝ) :
    |∑ x, ∑ y, g x * Vk t u v x y * f y - (∑ x, g x) * ∑ y, f y| ≤
      (15 * √qF + 8) * qF ^ 2 * (nrm g * nrm f) := by
  have ht : |1 - t| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hq : (0 : ℝ) ≤ qF := Nat.cast_nonneg _
  have hN : 0 ≤ nrm g * nrm f := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set KB : (Fin 3 → F) → (Fin 3 → F) → ℝ := fun x y => (1 - t) * (χ (x 2 - y 0) : ℝ) *
    ((1 + u * (χ (y 1 - x 0) : ℝ)) * (1 + v * (χ (y 2 - x 0) : ℝ)))
  set KD : (Fin 3 → F) → (Fin 3 → F) → ℝ := fun x y => u * (χ (y 1 - x 0) : ℝ) *
    (1 + v * (χ (y 2 - x 0) : ℝ))
  set KA : (Fin 3 → F) → (Fin 3 → F) → ℝ := fun x y => v * (χ (y 2 - x 0) : ℝ)
  set KC : (Fin 3 → F) → (Fin 3 → F) → ℝ := fun x y => (χ (y 0 - x 1) : ℝ) * Wp t u v x y
  set K0 : (Fin 3 → F) → (Fin 3 → F) → ℝ := fun x y =>
    (if y 0 - x 1 = 0 then 1 else 0) * Wp t u v x y
  have hsplit : ∑ x, ∑ y, g x * Vk t u v x y * f y - (∑ x, g x) * ∑ y, f y =
      ∑ x, ∑ y, g x * KB x y * f y + ∑ x, ∑ y, g x * KD x y * f y +
        ∑ x, ∑ y, g x * KA x y * f y + ∑ x, ∑ y, g x * KC x y * f y -
        ∑ x, ∑ y, g x * K0 x y * f y := by
    rw [sum_mul_sum]
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [Vk_split]
    ring
  -- the four separable terms
  have hB := separable_bound hR h3 2 0 KB (fun _ _ _ => 1)
    (fun x y b => -((1 - t) * ((1 + u * (χ (y 1 - x 0) : ℝ)) * (1 + v * (χ (y 2 - x 0) : ℝ)))))
    (c₁ := 1) (c₂ := 4) (fun _ _ _ => by norm_num)
    (fun x y b => by
      rw [abs_neg, abs_mul, abs_mul]
      have h1 := one_add_chi_bound hu (y 1 - x 0)
      have h2 := one_add_chi_bound hv (y 2 - x 0)
      calc |1 - t| * (|1 + u * (χ (y 1 - x 0) : ℝ)| * |1 + v * (χ (y 2 - x 0) : ℝ)|)
          ≤ 1 * (2 * 2) := by gcongr
        _ = 4 := by norm_num)
    (fun x y a b => by
      simp (config := { decide := true }) only [KB, Function.update_apply, ↓reduceIte]
      rw [Sarkozy.SignedEstimates.chiR_swap h3]
      ring) g f
  have hD := separable_bound hR h3 0 1 KD (fun x y a => 1 + v * (χ (y 2 - a) : ℝ))
    (fun _ _ _ => u) (c₁ := 2) (c₂ := 1) (fun x y a => one_add_chi_bound hv _) (fun _ _ _ => hu)
    (fun x y a b => by
      simp (config := { decide := true }) only [KD, Function.update_apply, ↓reduceIte]
      ring) g f
  have hA := separable_bound hR h3 0 2 KA (fun _ _ _ => 1) (fun _ _ _ => v) (c₁ := 1) (c₂ := 1)
    (fun _ _ _ => by norm_num) (fun _ _ _ => hv)
    (fun x y a b => by
      simp (config := { decide := true }) only [KA, Function.update_apply, ↓reduceIte]
      ring) g f
  have hC := separable_bound hR h3 1 0 KC (fun _ _ _ => 1) (fun x y b => Wp t u v x
    (Function.update y 0 b)) (c₁ := 1) (c₂ := 8) (fun _ _ _ => by norm_num)
    (fun x y b => Wp_bound ht hu hv _ _)
    (fun x y a b => by
      simp (config := { decide := true }) only [KC, Wp, Function.update_apply, ↓reduceIte]
      ring) g f
  -- the coincidence term
  have hpt : ∀ x y, |K0 x y| ≤ 8 * (if y 0 = x 1 then 1 else 0) := by
    intro x y
    by_cases h : y 0 = x 1
    · have h' : y 0 - x 1 = 0 := sub_eq_zero.mpr h
      have e : K0 x y = Wp t u v x y := by simp only [K0, h', ↓reduceIte, one_mul]
      rw [e]
      simp only [h, ↓reduceIte, mul_one]
      exact Wp_bound ht hu hv x y
    · have h' : y 0 - x 1 ≠ 0 := sub_ne_zero.mpr h
      simp [K0, h', h]
  have hrow : ∀ x, ∑ y, |K0 x y| ≤ 8 * qF ^ 2 := by
    intro x
    calc ∑ y, |K0 x y| ≤ ∑ y : Fin 3 → F, 8 * (if y 0 = x 1 then (1 : ℝ) else 0) :=
          sum_le_sum fun y _ => hpt x y
      _ = 8 * qF ^ 2 := by rw [← mul_sum, card_coord]
  have hcol : ∀ y, ∑ x, |K0 x y| ≤ 8 * qF ^ 2 := by
    intro y
    calc ∑ x, |K0 x y| ≤ ∑ x : Fin 3 → F, 8 * (if x 1 = y 0 then (1 : ℝ) else 0) :=
          sum_le_sum fun x _ => by
            have := hpt x y
            simp only [eq_comm (a := y 0)] at this
            exact this
      _ = 8 * qF ^ 2 := by rw [← mul_sum, card_coord]
  have h0 := schur_bound K0 (by positivity) hrow hcol g f
  rw [hsplit]
  have e : (15 * √qF + 8) * qF ^ 2 * (nrm g * nrm f) =
      1 * 4 * (√qF * qF ^ 2) * (nrm g * nrm f) + 2 * 1 * (√qF * qF ^ 2) * (nrm g * nrm f) +
      1 * 1 * (√qF * qF ^ 2) * (nrm g * nrm f) + 1 * 8 * (√qF * qF ^ 2) * (nrm g * nrm f) +
      8 * qF ^ 2 * (nrm g * nrm f) := by ring
  rw [e]
  refine (abs_sub _ _).trans (add_le_add ?_ h0)
  refine (abs_add_le _ _).trans (add_le_add ?_ hC)
  refine (abs_add_le _ _).trans (add_le_add ?_ hA)
  exact (abs_add_le _ _).trans (add_le_add hB hD)

include hR h3 in
/-- **The form of B8's `J_C`** (unnormalized `ℓ²`):
`|∑ G J F - p/(p - 1)(∑ G)(∑ F)| ≤ p/(p - 1)(√p + 1)p² ‖G‖ ‖F‖`. -/
theorem Jker_form (G H : (Fin 3 → F) → ℝ) :
    |∑ x, ∑ y, G x * Jker (x, y) * H y - qF / (qF - 1) * ((∑ x, G x) * ∑ y, H y)| ≤
      qF / (qF - 1) * ((√qF + 1) * qF ^ 2) * (nrm G * nrm H) := by
  have hq1 : (1 : ℝ) < qF := by
    have : 2 ≤ Fintype.card F := by omega
    exact_mod_cast this
  have hq : (0 : ℝ) ≤ qF := by linarith
  have hk : 0 ≤ qF / (qF - 1) := div_nonneg hq (by linarith)
  set KC : (Fin 3 → F) → (Fin 3 → F) → ℝ := fun x y => (χ (y 0 - x 1) : ℝ)
  set K0 : (Fin 3 → F) → (Fin 3 → F) → ℝ := fun x y => if y 0 - x 1 = 0 then 1 else 0
  have hsplit : ∑ x, ∑ y, G x * Jker (x, y) * H y - qF / (qF - 1) * ((∑ x, G x) * ∑ y, H y) =
      qF / (qF - 1) * (∑ x, ∑ y, G x * KC x y * H y - ∑ x, ∑ y, G x * K0 x y * H y) := by
    have hpt : ∀ x y, G x * Jker (x, y) * H y = qF / (qF - 1) * (G x * H y) +
        qF / (qF - 1) * (G x * KC x y * H y) - qF / (qF - 1) * (G x * K0 x y * H y) := by
      intro x y
      have e : Jker (x, y) = qF / (qF - 1) * (2 * (if χ (y 0 - x 1) = 1 then (1 : ℝ) else 0)) := by
        unfold Jker; ring
      rw [e, two_ind]
      simp only [KC, K0]
      ring
    simp only [hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum]
    rw [← sum_mul]
    ring
  have hC := separable_bound hR h3 1 0 KC (fun _ _ _ => 1) (fun _ _ _ => 1) (c₁ := 1) (c₂ := 1)
    (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)
    (fun x y a b => by
      simp (config := { decide := true }) only [KC, Function.update_apply, ↓reduceIte]
      ring) G H
  have hpt : ∀ x y, |K0 x y| = if y 0 = x 1 then 1 else 0 := by
    intro x y
    by_cases h : y 0 = x 1
    · simp [K0, h]
    · have h' : y 0 - x 1 ≠ 0 := sub_ne_zero.mpr h
      simp [K0, h', h]
  have hrow : ∀ x, ∑ y, |K0 x y| ≤ qF ^ 2 := fun x => by
    simp only [hpt]; rw [card_coord]
  have hcol : ∀ y, ∑ x, |K0 x y| ≤ qF ^ 2 := fun y => by
    simp only [hpt, eq_comm (a := y 0)]; rw [card_coord]
  have h0 := schur_bound K0 (by positivity) hrow hcol G H
  rw [hsplit, abs_mul, abs_of_nonneg hk, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hk
  refine (abs_sub _ _).trans ?_
  have e : (√qF + 1) * qF ^ 2 * (nrm G * nrm H) =
      1 * 1 * (√qF * qF ^ 2) * (nrm G * nrm H) + qF ^ 2 * (nrm G * nrm H) := by ring
  rw [e]
  exact add_le_add hC h0

end Bounds

end Sarkozy.SignedDecomp
