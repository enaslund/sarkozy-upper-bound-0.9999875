module

public import Sarkozy.PrimeGram.OldLaw

@[expose] public section

/-!
# `lem:old-f-law`(b)(ii): `‖𝖠𝖡‖ ≤ 2q/(1 - q)` on `L²(ν_F)` (PG)

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(b)(ii): "The kernel `𝖠𝖡` depends on
`(x₀, x₂)` and `(y₀, y₂)` and is a product of two single cross edges; for independent uniform
labels it is a tensor product of two operators of norm `r`, and `lem:record:projection` with the
density `2/(1 - q)` of a directed edge on both sides gives the bound."

* `paley_sq_le`: `∑_a (∑_t χ(t - a) h(t))² ≤ p ∑_t h(t)²` (the Paley matrix has norm `√p`; from
  `∑_a χ(a - t) χ(a - t') = p [t = t'] - 1`).
* `sum_half_02`: a sum over halves of `φ(x) W(x₀, x₂)` is a sum over `(x₀, x₂)` of the
  conditional sums `F₁(x₀, x₂) = ∑_{x₁} φ(x)`.
* `sum_F1_sq`: `∑ F₁² ≤ (p - 2) ∑_{x ∈ H_F} f(x)²` (at most `p - 2` middle labels).
* **`abBound`**: `ABBound` holds for every finite field with `p ≡ 3 (mod 4)`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents
  Sarkozy.SignedEstimates Sarkozy.MiddleRecords

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

section AB

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)

include hR h3 in
/-- `∑_a χ(t - a) χ(t' - a) = p [t = t'] - 1`. -/
theorem chi_corr (t t' : F) :
    ∑ a, (χ (t - a) : ℝ) * (χ (t' - a) : ℝ) = (if t = t' then qF else 0) - 1 := by
  have e : ∀ a, (χ (t - a) : ℝ) * (χ (t' - a) : ℝ) = ((χ (a - t) * χ (a - t') : ℤ) : ℝ) := by
    intro a
    rw [chiR_swap h3 t a, chiR_swap h3 t' a]
    push_cast
    ring
  simp only [e]
  rw [← Int.cast_sum, sum_chi_mul_chi hR t t']
  split_ifs <;> push_cast <;> ring

include hR h3 in
/-- **The Paley matrix has norm `√p`**: `∑_a (∑_t χ(t - a) h(t))² ≤ p ∑_t h(t)²`. -/
theorem paley_sq_le (h : F → ℝ) :
    ∑ a, (∑ t, (χ (t - a) : ℝ) * h t) ^ 2 ≤ qF * ∑ t, h t ^ 2 := by
  have e : ∑ a, (∑ t, (χ (t - a) : ℝ) * h t) ^ 2 =
      ∑ t, ∑ t', h t * h t' * ∑ a, (χ (t - a) : ℝ) * (χ (t' - a) : ℝ) := by
    simp only [sq, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t' _ => ?_
    exact sum_congr rfl fun a _ => by ring
  rw [e]
  simp only [chi_corr hR h3, mul_sub, mul_ite, mul_zero, mul_one, sum_sub_distrib,
    sum_ite_eq, mem_univ, ↓reduceIte]
  have h1 : ∑ t, h t * h t * qF = qF * ∑ t, h t ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun t _ => by ring
  have h2 : ∑ t, ∑ t', h t * h t' = (∑ t, h t) ^ 2 := by
    rw [sq, sum_mul_sum]
  rw [h1, h2]
  nlinarith [sq_nonneg (∑ t, h t)]

include hR h3 in
/-- The same with the kernel `χ(a - t)`. -/
theorem paley_sq_le' (h : F → ℝ) :
    ∑ a, (∑ t, (χ (a - t) : ℝ) * h t) ^ 2 ≤ qF * ∑ t, h t ^ 2 := by
  have e : ∀ a, (∑ t, (χ (a - t) : ℝ) * h t) ^ 2 = (∑ t, (χ (t - a) : ℝ) * h t) ^ 2 := by
    intro a
    have : ∑ t, (χ (a - t) : ℝ) * h t = -∑ t, (χ (t - a) : ℝ) * h t := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun t _ => by rw [chiR_swap h3 a t]; ring
    rw [this, neg_sq]
  simp only [e]
  exact paley_sq_le hR h3 h

end AB

omit [Field F] [DecidableEq F] in
/-- Sums over halves of `φ(x) W(x₀, x₂)`. -/
theorem sum_half_02 (φ : (Fin 3 → F) → ℝ) (W : F → F → ℝ) :
    ∑ x, φ x * W (x 0) (x 2) = ∑ a, ∑ c, (∑ b, φ ![a, b, c]) * W a c := by
  rw [sum_triple]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_mul]
  rfl

theorem sum_hf_le (a c : F) : ∑ b, hfI (F := F) ![a, b, c] ≤ qF - 2 := by
  have hc2 : 2 ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F); omega
  have hq2 : (2 : ℝ) ≤ qF := by exact_mod_cast hc2
  by_cases hac : a = c
  · subst hac
    have h0 : ∀ b, hfI (F := F) ![a, b, a] = 0 := by
      intro b
      unfold hfI
      have : ¬ HF (F := F) ![a, b, a] := fun hx =>
        absurd (hx.1 (a₁ := 0) (a₂ := 2) (by simp)) (by decide)
      simp [this]
    simp only [h0, sum_const_zero]
    linarith
  · have hle : ∀ b, hfI (F := F) ![a, b, c] ≤ if b ≠ a ∧ b ≠ c then 1 else 0 := by
      intro b
      unfold hfI
      by_cases hx : HF (F := F) ![a, b, c]
      · have hinj := hx.1
        have h1 : b ≠ a := fun e => absurd (hinj (a₁ := 1) (a₂ := 0) (by simp [e])) (by decide)
        have h2 : b ≠ c := fun e => absurd (hinj (a₁ := 1) (a₂ := 2) (by simp [e])) (by decide)
        simp [hx, h1, h2]
      · simp only [hx, ↓reduceIte]
        split_ifs <;> norm_num
    calc ∑ b, hfI (F := F) ![a, b, c] ≤ ∑ b, (if b ≠ a ∧ b ≠ c then (1 : ℝ) else 0) :=
          sum_le_sum fun b _ => hle b
      _ = qF - 2 := by
          rw [sum_boole]
          have hsub : (univ.filter fun b : F => b ≠ a ∧ b ≠ c) = (univ.erase a).erase c := by
            ext b; simp [and_comm]
          rw [hsub, card_erase_of_mem (mem_erase.mpr ⟨Ne.symm hac, mem_univ c⟩),
            card_erase_of_mem (mem_univ a), card_univ]
          rw [Nat.sub_sub, Nat.cast_sub hc2]
          norm_num

/-- The conditional sums `F₁(a, c) = ∑_b 1_{H_F}(a, b, c) f(a, b, c)`. -/
noncomputable def F1 (f : (Fin 3 → F) → ℝ) (a c : F) : ℝ := ∑ b, hfI ![a, b, c] * f ![a, b, c]

theorem hfI_sq (x : Fin 3 → F) : hfI x * hfI x = hfI x := by
  unfold hfI; split_ifs <;> norm_num

/-- `∑ F₁² ≤ (p - 2) ∑_{x ∈ H_F} f(x)²`. -/
theorem sum_F1_sq (f : (Fin 3 → F) → ℝ) :
    ∑ a, ∑ c, F1 f a c ^ 2 ≤ (qF - 2) * ∑ x, hfI x * f x ^ 2 := by
  have hpt : ∀ a c, F1 f a c ^ 2 ≤ (qF - 2) * ∑ b, hfI ![a, b, c] * f ![a, b, c] ^ 2 := by
    intro a c
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun b => hfI (F := F) ![a, b, c])
      (fun b => hfI (F := F) ![a, b, c] * f ![a, b, c])
    have e1 : ∑ b, hfI (F := F) ![a, b, c] * (hfI ![a, b, c] * f ![a, b, c]) = F1 f a c := by
      unfold F1
      exact sum_congr rfl fun b _ => by rw [← mul_assoc, hfI_sq]
    have e2 : ∑ b, hfI (F := F) ![a, b, c] ^ 2 = ∑ b, hfI (F := F) ![a, b, c] :=
      sum_congr rfl fun b _ => by rw [sq, hfI_sq]
    have e3 : ∑ b, (hfI (F := F) ![a, b, c] * f ![a, b, c]) ^ 2 =
        ∑ b, hfI ![a, b, c] * f ![a, b, c] ^ 2 :=
      sum_congr rfl fun b _ => by rw [mul_pow, sq (hfI _), hfI_sq]
    rw [e1, e2, e3] at hcs
    have hS : 0 ≤ ∑ b, hfI (F := F) ![a, b, c] * f ![a, b, c] ^ 2 :=
      sum_nonneg fun b _ => mul_nonneg (by unfold hfI; split_ifs <;> norm_num) (sq_nonneg _)
    exact hcs.trans (mul_le_mul_of_nonneg_right (sum_hf_le a c) hS)
  calc ∑ a, ∑ c, F1 f a c ^ 2 ≤ ∑ a, ∑ c, (qF - 2) * ∑ b, hfI ![a, b, c] * f ![a, b, c] ^ 2 :=
        sum_le_sum fun a _ => sum_le_sum fun c _ => hpt a c
    _ = (qF - 2) * ∑ x, hfI x * f x ^ 2 := by
        rw [sum_triple, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_comm, mul_sum]

omit [Field F] [DecidableEq F] in
/-- Cauchy–Schwarz for double sums. -/
theorem dsum_abs_le (u v : F → F → ℝ) :
    |∑ a, ∑ c, u a c * v a c| ≤ √(∑ a, ∑ c, u a c ^ 2) * √(∑ a, ∑ c, v a c ^ 2) := by
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun p : F × F => u p.1 p.2) (fun p => v p.1 p.2)
  simp only [Fintype.sum_prod_type] at hcs
  rw [← Real.sqrt_mul (sum_nonneg fun a _ => sum_nonneg fun c _ => sq_nonneg _)]
  exact Real.abs_le_sqrt hcs

section ABproof

variable (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)

include hR h3 in
/-- `∑_{a,c} V(a, c)² ≤ p² ∑ G²` for `V(a, c) = ∑_{a',c'} G(a', c') χ(c' - a) χ(c - a')`. -/
theorem sum_V_sq (G : F → F → ℝ) :
    ∑ a, ∑ c, (∑ a', ∑ c', G a' c' * ((χ (c' - a) : ℝ) * (χ (c - a') : ℝ))) ^ 2 ≤
      qF ^ 2 * ∑ a, ∑ c, G a c ^ 2 := by
  set Hh : F → F → ℝ := fun c c' => ∑ a', (χ (c - a') : ℝ) * G a' c'
  have eV : ∀ a c, ∑ a', ∑ c', G a' c' * ((χ (c' - a) : ℝ) * (χ (c - a') : ℝ)) =
      ∑ c', (χ (c' - a) : ℝ) * Hh c c' := by
    intro a c
    rw [sum_comm]
    refine sum_congr rfl fun c' _ => ?_
    simp only [Hh, mul_sum]
    exact sum_congr rfl fun a' _ => by ring
  simp only [eV]
  rw [sum_comm]
  have hq : (0 : ℝ) ≤ qF := Nat.cast_nonneg _
  calc ∑ c, ∑ a, (∑ c', (χ (c' - a) : ℝ) * Hh c c') ^ 2 ≤ ∑ c, qF * ∑ c', Hh c c' ^ 2 :=
        sum_le_sum fun c _ => paley_sq_le hR h3 (Hh c)
    _ = qF * ∑ c', ∑ c, (∑ a', (χ (c - a') : ℝ) * G a' c') ^ 2 := by
        rw [← mul_sum, sum_comm]
    _ ≤ qF * ∑ c', qF * ∑ a', G a' c' ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun c' _ => paley_sq_le' hR h3 (fun a' => G a' c'))
          hq
    _ = qF ^ 2 * ∑ a, ∑ c, G a c ^ 2 := by
        rw [← mul_sum, sum_comm, ← mul_assoc, sq]

include hR h3 in
/-- **`lem:old-f-law`(b)(ii)**: `‖𝖠𝖡‖ ≤ 2q/(1 - q)` on `L²(ν_F)`, for every `p ≡ 3 (mod 4)`,
`p ≥ 19`. -/
theorem abBound (h19 : 19 ≤ Fintype.card F) : ABBound (F := F) := by
  intro f g
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have hH := Hcard_pos (F := F) hR h19
  set H := Hcard (F := F)
  set V : F → F → ℝ := fun a c => ∑ a', ∑ c', F1 g a' c' * ((χ (c' - a) : ℝ) * (χ (c - a') : ℝ))
  -- the identity
  have hE : E2 (fun x y => chA x y * chB x y) f g = (∑ a, ∑ c, F1 f a c * V a c) / H ^ 2 := by
    have e1 : E2 (fun x y => chA x y * chB x y) f g = (∑ x, (hfI x * f x) *
        ∑ y, (hfI y * g y) * ((χ (y 2 - x 0) : ℝ) * (χ (x 2 - y 0) : ℝ))) / H ^ 2 := by
      unfold E2 chA chB
      rw [sum_div]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum, sum_div]
      exact sum_congr rfl fun y _ => by ring
    rw [e1]
    congr 1
    have e2 : ∀ x : Fin 3 → F, ∑ y, (hfI y * g y) * ((χ (y 2 - x 0) : ℝ) * (χ (x 2 - y 0) : ℝ)) =
        V (x 0) (x 2) := by
      intro x
      rw [sum_half_02 (fun y => hfI y * g y)
        (fun a' c' => (χ (c' - x 0) : ℝ) * (χ (x 2 - a') : ℝ))]
      rfl
    simp only [e2]
    exact sum_half_02 (fun x => hfI x * f x) V
  rw [hE, abs_div, abs_of_pos (pow_pos hH 2)]
  have hcs := dsum_abs_le (F1 f) V
  have hF1 := sum_F1_sq f
  have hG1 := sum_F1_sq g
  have hV := sum_V_sq hR h3 (F1 g)
  set Sf := ∑ x, hfI x * f x ^ 2
  set Sg := ∑ x, hfI x * g x ^ 2
  have hSf : 0 ≤ Sf := sum_nonneg fun x _ => mul_nonneg (by unfold hfI; split_ifs <;> norm_num)
    (sq_nonneg _)
  have hSg : 0 ≤ Sg := sum_nonneg fun x _ => mul_nonneg (by unfold hfI; split_ifs <;> norm_num)
    (sq_nonneg _)
  have hp2 : (0 : ℝ) ≤ qF - 2 := by linarith
  have hq0 : (0 : ℝ) ≤ qF := by linarith
  -- `√(∑ F₁²) ≤ √(p - 2) √S_f`, `√(∑ V²) ≤ p √(p - 2) √S_g`
  have b1 : √(∑ a, ∑ c, F1 f a c ^ 2) ≤ √(qF - 2) * √Sf := by
    rw [← Real.sqrt_mul hp2]; exact Real.sqrt_le_sqrt hF1
  have b2 : √(∑ a, ∑ c, V a c ^ 2) ≤ qF * (√(qF - 2) * √Sg) := by
    calc √(∑ a, ∑ c, V a c ^ 2) ≤ √(qF ^ 2 * ((qF - 2) * Sg)) :=
          Real.sqrt_le_sqrt (hV.trans (mul_le_mul_of_nonneg_left hG1 (sq_nonneg _)))
      _ = qF * (√(qF - 2) * √Sg) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq0, Real.sqrt_mul hp2]
  have hbound : |∑ a, ∑ c, F1 f a c * V a c| ≤ qF * (qF - 2) * (√Sf * √Sg) := by
    have hs2 : √(qF - 2) * √(qF - 2) = qF - 2 := Real.mul_self_sqrt hp2
    calc _ ≤ √(∑ a, ∑ c, F1 f a c ^ 2) * √(∑ a, ∑ c, V a c ^ 2) := hcs
      _ ≤ (√(qF - 2) * √Sf) * (qF * (√(qF - 2) * √Sg)) :=
          mul_le_mul b1 b2 (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _))
      _ = qF * (√(qF - 2) * √(qF - 2)) * (√Sf * √Sg) := by ring
      _ = qF * (qF - 2) * (√Sf * √Sg) := by rw [hs2]
  -- the `ν`-norms
  have hEf : √(Enu (fun x => f x ^ 2)) = √Sf / √H := by
    unfold Enu; rw [← sum_div, Real.sqrt_div' _ hH.le]
  have hEg : √(Enu (fun x => g x ^ 2)) = √Sg / √H := by
    unfold Enu; rw [← sum_div, Real.sqrt_div' _ hH.le]
  rw [hEf, hEg]
  have hHe : H = qF * (qF - 1) * (qF - 2) / 2 := Hcard_eq hR
  have hsH : √H * √H = H := Real.mul_self_sqrt hH.le
  have hsHp : 0 < √H := Real.sqrt_pos.mpr hH
  have hq1 : (0 : ℝ) < qF - 1 := by linarith
  have hqF : (0 : ℝ) < qF := by linarith
  rw [div_le_iff₀ (pow_pos hH 2)]
  have hRHS : 2 * qF⁻¹ / (1 - qF⁻¹) * (√Sf / √H * (√Sg / √H)) * H ^ 2 =
      qF * (qF - 2) * (√Sf * √Sg) := by
    have e1 : √Sf / √H * (√Sg / √H) = √Sf * √Sg / H := by rw [div_mul_div_comm, hsH]
    rw [e1, hHe]
    field_simp
  rw [hRHS]
  exact hbound

end ABproof

end Sarkozy.PrimeGram
