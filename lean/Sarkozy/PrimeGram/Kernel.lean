module

public import Sarkozy.PrimeGram.Gram

@[expose] public section

/-!
# `O₀` is the natural operator of the leading kernel `𝖫 = 𝖠 + 𝖡` (PG)

`paper/sections/21_middle_records.tex`, proof of `lem:old-f-law`(e),(f), paragraph "Transport":
"the natural operator of a kernel that depends on `y` only through `y_j` is `A V^*_{j,m}` …; so
`N_𝖫 = V₀PV^*_{2,m} - V₂PV^*_{0,m} = O₀`", with the channels `𝖠 = χ(y₂ - x₀)`, `𝖡 = χ(x₂ - y₀)`
of `eq:middle:channels`.

* **`oForm_eq_kernel`**: for **any** weights `m` on the half triples and all `u, v`,
  `⟨u, O₀ v⟩_m = ∑_{x,y} m(x) m(y) u(x) v(y) (χ(y₂ - x₀) + χ(x₂ - y₀))`.
* `oForm_symm`, `lForm_skew`: `O₀` is self-adjoint and `L^m_t` is skew in `L²(m)`.

So the operator `O₀` of `OldDecomp` (built from the adjoints of the features) is exactly the
paper's natural operator of `𝖫` relative to `m ⊗ m`, and `OldDecomp` is the paper's
`lem:old-f-law`(f): `Π_⊥ T_old Π_⊥ = N_𝖫 + R_o`, `‖R_o‖ ≤ e_o q`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.TraceMixing Sarkozy.MiddleRecords Sarkozy.SignedEstimates

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

omit [Field F] in
theorem sum_coord (m u : (Fin 3 → F) → ℝ) (j : Fin 3) (G : F → ℝ) :
    ∑ s, (∑ x, m x * (if x j = s then u x else 0)) * G s = ∑ x, m x * u x * G (x j) := by
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

omit [Field F] in
theorem sum_coord' (m u : (Fin 3 → F) → ℝ) (j : Fin 3) (G : F → ℝ) :
    ∑ s, G s * (∑ x, m x * (if x j = s then u x else 0)) = ∑ x, m x * u x * G (x j) := by
  rw [← sum_coord]
  exact sum_congr rfl fun s _ => mul_comm _ _

omit [DecidableEq F] in
theorem uip_qF_right (h k : F → ℝ) : uip h (fun s => qF * k s) = ∑ s, h s * k s := by
  unfold uip
  have hq : qF ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [mul_sum]
  refine sum_congr rfl fun s _ => ?_
  field_simp

omit [Field F] [DecidableEq F] in
theorem uip_cen_left {k : F → ℝ} (hk : ∑ a, k a = 0) (h : F → ℝ) : uip (cen h) k = uip h k := by
  rw [uip_comm, uip_cen hk, uip_comm]

omit [Field F] in
/-- `V₀^{*m} u = Π₀ (p U_u)`, `U_u(s) = ∑_{x₀ = s} m(x) u(x)`. -/
theorem Wa_eq (m u : (Fin 3 → F) → ℝ) :
    Wa m u = cen (fun s => qF * ∑ x, m x * (if x 0 = s then u x else 0)) := by
  unfold Wa adj mip V0 delta
  congr 1
  funext s
  congr 1
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

/-- `A₁^{*m} v = s ↦ ∑_y m(y) χ(s - y₂) v(y)` (already mean zero). -/
theorem Ba0_eq (hR : ringChar F ≠ 2) (m v : (Fin 3 → F) → ℝ) :
    Ba m 0 v = fun s => ∑ y, m y * (χ (s - y 2) : ℝ) * v y := by
  have hq : qF ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e : (fun s => qF * mip m (arm 0 (delta s)) v) =
      fun s => ∑ y, m y * (χ (s - y 2) : ℝ) * v y := by
    funext s
    simp only [arm, Matrix.cons_val_zero, A1, mip, paleyOp, delta, mul_ite, mul_one, mul_zero,
      sum_ite_eq', mem_univ, ↓reduceIte, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    field_simp
  have hs : ∑ s, (∑ y, m y * (χ (s - y 2) : ℝ) * v y) = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun y _ => ?_
    have := sumR_chi hR (y 2)
    rw [← sum_mul, ← mul_sum, this, mul_zero, zero_mul]
  unfold Ba adj
  rw [e]
  funext s
  unfold cen
  rw [hs, mul_zero, sub_zero]

/-- **`N_𝖫 = O₀`** (proof of `lem:old-f-law`(e),(f), "Transport"): for any weights `m` and all
`u, v`, `⟨u, O₀ v⟩_m = ∑_{x,y} m(x) m(y) u(x) v(y) (𝖠 + 𝖡)(x, y)`, with
`𝖠 = χ(y₂ - x₀)` and `𝖡 = χ(x₂ - y₀)`. -/
theorem oForm_eq_kernel (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (m u v : (Fin 3 → F) → ℝ) :
    oForm m u v = ∑ x, ∑ y, m x * m y * u x * v y *
      ((χ (y 2 - x 0) : ℝ) + (χ (x 2 - y 0) : ℝ)) := by
  have hX : ∀ w : (Fin 3 → F) → ℝ, ∑ s, Ba m 0 w s = 0 := fun w => sum_Ba m 0 w
  have T1 : uip (Ba m 0 u) (Wa m v) =
      ∑ x, ∑ y, m x * m y * u x * v y * (χ (y 0 - x 2) : ℝ) := by
    rw [Wa_eq m v, uip_cen (hX u), uip_qF_right, sum_coord', Ba0_eq hR, sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun y _ => by ring
  have T2 : uip (Wa m u) (Ba m 0 v) =
      ∑ x, ∑ y, m x * m y * u x * v y * (χ (x 0 - y 2) : ℝ) := by
    rw [Wa_eq m u, uip_cen_left (hX v), uip_comm, uip_qF_right, sum_coord', Ba0_eq hR]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun y _ => by ring
  unfold oForm
  rw [T1, T2, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [chiR_swap h3 (x 0) (y 2), chiR_swap h3 (y 0) (x 2)]
  ring

/-- `O₀` is self-adjoint in `L²(m)` (`lem:old-f-law`(f)). -/
theorem oForm_symm (m u v : (Fin 3 → F) → ℝ) : oForm m u v = oForm m v u := by
  unfold oForm
  rw [uip_comm (Ba m 0 u), uip_comm (Wa m u)]
  ring

/-- `L^m_t` is skew in `L²(m)` (`prop:signed-bounds`(c): the signed leading difference). -/
theorem lForm_skew (m : (Fin 3 → F) → ℝ) (t : ℝ) (u v : (Fin 3 → F) → ℝ) :
    lForm m t u v = -lForm m t v u := by
  unfold lForm
  simp only [uip_comm (Ba m _ u), uip_comm (Wa m u)]
  ring

end Sarkozy.PrimeGram
