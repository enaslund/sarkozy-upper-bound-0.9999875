module

public import Sarkozy.PrimeGram.Kernel
public import Sarkozy.PrimeGram.OldLaw
public import Sarkozy.SignedDecomp.CompForm

@[expose] public section

/-!
# The natural operator of the signed star and the kernel of the signed record (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 2, and the proof of
`lem:old-f-law`(e),(f) ("Transport", the natural operators of the star channels).

Channels on pairs of halves (`eq:middle:channels`): `𝖠 = χ(y₂ - x₀)`, `𝖡 = χ(x₂ - y₀)` (PG's
`chA`, `chB`), `𝖢 = χ(y₀ - x₁)`, `𝖣 = χ(y₁ - x₀)`.

* **`lForm_eq_kernel`**: for weights `m` vanishing on `{x₁ = x₂}`, the form of
  `L^m_t = A_{a_t}V₀^{*m} - V₀A_{a_t}^{*m}` (unprojected `A₃`) is the kernel form
  `∑ m(x) m(y) u(x) v(y) K_L(x, y)`; the constants `-q` of the pair features cancel
  ("its constants cancel").
* **`star_eq_kernel`**: with PG's `oForm_eq_kernel`, at `p ≡ 3 (mod 4)`,
  `⟨u, (O₀ + L^m_t) v⟩_m = ∑ m m u v K_⋆`, where
  `K_⋆ = 𝖢 + (1 - t)𝖡 + (1 - t)𝖡𝖢 + 𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣` is the star part of
  `Ψ^soft_t` (`lem:mirror`(d): the star part `-𝐞` of `(1 + 𝖠)(1 + 𝖡)` plus `L_{t,p}`).
* **`signedV_split`**: the signed combination of the three unnormalized component kernels
  `V_{uv} = 2·1[χ(y₀ - x₁) = 1](1 + (1 - t)𝖡)(1 + u𝖣)(1 + v𝖠)` (SD2's `Vk`) with
  `c = (1, t/2, -t/2)` is `∑ c_{uv} V_{uv} = 1 + K_⋆ + K_ns - K_rq`, where
  `K_ns = (𝖢 + (1 - t)𝖡 + (1 - t)𝖡𝖢)(𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣)` are the nine nonstar
  monomials and `K_rq = 1[y₀ = x₁](1 + (1 - t)𝖡)[1 + 𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣]` is the removed
  query `δ₁₀ G_t`.
-/

open Finset

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.TraceMixing Sarkozy.MiddleRecords Sarkozy.SignedEstimates
open Sarkozy.SignedComponents Sarkozy.SignedDecomp Sarkozy.Envelopes
open Sarkozy.MiddleComparison (signedCoef)

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-! ## The adjoints of the arms as kernels -/

omit [DecidableEq F] in
theorem cen_add_const (h : F → ℝ) (c : ℝ) : cen (fun s => h s + c) = cen h := by
  funext a
  unfold cen
  have hq : qF ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- `A₂^{*m} v = s ↦ ∑_y m(y) χ(s - y₁) v(y)` (already mean zero). -/
theorem Ba1_eq (hR : ringChar F ≠ 2) (m v : (Fin 3 → F) → ℝ) :
    Ba m 1 v = fun s => ∑ y, m y * (χ (s - y 1) : ℝ) * v y := by
  have e : (fun s => qF * mip m (arm 1 (delta s)) v) =
      fun s => ∑ y, m y * (χ (s - y 1) : ℝ) * v y := by
    funext s
    have harm : arm (F := F) 1 = A2 := rfl
    simp only [harm, A2, mip, paleyOp, delta, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      ↓reduceIte, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    field_simp
  have hs : ∑ s, (∑ y, m y * (χ (s - y 1) : ℝ) * v y) = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun y _ => ?_
    have := sumR_chi hR (y 1)
    rw [← sum_mul, ← mul_sum, this, mul_zero, zero_mul]
  unfold Ba adj
  rw [e]
  funext s
  unfold cen
  rw [hs, mul_zero, sub_zero]

/-- The uncentred pair profile `Φ_v(s) = -∑_y m(y) χ(s - y₁) χ(s - y₂) v(y)`. -/
noncomputable def phi2 (m v : (Fin 3 → F) → ℝ) (s : F) : ℝ :=
  -∑ y, m y * ((χ (s - y 1) : ℝ) * χ (s - y 2)) * v y

/-- `A₃^{*m} v = Π₀ Φ_v` (unprojected `A₃`; the constant `-q` of `A₃` is removed by `Π₀`). -/
theorem Ba2_eq (m v : (Fin 3 → F) → ℝ) : Ba m 2 v = cen (phi2 m v) := by
  have hq : qF ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e : (fun s => qF * mip m (arm 2 (delta s)) v) =
      fun s => phi2 m v s + (-(qF⁻¹ * ∑ y, m y * v y)) := by
    funext s
    have harm : arm (F := F) 2 = A3 := rfl
    simp only [harm, A3, A3op, mip, delta, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      ↓reduceIte, phi2]
    rw [mul_sum, mul_sum, ← sum_neg_distrib, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    field_simp
    ring
  unfold Ba adj
  rw [e, cen_add_const]

/-- `∑_s Φ_v(s) = ∑_x m(x) v(x)` when `m` vanishes on `{x₁ = x₂}`
(`∑_s χ(s - a) χ(s - b) = -1` for `a ≠ b`). -/
theorem sum_phi2 (hR : ringChar F ≠ 2) {m : (Fin 3 → F) → ℝ} (hm12 : ∀ x, x 1 = x 2 → m x = 0)
    (v : (Fin 3 → F) → ℝ) : ∑ s, phi2 m v s = ∑ x, m x * v x := by
  have h : ∀ x, m x * v x * ∑ s, (χ (s - x 1) : ℝ) * χ (s - x 2) = -(m x * v x) := by
    intro x
    by_cases hx : x 1 = x 2
    · rw [hm12 x hx]; ring
    · rw [sumR_chi_mul_ne hR hx]; ring
  unfold phi2
  rw [sum_neg_distrib, sum_comm]
  have e : ∑ y, ∑ s, m y * ((χ (s - y 1) : ℝ) * χ (s - y 2)) * v y =
      ∑ y, m y * v y * ∑ s, (χ (s - y 1) : ℝ) * χ (s - y 2) := by
    refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun s _ => by ring
  rw [e]
  simp only [h, sum_neg_distrib, neg_neg]

/-! ## The six star forms -/

theorem uip_B0_W (hR : ringChar F ≠ 2) (m u v : (Fin 3 → F) → ℝ) :
    uip (Ba m 0 u) (Wa m v) = ∑ x, ∑ y, m x * m y * u x * v y * (χ (y 0 - x 2) : ℝ) := by
  rw [Wa_eq m v, uip_cen (sum_Ba m 0 u), uip_qF_right, sum_coord', Ba0_eq hR, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

theorem uip_W_B0 (hR : ringChar F ≠ 2) (m u v : (Fin 3 → F) → ℝ) :
    uip (Wa m u) (Ba m 0 v) = ∑ x, ∑ y, m x * m y * u x * v y * (χ (x 0 - y 2) : ℝ) := by
  rw [Wa_eq m u, uip_cen_left (sum_Ba m 0 v), uip_comm, uip_qF_right, sum_coord', Ba0_eq hR]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

theorem uip_B1_W (hR : ringChar F ≠ 2) (m u v : (Fin 3 → F) → ℝ) :
    uip (Ba m 1 u) (Wa m v) = ∑ x, ∑ y, m x * m y * u x * v y * (χ (y 0 - x 1) : ℝ) := by
  rw [Wa_eq m v, uip_cen (sum_Ba m 1 u), uip_qF_right, sum_coord', Ba1_eq hR, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

theorem uip_W_B1 (hR : ringChar F ≠ 2) (m u v : (Fin 3 → F) → ℝ) :
    uip (Wa m u) (Ba m 1 v) = ∑ x, ∑ y, m x * m y * u x * v y * (χ (x 0 - y 1) : ℝ) := by
  rw [Wa_eq m u, uip_cen_left (sum_Ba m 1 v), uip_comm, uip_qF_right, sum_coord', Ba1_eq hR]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun y _ => by ring

theorem uip_B2_W (hR : ringChar F ≠ 2) {m : (Fin 3 → F) → ℝ} (hm12 : ∀ x, x 1 = x 2 → m x = 0)
    (u v : (Fin 3 → F) → ℝ) :
    uip (Ba m 2 u) (Wa m v) = ∑ x, ∑ y, m x * m y * u x * v y *
      (-((χ (y 0 - x 1) : ℝ) * χ (y 0 - x 2)) - qF⁻¹) := by
  rw [Wa_eq m v, uip_cen (sum_Ba m 2 u), uip_qF_right, sum_coord', Ba2_eq]
  simp only [cen]
  rw [sum_phi2 hR hm12, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  unfold phi2
  rw [← sum_neg_distrib, mul_sum, ← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun x _ => by ring

theorem uip_W_B2 (hR : ringChar F ≠ 2) {m : (Fin 3 → F) → ℝ} (hm12 : ∀ x, x 1 = x 2 → m x = 0)
    (u v : (Fin 3 → F) → ℝ) :
    uip (Wa m u) (Ba m 2 v) = ∑ x, ∑ y, m x * m y * u x * v y *
      (-((χ (x 0 - y 1) : ℝ) * χ (x 0 - y 2)) - qF⁻¹) := by
  rw [Wa_eq m u, uip_cen_left (sum_Ba m 2 v), uip_comm, uip_qF_right, sum_coord', Ba2_eq]
  simp only [cen]
  rw [sum_phi2 hR hm12]
  refine sum_congr rfl fun x _ => ?_
  unfold phi2
  rw [← sum_neg_distrib, mul_sum, ← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun y _ => by ring

/-! ## `L^m_t` and `O₀ + L^m_t` as kernels -/

/-- The kernel of `L^m_t`: `t χ(y₀ - x₂) + χ(y₀ - x₁) - (1 - t) χ(y₀ - x₁) χ(y₀ - x₂)` minus the
same with `x` and `y` exchanged. -/
noncomputable def KL (t : ℝ) (x y : Fin 3 → F) : ℝ :=
  (t * (χ (y 0 - x 2) : ℝ) + (χ (y 0 - x 1) : ℝ) -
      (1 - t) * ((χ (y 0 - x 1) : ℝ) * χ (y 0 - x 2))) -
    (t * (χ (x 0 - y 2) : ℝ) + (χ (x 0 - y 1) : ℝ) -
      (1 - t) * ((χ (x 0 - y 1) : ℝ) * χ (x 0 - y 2)))

/-- **`⟨u, L^m_t v⟩_m = ∑ m(x) m(y) u(x) v(y) K_L(x, y)`** (`prop:signed-bounds`(c), the natural
operator of `L_{t,p}`), for weights vanishing on `{x₁ = x₂}` (e.g. `m₀`, supported on `H_F`). -/
theorem lForm_eq_kernel (hR : ringChar F ≠ 2) {m : (Fin 3 → F) → ℝ}
    (hm12 : ∀ x, x 1 = x 2 → m x = 0) (t : ℝ) (u v : (Fin 3 → F) → ℝ) :
    lForm m t u v = ∑ x, ∑ y, m x * m y * u x * v y * KL t x y := by
  unfold lForm
  simp only [Fin.sum_univ_three, aT, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [uip_B0_W hR, uip_B1_W hR, uip_B2_W hR hm12, uip_W_B0 hR, uip_W_B1 hR, uip_W_B2 hR hm12]
  simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  unfold KL
  ring

/-- The channel `𝖢 = χ(y₀ - x₁)`. -/
noncomputable def chC (x y : Fin 3 → F) : ℝ := (χ (y 0 - x 1) : ℝ)

/-- The channel `𝖣 = χ(y₁ - x₀)`. -/
noncomputable def chD (x y : Fin 3 → F) : ℝ := (χ (y 1 - x 0) : ℝ)

/-- **The star kernel** `K_⋆ = 𝖢 + (1 - t)𝖡 + (1 - t)𝖡𝖢 + 𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣`. -/
noncomputable def Kstar (t : ℝ) (x y : Fin 3 → F) : ℝ :=
  chC x y + (1 - t) * PrimeGram.chB x y + (1 - t) * (PrimeGram.chB x y * chC x y) + chD x y +
    (1 + t) * PrimeGram.chA x y +
    (1 - t) * (PrimeGram.chA x y * chD x y)

/-- **`⟨u, (O₀ + L^m_t) v⟩_m = ∑ m m u v K_⋆`** (`prop:signed-bounds`(c), Step 2: the star part of
`Ψ^soft_t` has the natural operator `O₀ + L^m_{t,p}`), for weights vanishing on `{x₁ = x₂}`,
at `p ≡ 3 (mod 4)`. -/
theorem star_eq_kernel (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    {m : (Fin 3 → F) → ℝ} (hm12 : ∀ x, x 1 = x 2 → m x = 0) (t : ℝ) (u v : (Fin 3 → F) → ℝ) :
    oForm m u v + lForm m t u v = ∑ x, ∑ y, m x * m y * u x * v y * Kstar t x y := by
  rw [oForm_eq_kernel hR h3, lForm_eq_kernel hR hm12, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  unfold KL Kstar PrimeGram.chA PrimeGram.chB chC chD
  rw [chiR_swap h3 (y 0) (x 2), chiR_swap h3 (x 0) (y 2), chiR_swap h3 (x 0) (y 1)]
  ring

/-! ## The signed record kernel -/

/-- **The signed combination of the component kernels**
`∑_c α_c V_{u_c v_c}`, `α = (1, t/2, -t/2)`, `(u, v) = (1, 1), (-1, 1), (-1, -1)`. -/
noncomputable def signedV (t : ℝ) (x y : Fin 3 → F) : ℝ :=
  ∑ c, signedCoef t c * Vk t (compU c : ℝ) (compV c : ℝ) x y

/-- **The nine nonstar monomials** `K_ns = (𝖢 + (1 - t)𝖡 + (1 - t)𝖡𝖢)(𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣)`
(`prop:signed-bounds`(c), Step 2: the nonstars of `Ψ^soft_t`). -/
noncomputable def Knon (t : ℝ) (x y : Fin 3 → F) : ℝ :=
  (chC x y + (1 - t) * PrimeGram.chB x y + (1 - t) * (PrimeGram.chB x y * chC x y)) *
    (chD x y + (1 + t) * PrimeGram.chA x y + (1 - t) * (PrimeGram.chA x y * chD x y))

/-- **The removed query** `K_rq = 1[y₀ = x₁] G_t`,
`G_t = (1 + (1 - t)𝖡)[1 + 𝖣 + (1 + t)𝖠 + (1 - t)𝖠𝖣]` (`prop:signed-bounds`(c), Step 2). -/
noncomputable def Krq (t : ℝ) (x y : Fin 3 → F) : ℝ :=
  (if y 0 - x 1 = 0 then 1 else 0) * ((1 + (1 - t) * PrimeGram.chB x y) *
    (1 + chD x y + (1 + t) * PrimeGram.chA x y + (1 - t) * (PrimeGram.chA x y * chD x y)))

/-- **`∑_c α_c V_c = 1 + K_⋆ + K_ns - K_rq`** (`prop:signed-bounds`(c), Step 2:
`∑ c_{uv} U_{uv} = Ψ^soft_t - δ₁₀ G_t`, with `2·1[χ(c) = 1] = 1 + χ(c) - 1[c = 0]`). -/
theorem signedV_split (t : ℝ) (x y : Fin 3 → F) :
    signedV t x y = 1 + Kstar t x y + Knon t x y - Krq t x y := by
  unfold signedV
  simp only [Fin.sum_univ_three, signedCoef, compU, compV, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Vk]
  rw [two_ind]
  unfold Kstar Knon Krq PrimeGram.chA PrimeGram.chB chC chD
  push_cast
  ring

end Sarkozy.SignedDecompCrude
