module

public import Sarkozy.MiddleRecords.ActualFeaturesNorms
public import Sarkozy.MiddleRecords.ActualFeaturesOps

@[expose] public section

/-!
# The projection of `A₃` on the singleton features (`lem:actual-features`(c), last claim)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(c):
`‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ J_F q r` as an operator from `H₀` to `L²(m₀)`, with
`J_F = (2/(1 - ϱ₀₁))^{1/2} (r/(1 - q) + 2q/((1 - q)(1 - 4q)))`. This was the one claim of (c)
not yet formalized (`MiddleRecords.ActualFeaturesA3`, "Not formalized").

`A₃ h` and the elements `G = u(x₁) + v(x₂)` of `𝓗₁ + 𝓗₂` are functions of `(x₁, x₂)`, so their
`L²(m₀)` inner product is that of the pair law `m₁₂` (`ip12`). The norm of the projection is
the largest `⟨A₃ h, G⟩` over unit `G` in `𝓗₁ + 𝓗₂`, so the claim is the inequality
`⟨A₃ h, G⟩² ≤ (J_F q r)² ‖h‖² ‖G‖²` for all such `G`. Proved here:

* `ip12_A3_left`, `ip12_A3_right`: `⟨A₃ h, u(x₁)⟩ = E_a u(a) w₁(a)` and
  `⟨A₃ h, v(x₂)⟩ = E_b v(b) w₂(b)`, with `w_i = V^*_{i,m} A₃ h` from W6's `V1m_A3`, `V2m_A3`;
* `sum_w1_sq`, `sum_w2_sq`: `‖V^*_{i,m} A₃ h‖ = q ϱ₀₁ ‖h‖` **exactly**:
  `∑ w_i² = (1 + μ²p)/(p(p - 1))² ∑ h²`, using `⟨h, P h⟩ = 0` and `‖P h‖² = q ‖h‖²`. The paper
  bounds it by the triangle inequality, `q/(p - 1) + μr/(p - 1)`, which is at least this;
* `ip12_gram_ge`: on `𝓗₁ + 𝓗₂`, `‖u(x₁) + v(x₂)‖² ≥ (1 - ϱ)(‖u‖² + ‖v‖²)` for every
  `ϱ ≥ ϱ₀₁` (from `‖V^*_{1,m} V₂ v‖ = ϱ₀₁ ‖v‖`, W6's `norm_V1m_V2`);
* **`A3_proj12_sharp`**: `⟨A₃ h, G⟩² ≤ 2 q² ϱ₀₁²/(1 - ϱ) ‖h‖² ‖G‖²`, i.e.
  `‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ (2/(1 - ϱ))^{1/2} q ϱ₀₁`;
* **`A3_proj12`**: the paper's form, `⟨A₃ h, G⟩² ≤ (J_F q r)² ‖h‖² ‖G‖²`, with `J_F q r` written
  as `(2/(1 - ϱ))^{1/2} (1 + μ√p)/(p(p - 1))` (`jFqr`) and `jFqr_eq` its identification with the
  paper's `J_F q r` at `q = 1/p`, `r = p^{-1/2}`.

Hypotheses as in W6: a finite field `F`, `p = |F| ≡ 3 (mod 4)`, `p ≥ 7`; `h`, `v` of mean zero
(`u` need not be). Norms on `H₀` are those of the uniform law (`unifNormSq`).
-/

open Finset

namespace Sarkozy.OpsCore

open Sarkozy.MiddleRecords Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- The inner product of `L²(m₀)` on functions of `(x₁, x₂)`, through the pair law `m₁₂`. -/
noncomputable def ip12 (f g : F → F → ℝ) : ℝ := ∑ a, ∑ b, m12 a b * f a b * g a b

/-- `V^*_{1,m} A₃ h` (W6's `V1m_A3`). -/
noncomputable def w1 (h : F → ℝ) (a : F) : ℝ :=
  (-h a + muF (F := F) * qF * paleyOp h a) / (qF * (qF - 1))

/-- `V^*_{2,m} A₃ h` (W6's `V2m_A3`). -/
noncomputable def w2 (h : F → ℝ) (b : F) : ℝ :=
  (-h b - muF (F := F) * qF * paleyOp h b) / (qF * (qF - 1))

/-- `ϱ₀₁²` in W6's form, `(1 + μ²p)/(p - 1)²`. -/
noncomputable def rho01Sq : ℝ := (1 + muF (F := F) ^ 2 * qF) / (qF - 1) ^ 2

theorem ip12_A3_left (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h u : F → ℝ) (hh : ∑ s, h s = 0) :
    ip12 (A3op h) (fun a _ => u a) = qF⁻¹ * ∑ a, u a * w1 h a := by
  have h0 : qF ≠ 0 := by intro h; linarith
  unfold ip12
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have hv := V1m_A3 hF h3 h7 h hh a
  have e : ∑ b, m12 a b * A3op h a b * u a = u a * ∑ b, m12 a b * A3op h a b := by
    rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
  rw [e, w1, ← hv]
  field_simp

theorem ip12_A3_right (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h v : F → ℝ) (hh : ∑ s, h s = 0) :
    ip12 (A3op h) (fun _ b => v b) = qF⁻¹ * ∑ b, v b * w2 h b := by
  have h0 : qF ≠ 0 := by intro h; linarith
  unfold ip12
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  have hv := V2m_A3 hF h3 h7 h hh b
  have e : ∑ a, m12 a b * A3op h a b * v b = v b * ∑ a, m12 a b * A3op h a b := by
    rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
  rw [e, w2, ← hv]
  field_simp

/-- `∑_s (c₁ h(s) + c₂ (P h)(s))² = (c₁² + c₂²/p) ∑ h²` on `H₀`. -/
theorem sum_comb_paley_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (c₁ c₂ : ℝ) :
    ∑ s, (c₁ * h s + c₂ * paleyOp h s) ^ 2 = (c₁ ^ 2 + c₂ ^ 2 * qF⁻¹) * ∑ s, h s ^ 2 := by
  have e : ∀ s, (c₁ * h s + c₂ * paleyOp h s) ^ 2 =
      c₁ ^ 2 * h s ^ 2 + 2 * c₁ * c₂ * (h s * paleyOp h s) + c₂ ^ 2 * paleyOp h s ^ 2 :=
    fun s => by ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_paleyOp_sq hF h hh, sum_mul_paleyOp_self h3 h]
  ring

/-- **`‖V^*_{1,m} A₃ h‖² = q² ϱ₀₁² ‖h‖²`** (exactly): `∑ w₁² = ϱ₀₁²/p² ∑ h²`. -/
theorem sum_w1_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h : F → ℝ) (hh : ∑ s, h s = 0) :
    ∑ a, w1 h a ^ 2 = qF⁻¹ ^ 2 * rho01Sq (F := F) * ∑ s, h s ^ 2 := by
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have e : ∀ a, w1 h a = (-(1 / (qF * (qF - 1)))) * h a +
      (muF (F := F) * qF / (qF * (qF - 1))) * paleyOp h a := fun a => by
    unfold w1; field_simp
  simp only [e, sum_comb_paley_sq hF h3 h hh]
  unfold rho01Sq
  field_simp

/-- **`‖V^*_{2,m} A₃ h‖² = q² ϱ₀₁² ‖h‖²`** (exactly). -/
theorem sum_w2_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h : F → ℝ) (hh : ∑ s, h s = 0) :
    ∑ a, w2 h a ^ 2 = qF⁻¹ ^ 2 * rho01Sq (F := F) * ∑ s, h s ^ 2 := by
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have e : ∀ a, w2 h a = (-(1 / (qF * (qF - 1)))) * h a +
      (-(muF (F := F) * qF / (qF * (qF - 1)))) * paleyOp h a := fun a => by
    unfold w2; field_simp; ring
  simp only [e, sum_comb_paley_sq hF h3 h hh]
  unfold rho01Sq
  field_simp

/-- The Gram of `u(x₁) + v(x₂)`: `‖u‖² + ‖v‖² + 2 E_a u(a) (V^*_{1,m} V₂ v)(a)`. -/
theorem ip12_gram (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (u v : F → ℝ) :
    ip12 (fun a b => u a + v b) (fun a b => u a + v b) =
      qF⁻¹ * ∑ a, u a ^ 2 + qF⁻¹ * ∑ b, v b ^ 2 +
        2 * (qF⁻¹ * ∑ a, u a * condOp m12 v a) := by
  have h0 : qF ≠ 0 := by intro h; linarith
  unfold ip12 condOp
  have e : ∀ a b, m12 a b * (u a + v b) * (u a + v b) =
      u a ^ 2 * m12 a b + v b ^ 2 * m12 a b + 2 * u a * (m12 a b * v b) := fun a b => by ring
  simp only [e, sum_add_distrib]
  have hA : ∑ a, ∑ b, u a ^ 2 * m12 a b = qF⁻¹ * ∑ a, u a ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [← mul_sum, sum_m12_right hF h3 h7 a]; ring
  have hB : ∑ a, ∑ b, v b ^ 2 * m12 a b = qF⁻¹ * ∑ b, v b ^ 2 := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [← mul_sum, sum_m12_left hF h3 h7 b]; ring
  have hC : ∑ a, ∑ b, 2 * u a * (m12 a b * v b) =
      2 * (qF⁻¹ * ∑ a, u a * (qF * ∑ b, m12 a b * v b)) := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [← mul_sum]; field_simp
  rw [hA, hB, hC]

/-- **The Gram of `𝓗₁ + 𝓗₂` is at least `1 - ϱ`** for every `ϱ ≥ ϱ₀₁` (`v` of mean zero). -/
theorem ip12_gram_ge (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (u v : F → ℝ) (hv : ∑ b, v b = 0) {ϱ : ℝ} (hϱ0 : 0 ≤ ϱ) (hϱ : rho01Sq (F := F) ≤ ϱ ^ 2) :
    (1 - ϱ) * (qF⁻¹ * ∑ a, u a ^ 2 + qF⁻¹ * ∑ b, v b ^ 2) ≤
      ip12 (fun a b => u a + v b) (fun a b => u a + v b) := by
  rw [ip12_gram hF h3 h7]
  have hq : 0 < qF⁻¹ := by
    have : 0 < qF := by linarith
    positivity
  set U := ∑ a, u a ^ 2
  set V := ∑ b, v b ^ 2
  set Y := ∑ a, u a * condOp m12 v a
  have hU : 0 ≤ U := sum_nonneg fun _ _ => sq_nonneg _
  have hV : 0 ≤ V := sum_nonneg fun _ _ => sq_nonneg _
  have hcs : Y ^ 2 ≤ U * ∑ a, condOp m12 v a ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
  rw [norm_V1m_V2 hF h3 h7 v hv] at hcs
  have hY : Y ^ 2 ≤ (ϱ * ((U + V) / 2)) ^ 2 := by
    have h1 : U * ((1 + muF (F := F) ^ 2 * qF) / (qF - 1) ^ 2 * V) ≤ U * (ϱ ^ 2 * V) := by
      refine mul_le_mul_of_nonneg_left ?_ hU
      exact mul_le_mul_of_nonneg_right hϱ hV
    have h2 : U * (ϱ ^ 2 * V) ≤ (ϱ * ((U + V) / 2)) ^ 2 := by
      have : U * V ≤ ((U + V) / 2) ^ 2 := by nlinarith [sq_nonneg (U - V)]
      calc U * (ϱ ^ 2 * V) = ϱ ^ 2 * (U * V) := by ring
        _ ≤ ϱ ^ 2 * ((U + V) / 2) ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = (ϱ * ((U + V) / 2)) ^ 2 := by ring
    exact hcs.trans (h1.trans h2)
  have hB : 0 ≤ ϱ * ((U + V) / 2) := by positivity
  have hYge : -(ϱ * ((U + V) / 2)) ≤ Y := by nlinarith [sq_nonneg (Y + ϱ * ((U + V) / 2))]
  nlinarith [mul_le_mul_of_nonneg_left hYge hq.le]

/-- **`‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ (2/(1 - ϱ))^{1/2} q ϱ₀₁`** (sharp form): for `h ∈ H₀` and
`G = u(x₁) + v(x₂)` with `v` of mean zero, and every `ϱ ∈ [ϱ₀₁, 1)`,
`⟨A₃ h, G⟩² ≤ 2 q² ϱ₀₁²/(1 - ϱ) ‖h‖² ‖G‖²`. -/
theorem A3_proj12_sharp (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h u v : F → ℝ) (hh : ∑ s, h s = 0) (hv : ∑ b, v b = 0) {ϱ : ℝ} (hϱ0 : 0 ≤ ϱ)
    (hϱ1 : ϱ < 1) (hϱ : rho01Sq (F := F) ≤ ϱ ^ 2) :
    ip12 (A3op h) (fun a b => u a + v b) ^ 2 ≤
      2 * (qF⁻¹ ^ 2 * rho01Sq (F := F)) / (1 - ϱ) * unifNormSq h *
        ip12 (fun a b => u a + v b) (fun a b => u a + v b) := by
  have hsplit : ip12 (A3op h) (fun a b => u a + v b) =
      ip12 (A3op h) (fun a _ => u a) + ip12 (A3op h) (fun _ b => v b) := by
    unfold ip12
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun b _ => by ring
  rw [hsplit, ip12_A3_left hF h3 h7 h u hh, ip12_A3_right hF h3 h7 h v hh]
  have hq : 0 < qF⁻¹ := by
    have : 0 < qF := by linarith
    positivity
  set κ := rho01Sq (F := F)
  have hκ : 0 ≤ κ := by unfold κ rho01Sq; positivity
  set H := ∑ s, h s ^ 2
  set U := ∑ a, u a ^ 2
  set V := ∑ b, v b ^ 2
  have hH : 0 ≤ H := sum_nonneg fun _ _ => sq_nonneg _
  have hU : 0 ≤ U := sum_nonneg fun _ _ => sq_nonneg _
  have hV : 0 ≤ V := sum_nonneg fun _ _ => sq_nonneg _
  set X1 := ∑ a, u a * w1 h a
  set X2 := ∑ b, v b * w2 h b
  have h1 : X1 ^ 2 ≤ U * (qF⁻¹ ^ 2 * κ * H) := by
    have := sum_mul_sq_le_sq_mul_sq univ u (w1 h)
    rwa [sum_w1_sq hF h3 h7 h hh] at this
  have h2 : X2 ^ 2 ≤ V * (qF⁻¹ ^ 2 * κ * H) := by
    have := sum_mul_sq_le_sq_mul_sq univ v (w2 h)
    rwa [sum_w2_sq hF h3 h7 h hh] at this
  have hG := ip12_gram_ge hF h3 h7 u v hv hϱ0 hϱ
  have hpos : 0 < 1 - ϱ := by linarith
  have hlhs : (qF⁻¹ * X1 + qF⁻¹ * X2) ^ 2 ≤
      2 * qF⁻¹ ^ 2 * (U + V) * (qF⁻¹ ^ 2 * κ * H) := by
    have : (X1 + X2) ^ 2 ≤ 2 * (X1 ^ 2 + X2 ^ 2) := by nlinarith [sq_nonneg (X1 - X2)]
    calc (qF⁻¹ * X1 + qF⁻¹ * X2) ^ 2 = qF⁻¹ ^ 2 * (X1 + X2) ^ 2 := by ring
      _ ≤ qF⁻¹ ^ 2 * (2 * (U * (qF⁻¹ ^ 2 * κ * H) + V * (qF⁻¹ ^ 2 * κ * H))) := by
        refine mul_le_mul_of_nonneg_left (this.trans ?_) (sq_nonneg _)
        linarith
      _ = 2 * qF⁻¹ ^ 2 * (U + V) * (qF⁻¹ ^ 2 * κ * H) := by ring
  have hUN : unifNormSq h = qF⁻¹ * H := rfl
  have hc : 0 ≤ 2 * (qF⁻¹ ^ 2 * κ) / (1 - ϱ) * unifNormSq h := by
    rw [hUN]; positivity
  calc (qF⁻¹ * X1 + qF⁻¹ * X2) ^ 2 ≤ 2 * qF⁻¹ ^ 2 * (U + V) * (qF⁻¹ ^ 2 * κ * H) := hlhs
    _ = 2 * (qF⁻¹ ^ 2 * κ) / (1 - ϱ) * unifNormSq h *
          ((1 - ϱ) * (qF⁻¹ * U + qF⁻¹ * V)) := by
        rw [hUN]; field_simp
    _ ≤ 2 * (qF⁻¹ ^ 2 * κ) / (1 - ϱ) * unifNormSq h *
          ip12 (fun a b => u a + v b) (fun a b => u a + v b) :=
        mul_le_mul_of_nonneg_left hG hc

/-- **The paper's constant** `J_F q r = (2/(1 - ϱ))^{1/2} (1 + μ√p)/(p(p - 1))`. -/
noncomputable def jFqr (ϱ : ℝ) : ℝ :=
  Real.sqrt (2 / (1 - ϱ)) * ((1 + muF (F := F) * Real.sqrt qF) / (qF * (qF - 1)))

omit [DecidableEq F] in
/-- `jFqr` is the paper's `J_F q r` at `q = 1/p`, `r = p^{-1/2}`:
`J_F = (2/(1 - ϱ))^{1/2} (r/(1 - q) + 2q/((1 - q)(1 - 4q)))`. -/
theorem jFqr_eq (h7 : 7 ≤ qF) (ϱ : ℝ) :
    jFqr (F := F) ϱ = Real.sqrt (2 / (1 - ϱ)) *
      (Real.sqrt (1 / qF) / (1 - 1 / qF) + 2 * (1 / qF) / ((1 - 1 / qF) * (1 - 4 * (1 / qF)))) *
        (1 / qF) * Real.sqrt (1 / qF) := by
  have h0 : 0 < qF := by linarith
  have hs : 0 < Real.sqrt qF := Real.sqrt_pos.mpr h0
  have hss : Real.sqrt qF ^ 2 = qF := Real.sq_sqrt h0.le
  have hr : Real.sqrt (1 / qF) = 1 / Real.sqrt qF := by
    rw [Real.sqrt_div' 1 h0.le, Real.sqrt_one]
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h4 : qF - 4 ≠ 0 := by intro h; linarith
  unfold jFqr muF
  rw [hr]
  have e1 : 1 - 1 / qF = (qF - 1) / qF := by field_simp
  have e4 : 1 - 4 * (1 / qF) = (qF - 4) / qF := by field_simp
  rw [e1, e4]
  field_simp
  rw [hss]

/-- **`lem:actual-features`(c), `‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ J_F q r`**, in the form
`⟨A₃ h, G⟩² ≤ (J_F q r)² ‖h‖² ‖G‖²` for `h ∈ H₀`, `G = u(x₁) + v(x₂)` (`v` of mean zero) and
every `ϱ ∈ [ϱ₀₁, 1)`. -/
theorem A3_proj12 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h u v : F → ℝ) (hh : ∑ s, h s = 0) (hv : ∑ b, v b = 0) {ϱ : ℝ} (hϱ0 : 0 ≤ ϱ)
    (hϱ1 : ϱ < 1) (hϱ : rho01Sq (F := F) ≤ ϱ ^ 2) :
    ip12 (A3op h) (fun a b => u a + v b) ^ 2 ≤
      jFqr (F := F) ϱ ^ 2 * unifNormSq h *
        ip12 (fun a b => u a + v b) (fun a b => u a + v b) := by
  refine (A3_proj12_sharp hF h3 h7 h u v hh hv hϱ0 hϱ1 hϱ).trans ?_
  have h0 : 0 < qF := by linarith
  have hpos : 0 < 1 - ϱ := by linarith
  have hμ : 0 ≤ muF (F := F) := by unfold muF; apply div_nonneg (by norm_num); linarith
  have hs : 0 ≤ Real.sqrt qF := Real.sqrt_nonneg _
  have hss : Real.sqrt qF ^ 2 = qF := Real.sq_sqrt h0.le
  have hG : 0 ≤ ip12 (fun a b => u a + v b) (fun a b => u a + v b) := by
    unfold ip12
    refine sum_nonneg fun a _ => sum_nonneg fun b _ => ?_
    have : 0 ≤ m12 a b := by
      unfold m12
      exact div_nonneg (sum_nonneg fun _ _ => oldW_nonneg h7 _ _ _)
        (oldZ_pos hF h3 h7).le
    nlinarith [sq_nonneg (u a + v b)]
  have hU : 0 ≤ unifNormSq h := by unfold unifNormSq; positivity
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hU) hG
  have hJ : jFqr (F := F) ϱ ^ 2 =
      2 / (1 - ϱ) * ((1 + muF (F := F) * Real.sqrt qF) / (qF * (qF - 1))) ^ 2 := by
    unfold jFqr
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hJ]
  have h1 : 0 < qF - 1 := by linarith
  have key : qF⁻¹ ^ 2 * rho01Sq (F := F) ≤
      ((1 + muF (F := F) * Real.sqrt qF) / (qF * (qF - 1))) ^ 2 := by
    unfold rho01Sq
    rw [div_pow, show qF⁻¹ ^ 2 * ((1 + muF (F := F) ^ 2 * qF) / (qF - 1) ^ 2) =
      (1 + muF (F := F) ^ 2 * qF) / (qF * (qF - 1)) ^ 2 by field_simp]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith [mul_nonneg hμ hs]
  calc 2 * (qF⁻¹ ^ 2 * rho01Sq (F := F)) / (1 - ϱ) =
        2 / (1 - ϱ) * (qF⁻¹ ^ 2 * rho01Sq (F := F)) := by ring
    _ ≤ 2 / (1 - ϱ) * ((1 + muF (F := F) * Real.sqrt qF) / (qF * (qF - 1))) ^ 2 :=
        mul_le_mul_of_nonneg_left key (by positivity)

omit [Field F] [DecidableEq F] in
/-- `ϱ₀₁ < 1` for `p ≥ 7`. -/
theorem rho01Sq_lt_one (h7 : 7 ≤ qF) : rho01Sq (F := F) < 1 := by
  unfold rho01Sq muF
  have h1 : 0 < (qF - 1) ^ 2 := by nlinarith
  have h4 : 0 < qF - 4 := by linarith
  rw [div_lt_one h1, div_pow, div_mul_eq_mul_div]
  have hq : 2 ^ 2 * qF / (qF - 4) ^ 2 < 4 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- **`lem:actual-features`(c) at the paper's `ϱ₀₁`**: `‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ J_F q r` with
`ϱ = ϱ₀₁ = √rho01Sq` exactly, for every `p ≡ 3 (mod 4)`, `p ≥ 7`. -/
theorem A3_proj12_paper (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h u v : F → ℝ) (hh : ∑ s, h s = 0) (hv : ∑ b, v b = 0) :
    ip12 (A3op h) (fun a b => u a + v b) ^ 2 ≤
      jFqr (F := F) (Real.sqrt (rho01Sq (F := F))) ^ 2 * unifNormSq h *
        ip12 (fun a b => u a + v b) (fun a b => u a + v b) := by
  have hκ : 0 ≤ rho01Sq (F := F) := by
    unfold rho01Sq; positivity
  refine A3_proj12 hF h3 h7 h u v hh hv (Real.sqrt_nonneg _) ?_ (Real.sq_sqrt hκ).ge
  rw [Real.sqrt_lt' one_pos, one_pow]
  exact rho01Sq_lt_one h7

end Sarkozy.OpsCore
