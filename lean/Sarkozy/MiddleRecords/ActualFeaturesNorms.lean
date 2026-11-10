module

public import Sarkozy.MiddleRecords.ActualFeaturesA3

/-!
# The norms of the features under `m₀` (`lem:actual-features`(c), the first norm claims)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(c): "as operators from `H₀` to
`L²(m₀)`, `‖A₁‖ = ‖A₂‖ = r`, `‖A₃‖ ≤ r`". With `(A₂ h)(x) = (P h)(x₁)`, `(A₁ h)(x) = (P h)(x₂)`
and the pair law `m₁₂` of `m₀`:

* `norm_A2_sq`, `norm_A1_sq`: `‖A₂ h‖²_{m₀} = ‖A₁ h‖²_{m₀} = q ‖h‖²` on `H₀` (the coordinates
  `x₁`, `x₂` are uniform under `m₀`, and `P^* P = q I` on `H₀`), so `‖A₁‖ = ‖A₂‖ = r` exactly;
* `norm_A3_sq_le`: `‖A₃ h‖²_{m₀} ≤ q ‖h‖²`, from `A₃^{*_m} A₃ = q(1 - 2q - q²)/(1 - q) I`.

Norms on `H₀` are those of the uniform law (`unifNormSq`). Part (d) is
`Sarkozy.MiddleRecords.synthesis_bound`. **Not formalized:** `‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ J_F q r` and
part (e).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- **`‖A₂ h‖²_{m₀} = q ‖h‖²` on `H₀`.** -/
theorem norm_A2_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ a, ∑ b, m12 a b * paleyOp h a ^ 2 = qF⁻¹ * unifNormSq h := by
  have e : ∀ a, ∑ b, m12 a b * paleyOp h a ^ 2 = paleyOp h a ^ 2 * ∑ b, m12 a b := by
    intro a; rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
  simp only [e, sum_m12_right hF h3 h7]
  rw [← sum_mul, sum_paleyOp_sq hF h hh, unifNormSq]
  ring

/-- **`‖A₁ h‖²_{m₀} = q ‖h‖²` on `H₀`.** -/
theorem norm_A1_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ a, ∑ b, m12 a b * paleyOp h b ^ 2 = qF⁻¹ * unifNormSq h := by
  rw [sum_comm]
  have e : ∀ b, ∑ a, m12 a b * paleyOp h b ^ 2 = paleyOp h b ^ 2 * ∑ a, m12 a b := by
    intro b; rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
  simp only [e, sum_m12_left hF h3 h7]
  rw [← sum_mul, sum_paleyOp_sq hF h hh, unifNormSq]
  ring

/-- **`‖A₃ h‖²_{m₀} ≤ q ‖h‖²` on `H₀`.** -/
theorem norm_A3_sq_le (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h : F → ℝ) (hh : ∑ s, h s = 0) :
    ∑ a, ∑ b, m12 a b * A3op h a b ^ 2 ≤ qF⁻¹ * unifNormSq h := by
  rw [A3_gram hF h3 h7 h hh]
  have hu : 0 ≤ unifNormSq h := by unfold unifNormSq; positivity
  have h1 : 0 < qF - 1 := by linarith
  have h0 : 0 < qF := by linarith
  have hc : (1 - 2 * (1 / qF) - (1 / qF) ^ 2) / (qF - 1) ≤ qF⁻¹ := by
    rw [div_le_iff₀ h1, inv_eq_one_div]
    have : 0 < 1 / qF := by positivity
    have hq : 1 / qF * qF = 1 := by field_simp
    nlinarith [sq_nonneg (1 / qF)]
  unfold unifNormSq
  have hS : 0 ≤ qF⁻¹ * ∑ s, h s ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hc hS

end Sarkozy.MiddleRecords
