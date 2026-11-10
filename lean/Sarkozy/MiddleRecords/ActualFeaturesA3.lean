module

public import Sarkozy.MiddleRecords.ActualFeaturesOps
public import Sarkozy.MiddleRecords.RectStar

/-!
# The pair feature `A₃` under the actual half marginal (`lem:actual-features`(c), part)

`paper/sections/21_middle_records.tex`, `lem:actual-features`(c). The feature
`(A₃ h)(x) = -E_s[χ(s - x₂) χ(s - x₁) h(s)] - q E h` (`A3op`, a function of `(x₁, x₂)`) of
`lem:paley-triple`(e), under the actual half marginal `m₀` (pair law `m₁₂` of
`Sarkozy.MiddleRecords.ActualFeatures`). On the mean-zero functions `H₀`, with `q = 1/p` and
`μ = 2/(p - 4)`:

* `V^*_{1,m} A₃ = -q/(p - 1) I + μ/(p - 1) P` (`V1m_A3`) and
  `V^*_{2,m} A₃ = -q/(p - 1) I - μ/(p - 1) P` (`V2m_A3`), where `V^*_{i,m}` is the conditional
  expectation given `x_i` (the coordinates `x₁`, `x₂` are uniform under `m₀`: `sum_m12_right`,
  `sum_m12_left`);
* `A₃^{*_m} A₃ = q(1 - 2q - q²)/(1 - q) I` (`A3_gram`): `‖A₃ h‖²_{m₀} = (1 - 2q - q²)/(p - 1) ‖h‖²`,
  with the uniform norm on `F` (`(1 - 2q - q²)/(p - 1) = q(1 - 2q - q²)/(1 - q)`). As in the
  paper, the density `1 - μ χ(x₂ - x₁)` of `m₁₂` against the uniform law of distinct pairs drops
  out because `A₃ h` is symmetric in `(x₁, x₂)`; the remaining four-character sum is the
  rectangular-star Gram of `Sarkozy.MiddleRecords.RectStar` with coefficients `(0, 0, 1)`.

The fourth identity `A₃^{*_m} V₀ = (p + 4)/(p(p - 1)(p - 4)) I` is
`Sarkozy.MiddleRecords.A3_V0`; part (d) is `Sarkozy.MiddleRecords.synthesis_bound`. **Not
formalized:** `‖Π_{𝓗₁+𝓗₂} A₃‖ ≤ J_F q r` and part (e).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- **The feature `A₃`** of `lem:paley-triple`(e):
`(A₃ h)(x₁, x₂) = -E_s[χ(s - x₁) χ(s - x₂) h(s)] - q E h`. -/
noncomputable def A3op (h : F → ℝ) (a b : F) : ℝ :=
  -(qF⁻¹ * ∑ s, (χ (s - a) : ℝ) * (χ (s - b) : ℝ) * h s) - qF⁻¹ * (qF⁻¹ * ∑ s, h s)

theorem A3op_meanZero (h : F → ℝ) (hh : ∑ s, h s = 0) (a b : F) :
    A3op h a b = -(qF⁻¹ * ∑ s, (χ (s - a) : ℝ) * (χ (s - b) : ℝ) * h s) := by
  rw [A3op, hh, mul_zero, mul_zero, sub_zero]

theorem A3op_symm (h : F → ℝ) (a b : F) : A3op h a b = A3op h b a := by
  unfold A3op
  congr 3
  exact sum_congr rfl fun s _ => by ring

/-- The coordinate `x₁` is uniform under `m₀`: `∑_b m₁₂(a, b) = 1/p`. -/
theorem sum_m12_right (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (a : F) : ∑ b, m12 a b = 1 / qF := by
  have h := sum_pair_mul (1 / (qF * (qF - 1))) (-(muF (F := F)) / (qF * (qF - 1)))
    (1 / (qF * (qF - 1))) (fun _ => 1) a
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  calc ∑ b, m12 a b = ∑ b, (1 / (qF * (qF - 1)) + -(muF (F := F)) / (qF * (qF - 1)) *
        (χ (b - a) : ℝ) - 1 / (qF * (qF - 1)) * (if a = b then 1 else 0)) * 1 :=
        sum_congr rfl fun b _ => by rw [m12_eq' hF h3 h7]; ring
    _ = _ := h
    _ = 1 / qF := by
        rw [paleyOp_const hF 1 a, sum_const, card_univ, nsmul_eq_mul, mul_one]
        field_simp
        ring

/-- The coordinate `x₂` is uniform under `m₀`: `∑_a m₁₂(a, b) = 1/p`. -/
theorem sum_m12_left (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (b : F) : ∑ a, m12 a b = 1 / qF := by
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  have e : ∀ a, m12 a b = 1 / (qF * (qF - 1)) - muF (F := F) / (qF * (qF - 1)) *
      (χ (b - a) : ℝ) - 1 / (qF * (qF - 1)) * (if b = a then 1 else 0) := by
    intro a
    rw [m12_eq' hF h3 h7]
    by_cases hab : a = b
    · subst hab; simp only [↓reduceIte]; ring
    · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab)]; ring
  simp only [e, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one,
    sumR_chi_sub hF b, sum_ite_eq, mem_univ, ↓reduceIte]
  field_simp
  ring

/-- `∑_s χ(s - a)² h(s) = -h(a)` on `H₀`. -/
theorem sum_chi_sq_mul (h : F → ℝ) (hh : ∑ s, h s = 0) (a : F) :
    ∑ s, (χ (s - a) : ℝ) * (χ (s - a) : ℝ) * h s = -h a := by
  have e : ∀ s, (χ (s - a) : ℝ) * (χ (s - a) : ℝ) * h s = h s - (if s = a then h s else 0) := by
    intro s
    by_cases hs : s = a
    · subst hs; simp
    · rw [ite_eq_right hs, sub_zero]
      have := chi_sq_one (u := a) (v := s) (Ne.symm hs)
      rw [← sq, this, one_mul]
  simp only [e, sum_sub_distrib, hh, sum_ite_eq', mem_univ, ↓reduceIte, zero_sub]

/-- `∑_b m₁₂(a, b) χ(s - b) = (μ(p [a = s] - 1) - χ(s - a))/(p(p - 1))`. -/
theorem sum_m12_chi_right (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (a s : F) : ∑ b, m12 a b * (χ (s - b) : ℝ) =
      (muF (F := F) * (qF * (if a = s then 1 else 0) - 1) - (χ (s - a) : ℝ)) /
        (qF * (qF - 1)) := by
  have e : ∀ b, m12 a b * (χ (s - b) : ℝ) = 1 / (qF * (qF - 1)) * (χ (s - b) : ℝ) +
      muF (F := F) / (qF * (qF - 1)) * ((χ (b - a) : ℝ) * (χ (b - s) : ℝ)) -
      1 / (qF * (qF - 1)) * (if a = b then (χ (s - b) : ℝ) else 0) := by
    intro b
    rw [m12_eq' hF h3 h7, chi_swap h3 s b]
    push_cast
    split_ifs <;> ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sumR_chi_sub hF s, sumR_chi_chi hF,
    sum_ite_eq, mem_univ, ↓reduceIte]
  ring

/-- `∑_a m₁₂(a, b) χ(s - a) = (-μ(p [b = s] - 1) - χ(s - b))/(p(p - 1))`. -/
theorem sum_m12_chi_left (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (b s : F) : ∑ a, m12 a b * (χ (s - a) : ℝ) =
      (-(muF (F := F) * (qF * (if b = s then 1 else 0) - 1)) - (χ (s - b) : ℝ)) /
        (qF * (qF - 1)) := by
  have e : ∀ a, m12 a b * (χ (s - a) : ℝ) = 1 / (qF * (qF - 1)) * (χ (s - a) : ℝ) -
      muF (F := F) / (qF * (qF - 1)) * ((χ (a - b) : ℝ) * (χ (a - s) : ℝ)) -
      1 / (qF * (qF - 1)) * (if b = a then (χ (s - a) : ℝ) else 0) := by
    intro a
    rw [m12_eq' hF h3 h7, chi_swap h3 s a, chi_swap h3 b a]
    push_cast
    by_cases hab : a = b
    · subst hab; simp only [↓reduceIte]; ring
    · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab)]; ring
  simp only [e, sum_sub_distrib, ← mul_sum, sumR_chi_sub hF s, sumR_chi_chi hF,
    sum_ite_eq, mem_univ, ↓reduceIte]
  ring

/-- **`lem:actual-features`(c): `V^*_{1,m} A₃ = -q/(p - 1) I + μ/(p - 1) P` on `H₀`**:
`p ∑_b m₁₂(a, b) (A₃ h)(a, b) = (-h(a) + μ p (P h)(a))/(p(p - 1))`. -/
theorem V1m_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (a : F) :
    qF * ∑ b, m12 a b * A3op h a b =
      (-h a + muF (F := F) * qF * paleyOp h a) / (qF * (qF - 1)) := by
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  simp only [A3op_meanZero h hh]
  -- swap the sums
  have hswap : ∑ b, m12 a b * -(qF⁻¹ * ∑ s, (χ (s - a) : ℝ) * (χ (s - b) : ℝ) * h s) =
      -(qF⁻¹ * ∑ s, (χ (s - a) : ℝ) * h s * ∑ b, m12 a b * (χ (s - b) : ℝ)) := by
    simp only [mul_neg, sum_neg_distrib, mul_sum]
    rw [sum_comm]
    refine congrArg Neg.neg (sum_congr rfl fun s _ => sum_congr rfl fun b _ => by ring)
  rw [hswap]
  simp only [sum_m12_chi_right hF h3 h7 a]
  have e : ∀ s, (χ (s - a) : ℝ) * h s * ((muF (F := F) * (qF * (if a = s then 1 else 0) - 1) -
      (χ (s - a) : ℝ)) / (qF * (qF - 1))) =
      (muF (F := F) * qF * (if a = s then (χ (s - a) : ℝ) * h s else 0) -
        muF (F := F) * ((χ (s - a) : ℝ) * h s) -
        (χ (s - a) : ℝ) * (χ (s - a) : ℝ) * h s) / (qF * (qF - 1)) := by
    intro s; split_ifs <;> ring
  simp only [e, ← sum_div, sum_sub_distrib, ← mul_sum, sum_ite_eq, mem_univ, ↓reduceIte,
    sub_self, quadraticChar_zero, Int.cast_zero, zero_mul, mul_zero, sum_chi_sq_mul h hh a]
  have hP : ∑ s, (χ (s - a) : ℝ) * h s = qF * paleyOp h a := by
    unfold paleyOp; field_simp
  rw [hP]
  field_simp
  ring

/-- **`lem:actual-features`(c): `V^*_{2,m} A₃ = -q/(p - 1) I - μ/(p - 1) P` on `H₀`**:
`p ∑_a m₁₂(a, b) (A₃ h)(a, b) = (-h(b) - μ p (P h)(b))/(p(p - 1))`. -/
theorem V2m_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (b : F) :
    qF * ∑ a, m12 a b * A3op h a b =
      (-h b - muF (F := F) * qF * paleyOp h b) / (qF * (qF - 1)) := by
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  simp only [A3op_meanZero h hh]
  have hswap : ∑ a, m12 a b * -(qF⁻¹ * ∑ s, (χ (s - a) : ℝ) * (χ (s - b) : ℝ) * h s) =
      -(qF⁻¹ * ∑ s, (χ (s - b) : ℝ) * h s * ∑ a, m12 a b * (χ (s - a) : ℝ)) := by
    simp only [mul_neg, sum_neg_distrib, mul_sum]
    rw [sum_comm]
    refine congrArg Neg.neg (sum_congr rfl fun s _ => sum_congr rfl fun a _ => by ring)
  rw [hswap]
  simp only [sum_m12_chi_left hF h3 h7 b]
  have e : ∀ s, (χ (s - b) : ℝ) * h s * ((-(muF (F := F) * (qF * (if b = s then 1 else 0) - 1)) -
      (χ (s - b) : ℝ)) / (qF * (qF - 1))) =
      (-(muF (F := F) * qF * (if b = s then (χ (s - b) : ℝ) * h s else 0)) +
        muF (F := F) * ((χ (s - b) : ℝ) * h s) -
        (χ (s - b) : ℝ) * (χ (s - b) : ℝ) * h s) / (qF * (qF - 1)) := by
    intro s; split_ifs <;> ring
  simp only [e, ← sum_div, sum_sub_distrib, sum_add_distrib, sum_neg_distrib, ← mul_sum,
    sum_ite_eq, mem_univ, ↓reduceIte, sub_self, quadraticChar_zero, Int.cast_zero, zero_mul,
    mul_zero, sum_chi_sq_mul h hh b]
  have hP : ∑ s, (χ (s - b) : ℝ) * h s = qF * paleyOp h b := by
    unfold paleyOp; field_simp
  rw [hP]
  field_simp
  ring

/-! ## The Gram of `A₃` -/

/-- `∑_{a,b} (A₃ h)(a, b)² = (1 - 2/p) ∑ h²` on `H₀` (the rectangular-star Gram `(0, 0, 1)`). -/
theorem sum_A3_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ a, ∑ b, A3op h a b ^ 2 = (1 - 2 / qF) * ∑ s, h s ^ 2 := by
  have h0 : qF ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  have e : ∀ a b, A3op h a b ^ 2 = qF⁻¹ ^ 2 * (∑ s, rectStar 0 0 1 s a b * h s) ^ 2 := by
    intro a b
    rw [A3op_meanZero h hh]
    have : ∑ s, (χ (s - a) : ℝ) * (χ (s - b) : ℝ) * h s = ∑ s, rectStar 0 0 1 s a b * h s := by
      refine sum_congr rfl fun s _ => ?_
      rw [rectStar_pairStar h3]
    rw [this]
    ring
  simp only [e, ← mul_sum]
  rw [rect_gram hF 0 0 1 h, hh]
  field_simp
  ring

/-- `∑_{a,b} χ(b - a) S(a, b) = 0` for a symmetric `S`. -/
theorem sum_chi_antisymm (h3 : Fintype.card F % 4 = 3) (S : F → F → ℝ)
    (hS : ∀ a b, S a b = S b a) : ∑ a, ∑ b, (χ (b - a) : ℝ) * S a b = 0 := by
  have h := sum_comm (s := (univ : Finset F)) (t := univ)
    (f := fun a b => (χ (b - a) : ℝ) * S a b)
  have e : ∑ b, ∑ a, (χ (b - a) : ℝ) * S a b = -∑ a, ∑ b, (χ (b - a) : ℝ) * S a b := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun b _ => ?_
    rw [chi_swap h3 a b, hS b a]
    push_cast
    ring
  linarith

/-- **`lem:actual-features`(c): `A₃^{*_m} A₃ = q(1 - 2q - q²)/(1 - q) I` on `H₀`**, as the
quadratic identity `∑_{a,b} m₁₂(a, b) (A₃ h)(a, b)² = (1 - 2q - q²)/(p - 1) · (1/p) ∑ h²`,
`q = 1/p`. -/
theorem A3_gram (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ a, ∑ b, m12 a b * A3op h a b ^ 2 =
      (1 - 2 * (1 / qF) - (1 / qF) ^ 2) / (qF - 1) * (qF⁻¹ * ∑ s, h s ^ 2) := by
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have e : ∀ a b, m12 a b * A3op h a b ^ 2 = 1 / (qF * (qF - 1)) * A3op h a b ^ 2 -
      muF (F := F) / (qF * (qF - 1)) * ((χ (b - a) : ℝ) * A3op h a b ^ 2) -
      1 / (qF * (qF - 1)) * (if a = b then A3op h a b ^ 2 else 0) := by
    intro a b
    rw [m12_eq' hF h3 h7]
    split_ifs <;> ring
  simp only [e, sum_sub_distrib, ← mul_sum]
  rw [sum_A3_sq hF h3 h hh, sum_chi_antisymm h3 (fun a b => A3op h a b ^ 2)
    (fun a b => by rw [A3op_symm])]
  have hdiag : ∑ a : F, ∑ b : F, (if a = b then A3op h a b ^ 2 else 0) =
      qF⁻¹ ^ 2 * ∑ s, h s ^ 2 := by
    have hd : ∀ a, A3op h a a = qF⁻¹ * h a := by
      intro a
      rw [A3op_meanZero h hh, sum_chi_sq_mul h hh a]
      ring
    simp only [sum_ite_eq, mem_univ, ↓reduceIte, hd, mul_pow, ← mul_sum]
  rw [hdiag]
  field_simp
  ring

end Sarkozy.MiddleRecords
