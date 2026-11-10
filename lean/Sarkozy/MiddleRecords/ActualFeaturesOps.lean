module

public import Sarkozy.MiddleRecords.ActualFeatures

/-!
# The singleton correlations of the actual half marginal (`lem:actual-features`(b))

`paper/sections/21_middle_records.tex`, `lem:actual-features`(b). Under `m₀` every coordinate
is uniform (`sum_m01`, `sum_m12`, `sum_m02`), so the conditional expectation of `f(x_j)` given
`x_i = a` is `p ∑_b m_{ij}(a, b) f(b)` (`condOp`); this is the operator `V^*_{i,m} V_j` on
functions of one label. On the mean-zero functions `H₀` (`∑ f = 0`), with `q = 1/p`, `μ = 2/(p-4)`
and the Paley operator `P` (WP-S's `paleyOp`):

* `V^*_{0,m} V_2 = (P - qI)/(1 - q)` (`V0m_V2`);
* `V^*_{0,m} V_1 = V^*_{1,m} V_2 = -(I + μ p P)/(p - 1)` (`V0m_V1`, `V1m_V2`);
* `‖V^*_{0,m} V_2 f‖² = ϱ₀₂² ‖f‖²` with `ϱ₀₂² = q(1 + q)/(1 - q)²`, i.e.
  `ϱ₀₂ = r (1 + q)^{1/2}/(1 - q)` (`norm_V0m_V2`), and
  `‖V^*_{0,m} V_1 f‖² = ‖V^*_{1,m} V_2 f‖² = ϱ₀₁² ‖f‖²` with
  `ϱ₀₁² = (q/(1 - q))² (1 + 4q/(1 - 4q)²)` (`norm_V0m_V1`, `norm_V1m_V2`, `rho01_sq_eq`).

Both operators are multiples of isometries of `H₀` (the norm identities hold for every `f`), so
on `H₀ ≠ 0` their operator norms are exactly `ϱ₀₂` and `ϱ₀₁`, as the paper states. Norms are
those of the counting measure on `F`; the uniform `L²` norm differs by the common factor `1/p`,
which cancels.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-! ## The pair laws on all pairs -/

theorem m01_eq' (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (a b : F) :
    m01 a b = (1 - muF (F := F) * (χ (b - a) : ℝ) - if a = b then 1 else 0) / (qF * (qF - 1)) := by
  by_cases h : a = b
  · subst h
    rw [(m_diag a).2.1, ite_eq_left (show a = a from rfl), sub_self, quadraticChar_zero]
    simp
  · rw [m01_eq hF h3 h7 h, ite_eq_right h, sub_zero]

theorem m12_eq' (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (a b : F) :
    m12 a b = (1 - muF (F := F) * (χ (b - a) : ℝ) - if a = b then 1 else 0) / (qF * (qF - 1)) := by
  by_cases h : a = b
  · subst h
    rw [(m_diag a).1, ite_eq_left (show a = a from rfl), sub_self, quadraticChar_zero]
    simp
  · rw [m12_eq hF h3 h7 h, ite_eq_right h, sub_zero]

theorem m02_eq' (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (a b : F) :
    m02 a b = (1 + (χ (b - a) : ℝ) - if a = b then 1 else 0) / (qF * (qF - 1)) := by
  by_cases h : a = b
  · subst h
    rw [(m_diag a).2.2, ite_eq_left (show a = a from rfl), sub_self, quadraticChar_zero]
    simp
  · rw [m02_eq hF h3 h7 h, ite_eq_right h, sub_zero, ← one_add_chi_div_two h]
    ring

/-! ## The conditional operators -/

/-- `∑_b (c₀ + c₁ χ(b - a) - c₂ [a = b]) f(b) = c₀ ∑ f + c₁ p (P f)(a) - c₂ f(a)`. -/
theorem sum_pair_mul (c₀ c₁ c₂ : ℝ) (f : F → ℝ) (a : F) :
    ∑ b, (c₀ + c₁ * (χ (b - a) : ℝ) - c₂ * (if a = b then 1 else 0)) * f b =
      c₀ * ∑ b, f b + c₁ * (qF * paleyOp f a) - c₂ * f a := by
  have hP : qF * paleyOp f a = ∑ b, (χ (b - a) : ℝ) * f b := by
    unfold paleyOp
    have : qF ≠ 0 := by
      have := Fintype.card_pos (α := F)
      positivity
    field_simp
  rw [hP]
  simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum]
  rw [show ∑ b, (if a = b then (1 : ℝ) else 0) * f b = f a by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]]

/-- The conditional expectation `(V^*_{i,m} V_j f)(a) = p ∑_b m_{ij}(a, b) f(b)`. -/
noncomputable def condOp (m : F → F → ℝ) (f : F → ℝ) (a : F) : ℝ := qF * ∑ b, m a b * f b

/-- **The coordinate `x₀` is uniform** under `m₀`: `∑_b m₀₁(a, b) = 1/p`. -/
theorem sum_m01 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (a : F) :
    ∑ b, m01 a b = 1 / qF := by
  have h := sum_pair_mul (1 / (qF * (qF - 1))) (-(muF (F := F)) / (qF * (qF - 1)))
    (1 / (qF * (qF - 1))) (fun _ => 1) a
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  calc ∑ b, m01 a b = ∑ b, (1 / (qF * (qF - 1)) + -(muF (F := F)) / (qF * (qF - 1)) *
        (χ (b - a) : ℝ) - 1 / (qF * (qF - 1)) * (if a = b then 1 else 0)) * 1 :=
        sum_congr rfl fun b _ => by rw [m01_eq' hF h3 h7]; ring
    _ = _ := h
    _ = 1 / qF := by
        rw [paleyOp_const hF 1 a, sum_const, card_univ, nsmul_eq_mul, mul_one]
        field_simp
        ring

/-- **`lem:actual-features`(b): `V^*_{0,m} V_1 = -(I + μ p P)/(p - 1)` on `H₀`.** -/
theorem V0m_V1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (f : F → ℝ)
    (hf : ∑ b, f b = 0) (a : F) :
    condOp m01 f a = -(f a + muF (F := F) * qF * paleyOp f a) / (qF - 1) := by
  unfold condOp
  have e : ∀ b, m01 a b * f b = (1 / (qF * (qF - 1)) + -(muF (F := F)) / (qF * (qF - 1)) *
      (χ (b - a) : ℝ) - 1 / (qF * (qF - 1)) * (if a = b then 1 else 0)) * f b := by
    intro b; rw [m01_eq' hF h3 h7]; ring
  simp only [e]
  rw [sum_pair_mul, hf]
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- **`lem:actual-features`(b): `V^*_{1,m} V_2 = -(I + μ p P)/(p - 1)` on `H₀`.** -/
theorem V1m_V2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (f : F → ℝ)
    (hf : ∑ b, f b = 0) (a : F) :
    condOp m12 f a = -(f a + muF (F := F) * qF * paleyOp f a) / (qF - 1) := by
  unfold condOp
  have e : ∀ b, m12 a b * f b = (1 / (qF * (qF - 1)) + -(muF (F := F)) / (qF * (qF - 1)) *
      (χ (b - a) : ℝ) - 1 / (qF * (qF - 1)) * (if a = b then 1 else 0)) * f b := by
    intro b; rw [m12_eq' hF h3 h7]; ring
  simp only [e]
  rw [sum_pair_mul, hf]
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- **`lem:actual-features`(b): `V^*_{0,m} V_2 = (P - qI)/(1 - q)` on `H₀`**, `q = 1/p`. -/
theorem V0m_V2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (f : F → ℝ)
    (hf : ∑ b, f b = 0) (a : F) :
    condOp m02 f a = (paleyOp f a - (1 / qF) * f a) / (1 - 1 / qF) := by
  unfold condOp
  have e : ∀ b, m02 a b * f b = (1 / (qF * (qF - 1)) + 1 / (qF * (qF - 1)) *
      (χ (b - a) : ℝ) - 1 / (qF * (qF - 1)) * (if a = b then 1 else 0)) * f b := by
    intro b; rw [m02_eq' hF h3 h7]; ring
  simp only [e]
  rw [sum_pair_mul, hf]
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp
  ring

/-! ## The norms -/

theorem sum_mul_paleyOp_self (h3 : Fintype.card F % 4 = 3) (f : F → ℝ) :
    ∑ s, f s * paleyOp f s = 0 := by
  have h := paleyOp_adjoint h3 f f
  have e : ∑ s, paleyOp f s * f s = ∑ s, f s * paleyOp f s :=
    sum_congr rfl fun s _ => mul_comm _ _
  linarith

theorem sum_paleyOp_sq (hF : ringChar F ≠ 2) (f : F → ℝ) (hf : ∑ s, f s = 0) :
    ∑ s, paleyOp f s ^ 2 = qF⁻¹ * ∑ s, f s ^ 2 := by
  have h := norm_paleyOp hF f
  rw [hf, mul_zero, zero_pow two_ne_zero, sub_zero] at h
  have h0 : qF⁻¹ ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  exact mul_left_cancel₀ h0 h

/-- **`ϱ₀₂`**: `‖V^*_{0,m} V_2 f‖² = q(1 + q)/(1 - q)² ‖f‖²` on `H₀`, `q = 1/p`. -/
theorem norm_V0m_V2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ b, f b = 0) :
    ∑ a, condOp m02 f a ^ 2 = (1 / qF) * (1 + 1 / qF) / (1 - 1 / qF) ^ 2 * ∑ a, f a ^ 2 := by
  simp only [V0m_V2 hF h3 h7 f hf]
  have hq : 1 - 1 / qF ≠ 0 := by
    have : 1 / qF < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have e : ∀ a, ((paleyOp f a - (1 / qF) * f a) / (1 - 1 / qF)) ^ 2 =
      (paleyOp f a ^ 2 - 2 * (1 / qF) * (f a * paleyOp f a) + (1 / qF) ^ 2 * f a ^ 2) /
        (1 - 1 / qF) ^ 2 := by
    intro a; rw [div_pow]; congr 1; ring
  simp only [e, ← sum_div, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_paleyOp_sq hF f hf, sum_mul_paleyOp_self h3 f]
  have h0 : qF ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- **`ϱ₀₁`**: `‖V^*_{0,m} V_1 f‖² = (1 + μ² p)/(p - 1)² ‖f‖²` on `H₀`. -/
theorem norm_V0m_V1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ b, f b = 0) :
    ∑ a, condOp m01 f a ^ 2 = (1 + muF (F := F) ^ 2 * qF) / (qF - 1) ^ 2 * ∑ a, f a ^ 2 := by
  simp only [V0m_V1 hF h3 h7 f hf]
  have e : ∀ a, (-(f a + muF (F := F) * qF * paleyOp f a) / (qF - 1)) ^ 2 =
      (f a ^ 2 + 2 * (muF (F := F) * qF) * (f a * paleyOp f a) +
        (muF (F := F) * qF) ^ 2 * paleyOp f a ^ 2) / (qF - 1) ^ 2 := by
    intro a; rw [div_pow]; congr 1; ring
  simp only [e, ← sum_div, sum_add_distrib, ← mul_sum, sum_paleyOp_sq hF f hf,
    sum_mul_paleyOp_self h3 f]
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- **`ϱ₀₁` for `V^*_{1,m} V_2`**: the same norm identity. -/
theorem norm_V1m_V2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ b, f b = 0) :
    ∑ a, condOp m12 f a ^ 2 = (1 + muF (F := F) ^ 2 * qF) / (qF - 1) ^ 2 * ∑ a, f a ^ 2 := by
  have h01 := norm_V0m_V1 hF h3 h7 f hf
  have e : ∀ a, condOp m12 f a = condOp m01 f a := by
    intro a; rw [V1m_V2 hF h3 h7 f hf, V0m_V1 hF h3 h7 f hf]
  simp only [e]
  exact h01

omit [Field F] [DecidableEq F] in
/-- **The paper's form of `ϱ₀₁`**: `(1 + μ² p)/(p - 1)² = (q/(1 - q))² (1 + 4q/(1 - 4q)²)`,
`q = 1/p`, `μ = 2/(p - 4)`. -/
theorem rho01_sq_eq (h7 : 7 ≤ qF) :
    (1 + muF (F := F) ^ 2 * qF) / (qF - 1) ^ 2 =
      ((1 / qF) / (1 - 1 / qF)) ^ 2 * (1 + 4 * (1 / qF) / (1 - 4 * (1 / qF)) ^ 2) := by
  unfold muF
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  have h4 : qF - 4 ≠ 0 := by intro h; linarith
  have h1' : 1 - 1 / qF ≠ 0 := by
    rw [one_sub_div h0]; exact div_ne_zero h1 h0
  have h4' : 1 - 4 * (1 / qF) ≠ 0 := by
    rw [mul_one_div, one_sub_div h0]; exact div_ne_zero h4 h0
  field_simp
  ring

end Sarkozy.MiddleRecords
