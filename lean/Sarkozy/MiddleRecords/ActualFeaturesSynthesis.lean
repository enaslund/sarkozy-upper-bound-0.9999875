module

public import Sarkozy.MiddleRecords.ActualFeaturesNorms
public import Sarkozy.MiddleRecords.ActualFeaturesA3V0
public import Sarkozy.TraceMixing.PaleySquare

/-!
# The synthesis bound `Γ_A` (`lem:actual-features`(d))

`paper/sections/21_middle_records.tex`, `lem:actual-features`(d): the synthesis map
`(h₀, h₁, h₂, h₃) ↦ V₀h₀ + (A₂h₁ + A₁h₂ + A₃h₃)/r` from `H₀⁴` to `L²(m₀)` has squared norm at most
`Γ_A = 1 + ϱ₀₂ + 2ϱ₀₁ + qr(1 + 4q)/((1 - q)(1 - 4q)) + 2qr/(1 - q) + 4q²/((1 - q)(1 - 4q))`.

`synthesis_bound`: `‖V₀h₀ + √p(A₂h₁ + A₁h₂ + A₃h₃)‖²_{m₀} ≤ Γ ∑ᵢ ‖hᵢ‖²` (`1/r = √p`) with
`Γ = 1 + ϱ₀₂ + 2ϱ₀₁ + g₀₃ + 2g₁₃`, and `Γ ≤ Γ_A` (`gamma_le_GammaA`). As in the paper the Gram of
the four maps is bounded entry by entry and the Schur test (here AM–GM on each pair) bounds the
form by the largest row sum:
* the diagonal entries are `‖h₀‖²`, `‖h₁‖²`, `‖h₂‖²` and at most `‖h₃‖²` (`diag0`, …, `diag3`,
  from `sum_m01`, `norm_A2_sq`, `norm_A1_sq`, `norm_A3_sq_le`);
* the off-diagonal entries are bounded by Cauchy–Schwarz after reducing the `m₀`-integral to a
  pair law (`Iw_pair01`, `Iw_pair02`, `Iw_pair12`): `ϱ₀₁` (`cross01`, `cross12`), `ϱ₀₂`
  (`cross02`), `g₀₃ = ‖A₃^{*m}V₀‖/r` (`cross03`, from `A3_V0`), and
  `g₁₃ = √(1 + μ²p)/(√p (p - 1)) ≥ ‖V^*_{i,m}A₃‖/r` (`cross13`, `cross23`, from `V1m_A3`,
  `V2m_A3`); `g₁₃` is at most the paper's `qr/(1 - q) + 2q²/((1 - q)(1 - 4q))`.

`h₀` need not have mean zero. The `m₀`-integral is `Iw G / oldZ` with
`Iw G = ∑_x oldW(x) G(x)`.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- The unnormalized `m₀`-integral `∑_x oldW(x) G(x)`. -/
noncomputable def Iw (G : F → F → F → ℝ) : ℝ := ∑ a, ∑ b, ∑ c, oldW a b c * G a b c

theorem Iw_add (G G' : F → F → F → ℝ) :
    Iw (fun a b c => G a b c + G' a b c) = Iw G + Iw G' := by
  unfold Iw
  rw [← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  ring

theorem Iw_pair01 (hZ : oldZ (F := F) ≠ 0) (G : F → F → ℝ) :
    Iw (fun a b _ => G a b) = oldZ (F := F) * ∑ a, ∑ b, m01 a b * G a b := by
  unfold Iw m01
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [← sum_mul]
  field_simp

theorem Iw_pair02 (hZ : oldZ (F := F) ≠ 0) (G : F → F → ℝ) :
    Iw (fun a _ c => G a c) = oldZ (F := F) * ∑ a, ∑ c, m02 a c * G a c := by
  unfold Iw m02
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [← sum_mul]
  field_simp

theorem Iw_pair12 (hZ : oldZ (F := F) ≠ 0) (G : F → F → ℝ) :
    Iw (fun _ b c => G b c) = oldZ (F := F) * ∑ b, ∑ c, m12 b c * G b c := by
  unfold Iw m12
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [← sum_mul]
  field_simp


theorem Iw_smul (k : ℝ) (G : F → F → F → ℝ) : Iw (fun a b c => k * G a b c) = k * Iw G := by
  unfold Iw
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  ring

omit [Field F] [DecidableEq F] in
theorem abs_sum_mul_le (f g : F → ℝ) :
    |∑ a, f a * g a| ≤ Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ a, g a ^ 2) := by
  rw [← Real.sqrt_mul (sum_nonneg fun a _ => sq_nonneg (f a))]
  exact Real.abs_le_sqrt (sum_mul_sq_le_sq_mul_sq univ f g)

omit [DecidableEq F] in
/-- `|∑_{a,b} m(a, b) f(a) g(b)| ≤ p⁻¹ √(∑ f²) √(∑ (condOp m g)²)`. -/
theorem abs_pair_le (m : F → F → ℝ) (f g : F → ℝ) :
    |∑ a, ∑ b, m a b * f a * g b| ≤
      qF⁻¹ * (Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ a, condOp m g a ^ 2)) := by
  have h0 : qF ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  have e : ∑ a, ∑ b, m a b * f a * g b = qF⁻¹ * ∑ a, f a * condOp m g a := by
    unfold condOp
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    field_simp
  rw [e, abs_mul, abs_of_pos (inv_pos.mpr (by positivity))]
  exact mul_le_mul_of_nonneg_left (abs_sum_mul_le _ _) (by positivity)


/-- `ϱ₀₁² = (1 + μ² p)/(p - 1)²`. -/
noncomputable def rho01sq : ℝ := (1 + muF (F := F) ^ 2 * qF) / (qF - 1) ^ 2

/-- `ϱ₀₂² = q(1 + q)/(1 - q)²`, `q = 1/p`. -/
noncomputable def rho02sq : ℝ := (1 / qF) * (1 + 1 / qF) / (1 - 1 / qF) ^ 2

/-- The `(A₃, V₀)` entry of the Gram matrix, `√p (p + 4)/(p(p - 1)(p - 4))`
(`= qr(1 + 4q)/((1 - q)(1 - 4q))`). -/
noncomputable def g03 : ℝ := Real.sqrt qF * (qF + 4) / (qF * (qF - 1) * (qF - 4))

/-- The `(A₃, V₁)`, `(A₃, V₂)` entries, `√(1 + μ² p) √p/(p(p - 1))`
(`≤ qr/(1 - q) + 2q²/((1 - q)(1 - 4q))`). -/
noncomputable def g13 : ℝ :=
  Real.sqrt (1 + muF (F := F) ^ 2 * qF) * Real.sqrt qF / (qF * (qF - 1))

theorem sum_sq_V1m_A3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h : F → ℝ)
    (hh : ∑ s, h s = 0) (sgn : ℝ) (hsgn : sgn ^ 2 = 1) :
    ∑ a, ((-h a + sgn * (muF (F := F) * qF * paleyOp h a)) / (qF * (qF - 1))) ^ 2 =
      (1 + muF (F := F) ^ 2 * qF) * ∑ a, h a ^ 2 / (qF * (qF - 1)) ^ 2 := by
  have h0 : qF ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  have e : ∀ a, ((-h a + sgn * (muF (F := F) * qF * paleyOp h a)) / (qF * (qF - 1))) ^ 2 =
      (h a ^ 2 - 2 * sgn * (muF (F := F) * qF) * (h a * paleyOp h a) +
        sgn ^ 2 * (muF (F := F) * qF) ^ 2 * paleyOp h a ^ 2) / (qF * (qF - 1)) ^ 2 := by
    intro a; rw [div_pow]; congr 1; ring
  simp only [e, ← sum_div, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    sum_mul_paleyOp_self h3 h, sum_paleyOp_sq hF h hh, hsgn]
  field_simp
  ring


omit [DecidableEq F] in
theorem sqrt_sum_sq (h : F → ℝ) :
    Real.sqrt (∑ a, h a ^ 2) = Real.sqrt qF * Real.sqrt (unifNormSq h) := by
  have h0 : qF ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  rw [← Real.sqrt_mul (by positivity), unifNormSq, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

omit [DecidableEq F] in
theorem unifNormSq_nonneg (h : F → ℝ) : 0 ≤ unifNormSq h := by
  unfold unifNormSq; positivity

theorem sum_paleyOp_sq_eq (hF : ringChar F ≠ 2) (h : F → ℝ) (hh : ∑ s, h s = 0) :
    ∑ a, paleyOp h a ^ 2 = unifNormSq h := by
  rw [sum_paleyOp_sq hF h hh, unifNormSq]

omit [DecidableEq F] in
/-- A generic pair term: `|2k ∑_{a,b} m(a,b) f(a) g(b)| ≤ 2 k p⁻¹ √(∑ f²) √(c ∑ g²)` when
`∑ (condOp m g)² = c ∑ g²`. -/
theorem cross_pair (m : F → F → ℝ) (f g : F → ℝ) {k c : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hcond : ∑ a, condOp m g a ^ 2 = c * ∑ a, g a ^ 2) :
    |2 * k * ∑ a, ∑ b, m a b * f a * g b| ≤
      2 * k * (qF⁻¹ * (Real.sqrt (∑ a, f a ^ 2) * (Real.sqrt c * Real.sqrt (∑ a, g a ^ 2)))) := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_pair_le m f g).trans ?_
  rw [hcond, Real.sqrt_mul hc]

/-- **The `(V₀, A₂/r)` term**: `|2√p ∑ m₀₁ h₀ (P h₁)| ≤ 2 ϱ₀₁ ‖h₀‖ ‖h₁‖`. -/
theorem cross01 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₀ h₁ : F → ℝ) (hh₁ : ∑ s, h₁ s = 0) :
    |2 * Real.sqrt qF * ∑ a, ∑ b, m01 a b * h₀ a * paleyOp h₁ b| ≤
      2 * Real.sqrt (rho01sq (F := F)) *
        (Real.sqrt (unifNormSq h₀) * Real.sqrt (unifNormSq h₁)) := by
  have h0 : 0 < qF := by linarith
  have hρ : 0 ≤ rho01sq (F := F) := by unfold rho01sq; positivity
  have hb := cross_pair m01 h₀ (paleyOp h₁) (Real.sqrt_nonneg qF) hρ
    (norm_V0m_V1 hF h3 h7 (paleyOp h₁) (paleyOp_mean hF h₁))
  rw [sqrt_sum_sq, sum_paleyOp_sq_eq hF h₁ hh₁] at hb
  refine hb.trans (le_of_eq ?_)
  have hs : Real.sqrt qF * Real.sqrt qF = qF := Real.mul_self_sqrt h0.le
  calc 2 * Real.sqrt qF * (qF⁻¹ * (Real.sqrt qF * Real.sqrt (unifNormSq h₀) *
        (Real.sqrt (rho01sq (F := F)) * Real.sqrt (unifNormSq h₁))))
      = 2 * (Real.sqrt qF * Real.sqrt qF) * qF⁻¹ * Real.sqrt (rho01sq (F := F)) *
          (Real.sqrt (unifNormSq h₀) * Real.sqrt (unifNormSq h₁)) := by ring
    _ = _ := by rw [hs, mul_assoc 2 qF, mul_inv_cancel₀ h0.ne', mul_one]


/-- **The `(V₀, A₁/r)` term**: `|2√p ∑ m₀₂ h₀ (P h₂)| ≤ 2 ϱ₀₂ ‖h₀‖ ‖h₂‖`. -/
theorem cross02 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₀ h₂ : F → ℝ) (hh₂ : ∑ s, h₂ s = 0) :
    |2 * Real.sqrt qF * ∑ a, ∑ b, m02 a b * h₀ a * paleyOp h₂ b| ≤
      2 * Real.sqrt (rho02sq (F := F)) *
        (Real.sqrt (unifNormSq h₀) * Real.sqrt (unifNormSq h₂)) := by
  have h0 : 0 < qF := by linarith
  have hρ : 0 ≤ rho02sq (F := F) := by unfold rho02sq; positivity
  have hb := cross_pair m02 h₀ (paleyOp h₂) (Real.sqrt_nonneg qF) hρ
    (norm_V0m_V2 hF h3 h7 (paleyOp h₂) (paleyOp_mean hF h₂))
  rw [sqrt_sum_sq, sum_paleyOp_sq_eq hF h₂ hh₂] at hb
  refine hb.trans (le_of_eq ?_)
  have hs : Real.sqrt qF * Real.sqrt qF = qF := Real.mul_self_sqrt h0.le
  calc 2 * Real.sqrt qF * (qF⁻¹ * (Real.sqrt qF * Real.sqrt (unifNormSq h₀) *
        (Real.sqrt (rho02sq (F := F)) * Real.sqrt (unifNormSq h₂))))
      = 2 * (Real.sqrt qF * Real.sqrt qF) * qF⁻¹ * Real.sqrt (rho02sq (F := F)) *
          (Real.sqrt (unifNormSq h₀) * Real.sqrt (unifNormSq h₂)) := by ring
    _ = _ := by rw [hs, mul_assoc 2 qF, mul_inv_cancel₀ h0.ne', mul_one]

/-- **The `(A₂/r, A₁/r)` term**: `|2p ∑ m₁₂ (P h₁)(P h₂)| ≤ 2 ϱ₀₁ ‖h₁‖ ‖h₂‖`. -/
theorem cross12 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₁ h₂ : F → ℝ) (hh₁ : ∑ s, h₁ s = 0) (hh₂ : ∑ s, h₂ s = 0) :
    |2 * qF * ∑ a, ∑ b, m12 a b * paleyOp h₁ a * paleyOp h₂ b| ≤
      2 * Real.sqrt (rho01sq (F := F)) *
        (Real.sqrt (unifNormSq h₁) * Real.sqrt (unifNormSq h₂)) := by
  have h0 : 0 < qF := by linarith
  have hρ : 0 ≤ rho01sq (F := F) := by unfold rho01sq; positivity
  have hb := cross_pair m12 (paleyOp h₁) (paleyOp h₂) h0.le hρ
    (norm_V1m_V2 hF h3 h7 (paleyOp h₂) (paleyOp_mean hF h₂))
  rw [sum_paleyOp_sq_eq hF h₁ hh₁, sum_paleyOp_sq_eq hF h₂ hh₂] at hb
  refine hb.trans (le_of_eq ?_)
  field_simp

/-- **The `(A₂/r, A₃/r)` term**: `|2p ∑ m₁₂ (P h₁)(A₃ h₃)| ≤ 2 g₁₃ ‖h₁‖ ‖h₃‖`. -/
theorem cross13 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₁ k : F → ℝ) (hh₁ : ∑ s, h₁ s = 0) (hk : ∑ s, k s = 0) :
    |2 * qF * ∑ a, ∑ b, m12 a b * paleyOp h₁ a * A3op k a b| ≤
      2 * g13 (F := F) * (Real.sqrt (unifNormSq h₁) * Real.sqrt (unifNormSq k)) := by
  have h0 : 0 < qF := by linarith
  have h1 : 0 < qF - 1 := by linarith
  set v : F → ℝ := fun a => (-k a + 1 * (muF (F := F) * qF * paleyOp k a)) / (qF * (qF - 1))
    with hv
  have e : ∑ a, ∑ b, m12 a b * paleyOp h₁ a * A3op k a b = qF⁻¹ * ∑ a, paleyOp h₁ a * v a := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have := V1m_A3 hF h3 h7 k hk a
    rw [hv]
    simp only
    rw [one_mul, ← this, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    field_simp
  have hv2 : ∑ a, v a ^ 2 = (1 + muF (F := F) ^ 2 * qF) * ∑ a, k a ^ 2 / (qF * (qF - 1)) ^ 2 :=
    sum_sq_V1m_A3 hF h3 k hk 1 (by norm_num)
  rw [e]
  have hcs := abs_sum_mul_le (paleyOp h₁) v
  rw [sum_paleyOp_sq_eq hF h₁ hh₁, hv2] at hcs
  have hD : 0 < qF * (qF - 1) := by positivity
  have hsq : Real.sqrt ((1 + muF (F := F) ^ 2 * qF) * ∑ a, k a ^ 2 / (qF * (qF - 1)) ^ 2) =
      Real.sqrt (1 + muF (F := F) ^ 2 * qF) * (Real.sqrt qF * Real.sqrt (unifNormSq k)) /
        (qF * (qF - 1)) := by
    rw [← sum_div, ← mul_div_assoc, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hD.le, sqrt_sum_sq]
  rw [hsq] at hcs
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h0,
    abs_of_pos (inv_pos.mpr h0)]
  calc 2 * qF * (qF⁻¹ * |∑ a, paleyOp h₁ a * v a|)
      ≤ 2 * qF * (qF⁻¹ * (Real.sqrt (unifNormSq h₁) * (Real.sqrt (1 + muF (F := F) ^ 2 * qF) *
          (Real.sqrt qF * Real.sqrt (unifNormSq k)) / (qF * (qF - 1))))) := by
        gcongr
    _ = _ := by
        unfold g13
        field_simp

/-- **The `(A₁/r, A₃/r)` term**: `|2p ∑ m₁₂ (P h₂)(A₃ h₃)| ≤ 2 g₁₃ ‖h₂‖ ‖h₃‖`. -/
theorem cross23 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₂ k : F → ℝ) (hh₂ : ∑ s, h₂ s = 0) (hk : ∑ s, k s = 0) :
    |2 * qF * ∑ a, ∑ b, m12 a b * paleyOp h₂ b * A3op k a b| ≤
      2 * g13 (F := F) * (Real.sqrt (unifNormSq h₂) * Real.sqrt (unifNormSq k)) := by
  have h0 : 0 < qF := by linarith
  have h1 : 0 < qF - 1 := by linarith
  set v : F → ℝ := fun b => (-k b + -1 * (muF (F := F) * qF * paleyOp k b)) / (qF * (qF - 1))
    with hv
  have e : ∑ a, ∑ b, m12 a b * paleyOp h₂ b * A3op k a b = qF⁻¹ * ∑ b, paleyOp h₂ b * v b := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    have := V2m_A3 hF h3 h7 k hk b
    rw [hv]
    simp only
    rw [show -k b + -1 * (muF (F := F) * qF * paleyOp k b) =
      -k b - muF (F := F) * qF * paleyOp k b by ring, ← this, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    field_simp
  have hv2 : ∑ b, v b ^ 2 = (1 + muF (F := F) ^ 2 * qF) * ∑ a, k a ^ 2 / (qF * (qF - 1)) ^ 2 :=
    sum_sq_V1m_A3 hF h3 k hk (-1) (by norm_num)
  rw [e]
  have hcs := abs_sum_mul_le (paleyOp h₂) v
  rw [sum_paleyOp_sq_eq hF h₂ hh₂, hv2] at hcs
  have hD : 0 < qF * (qF - 1) := by positivity
  have hsq : Real.sqrt ((1 + muF (F := F) ^ 2 * qF) * ∑ a, k a ^ 2 / (qF * (qF - 1)) ^ 2) =
      Real.sqrt (1 + muF (F := F) ^ 2 * qF) * (Real.sqrt qF * Real.sqrt (unifNormSq k)) /
        (qF * (qF - 1)) := by
    rw [← sum_div, ← mul_div_assoc, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hD.le, sqrt_sum_sq]
  rw [hsq] at hcs
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h0,
    abs_of_pos (inv_pos.mpr h0)]
  calc 2 * qF * (qF⁻¹ * |∑ b, paleyOp h₂ b * v b|)
      ≤ 2 * qF * (qF⁻¹ * (Real.sqrt (unifNormSq h₂) * (Real.sqrt (1 + muF (F := F) ^ 2 * qF) *
          (Real.sqrt qF * Real.sqrt (unifNormSq k)) / (qF * (qF - 1))))) := by
        gcongr
    _ = _ := by
        unfold g13
        field_simp


/-- **The `(V₀, A₃/r)` term**: `|2√p E_{m₀}[h₀(x₀)(A₃ h₃)(x₁, x₂)]| ≤ 2 g₀₃ ‖h₀‖ ‖h₃‖`. -/
theorem cross03 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₀ k : F → ℝ) (hk : ∑ s, k s = 0) :
    |2 * Real.sqrt qF * (Iw (fun a b c => h₀ a * A3op k b c) / oldZ (F := F))| ≤
      2 * g03 (F := F) * (Real.sqrt (unifNormSq h₀) * Real.sqrt (unifNormSq k)) := by
  have h0 : 0 < qF := by linarith
  have hIw : Iw (fun a b c => h₀ a * A3op k b c) =
      ∑ a, ∑ b, ∑ c, oldW a b c * A3op k b c * h₀ a := by
    unfold Iw
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by ring
  rw [hIw, A3_V0 hF h3 h7 k h₀ hk]
  have hcs := abs_sum_mul_le k h₀
  rw [sqrt_sum_sq, sqrt_sum_sq] at hcs
  have hc : 0 ≤ (qF + 4) / (qF * (qF - 1) * (qF - 4)) := by
    have : 0 < qF - 4 := by linarith
    have : 0 < qF - 1 := by linarith
    positivity
  simp only [abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hc, abs_of_pos (inv_pos.mpr h0)]
  have hs : Real.sqrt qF * Real.sqrt qF = qF := Real.mul_self_sqrt h0.le
  calc 2 * Real.sqrt qF * ((qF + 4) / (qF * (qF - 1) * (qF - 4)) * (qF⁻¹ * |∑ s, k s * h₀ s|))
      ≤ 2 * Real.sqrt qF * ((qF + 4) / (qF * (qF - 1) * (qF - 4)) *
          (qF⁻¹ * (Real.sqrt qF * Real.sqrt (unifNormSq k) *
            (Real.sqrt qF * Real.sqrt (unifNormSq h₀))))) := by gcongr
    _ = 2 * g03 (F := F) * (Real.sqrt (unifNormSq h₀) * Real.sqrt (unifNormSq k)) := by
        unfold g03
        have e : Real.sqrt qF * Real.sqrt (unifNormSq k) *
            (Real.sqrt qF * Real.sqrt (unifNormSq h₀)) =
            (Real.sqrt qF * Real.sqrt qF) *
              (Real.sqrt (unifNormSq h₀) * Real.sqrt (unifNormSq k)) := by
          ring
        rw [e, hs]
        field_simp

/-! ## The diagonal terms -/

theorem diag0 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h₀ : F → ℝ) :
    Iw (fun a _ _ => h₀ a ^ 2) / oldZ (F := F) = unifNormSq h₀ := by
  have hZ := (oldZ_pos hF h3 h7).ne'
  rw [Iw_pair01 hZ (fun a _ => h₀ a ^ 2), mul_div_cancel_left₀ _ hZ]
  have e : ∀ a, ∑ b, m01 a b * h₀ a ^ 2 = h₀ a ^ 2 * ∑ b, m01 a b := by
    intro a; rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
  simp only [e, sum_m01 hF h3 h7, unifNormSq]
  rw [← sum_mul]
  ring

theorem diag1 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h₁ : F → ℝ)
    (hh₁ : ∑ s, h₁ s = 0) :
    Iw (fun _ b _ => qF * paleyOp h₁ b ^ 2) / oldZ (F := F) = unifNormSq h₁ := by
  have hZ := (oldZ_pos hF h3 h7).ne'
  have h0 : qF ≠ 0 := by intro h; linarith
  rw [Iw_smul, Iw_pair12 hZ (fun b _ => paleyOp h₁ b ^ 2), norm_A2_sq hF h3 h7 h₁ hh₁]
  field_simp

theorem diag2 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (h₂ : F → ℝ)
    (hh₂ : ∑ s, h₂ s = 0) :
    Iw (fun _ _ c => qF * paleyOp h₂ c ^ 2) / oldZ (F := F) = unifNormSq h₂ := by
  have hZ := (oldZ_pos hF h3 h7).ne'
  have h0 : qF ≠ 0 := by intro h; linarith
  rw [Iw_smul, Iw_pair12 hZ (fun _ c => paleyOp h₂ c ^ 2), norm_A1_sq hF h3 h7 h₂ hh₂]
  field_simp

theorem diag3 (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (k : F → ℝ)
    (hk : ∑ s, k s = 0) :
    Iw (fun _ b c => qF * A3op k b c ^ 2) / oldZ (F := F) ≤ unifNormSq k := by
  have hZ := (oldZ_pos hF h3 h7).ne'
  have h0 : 0 < qF := by linarith
  rw [Iw_smul, Iw_pair12 hZ (fun b c => A3op k b c ^ 2)]
  have := norm_A3_sq_le hF h3 h7 k hk
  rw [show qF * (oldZ (F := F) * ∑ b, ∑ c, m12 b c * A3op k b c ^ 2) / oldZ (F := F) =
    qF * ∑ b, ∑ c, m12 b c * A3op k b c ^ 2 by field_simp]
  calc qF * ∑ b, ∑ c, m12 b c * A3op k b c ^ 2 ≤ qF * (qF⁻¹ * unifNormSq k) :=
        mul_le_mul_of_nonneg_left this h0.le
    _ = unifNormSq k := by field_simp


/-! ## The expansion and the bound -/

/-- **The expansion of `‖V₀h₀ + (A₂h₁ + A₁h₂ + A₃h₃)/r‖²_{m₀}`** into its ten Gram terms. -/
theorem synth_expand (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₀ h₁ h₂ k : F → ℝ) :
    Iw (fun a b c => (h₀ a + Real.sqrt qF * paleyOp h₁ b + Real.sqrt qF * paleyOp h₂ c +
        Real.sqrt qF * A3op k b c) ^ 2) / oldZ (F := F) =
      Iw (fun a _ _ => h₀ a ^ 2) / oldZ (F := F) +
        Iw (fun _ b _ => qF * paleyOp h₁ b ^ 2) / oldZ (F := F) +
        Iw (fun _ _ c => qF * paleyOp h₂ c ^ 2) / oldZ (F := F) +
        Iw (fun _ b c => qF * A3op k b c ^ 2) / oldZ (F := F) +
        2 * Real.sqrt qF * ∑ a, ∑ b, m01 a b * h₀ a * paleyOp h₁ b +
        2 * Real.sqrt qF * ∑ a, ∑ b, m02 a b * h₀ a * paleyOp h₂ b +
        2 * Real.sqrt qF * (Iw (fun a b c => h₀ a * A3op k b c) / oldZ (F := F)) +
        2 * qF * ∑ a, ∑ b, m12 a b * paleyOp h₁ a * paleyOp h₂ b +
        2 * qF * ∑ a, ∑ b, m12 a b * paleyOp h₁ a * A3op k a b +
        2 * qF * ∑ a, ∑ b, m12 a b * paleyOp h₂ b * A3op k a b := by
  have hZ := (oldZ_pos hF h3 h7).ne'
  have h0 : 0 < qF := by linarith
  have hs : Real.sqrt qF ^ 2 = qF := Real.sq_sqrt h0.le
  have e : (fun a b c => (h₀ a + Real.sqrt qF * paleyOp h₁ b + Real.sqrt qF * paleyOp h₂ c +
      Real.sqrt qF * A3op k b c) ^ 2) = fun a b c =>
      h₀ a ^ 2 + qF * paleyOp h₁ b ^ 2 + qF * paleyOp h₂ c ^ 2 + qF * A3op k b c ^ 2 +
        (2 * Real.sqrt qF) * (h₀ a * paleyOp h₁ b) + (2 * Real.sqrt qF) * (h₀ a * paleyOp h₂ c) +
        (2 * Real.sqrt qF) * (h₀ a * A3op k b c) + (2 * qF) * (paleyOp h₁ b * paleyOp h₂ c) +
        (2 * qF) * (paleyOp h₁ b * A3op k b c) + (2 * qF) * (paleyOp h₂ c * A3op k b c) := by
    funext a b c
    linear_combination (paleyOp h₁ b ^ 2 + paleyOp h₂ c ^ 2 + A3op k b c ^ 2 +
      2 * paleyOp h₁ b * paleyOp h₂ c + 2 * paleyOp h₁ b * A3op k b c +
      2 * paleyOp h₂ c * A3op k b c) * hs
  rw [e]
  simp only [Iw_add, add_div]
  rw [Iw_smul (2 * Real.sqrt qF) (fun a b _ => h₀ a * paleyOp h₁ b),
    Iw_smul (2 * Real.sqrt qF) (fun a _ c => h₀ a * paleyOp h₂ c),
    Iw_smul (2 * Real.sqrt qF) (fun a b c => h₀ a * A3op k b c),
    Iw_smul (2 * qF) (fun _ b c => paleyOp h₁ b * paleyOp h₂ c),
    Iw_smul (2 * qF) (fun _ b c => paleyOp h₁ b * A3op k b c),
    Iw_smul (2 * qF) (fun _ b c => paleyOp h₂ c * A3op k b c),
    Iw_pair01 hZ (fun a b => h₀ a * paleyOp h₁ b),
    Iw_pair02 hZ (fun a c => h₀ a * paleyOp h₂ c),
    Iw_pair12 hZ (fun b c => paleyOp h₁ b * paleyOp h₂ c),
    Iw_pair12 hZ (fun b c => paleyOp h₁ b * A3op k b c),
    Iw_pair12 hZ (fun b c => paleyOp h₂ c * A3op k b c)]
  have e1 : ∀ (x : ℝ) (S : ℝ), x * (oldZ (F := F) * S) / oldZ (F := F) = x * S := by
    intro x S; field_simp
  rw [e1, e1, e1, e1, e1, mul_div_assoc]
  simp only [mul_assoc]


/-- **`lem:actual-features`(d), the synthesis bound**: for mean-zero `h₁, h₂, h₃` and any `h₀`,
`‖V₀h₀ + (A₂h₁ + A₁h₂ + A₃h₃)/r‖²_{m₀} ≤ Γ (‖h₀‖² + ‖h₁‖² + ‖h₂‖² + ‖h₃‖²)` with
`Γ = 1 + ϱ₀₂ + 2ϱ₀₁ + g₀₃ + 2g₁₃` (`1/r = √p`). -/
theorem synthesis_bound (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (h₀ h₁ h₂ k : F → ℝ) (hh₁ : ∑ s, h₁ s = 0) (hh₂ : ∑ s, h₂ s = 0) (hk : ∑ s, k s = 0) :
    Iw (fun a b c => (h₀ a + Real.sqrt qF * paleyOp h₁ b + Real.sqrt qF * paleyOp h₂ c +
        Real.sqrt qF * A3op k b c) ^ 2) / oldZ (F := F) ≤
      (1 + Real.sqrt (rho02sq (F := F)) + 2 * Real.sqrt (rho01sq (F := F)) + g03 (F := F) +
          2 * g13 (F := F)) *
        (unifNormSq h₀ + unifNormSq h₁ + unifNormSq h₂ + unifNormSq k) := by
  have h0 : 0 < qF := by linarith
  have h1 : 0 < qF - 1 := by linarith
  have h4 : 0 < qF - 4 := by linarith
  rw [synth_expand hF h3 h7, diag0 hF h3 h7, diag1 hF h3 h7 h₁ hh₁, diag2 hF h3 h7 h₂ hh₂]
  have d3 := diag3 hF h3 h7 k hk
  have c01 := (le_abs_self _).trans (cross01 hF h3 h7 h₀ h₁ hh₁)
  have c02 := (le_abs_self _).trans (cross02 hF h3 h7 h₀ h₂ hh₂)
  have c03 := (le_abs_self _).trans (cross03 hF h3 h7 h₀ k hk)
  have c12 := (le_abs_self _).trans (cross12 hF h3 h7 h₁ h₂ hh₁ hh₂)
  have c13 := (le_abs_self _).trans (cross13 hF h3 h7 h₁ k hh₁ hk)
  have c23 := (le_abs_self _).trans (cross23 hF h3 h7 h₂ k hh₂ hk)
  set u₀ := unifNormSq h₀
  set u₁ := unifNormSq h₁
  set u₂ := unifNormSq h₂
  set u₃ := unifNormSq k
  have hu₀ : 0 ≤ u₀ := unifNormSq_nonneg h₀
  have hu₁ : 0 ≤ u₁ := unifNormSq_nonneg h₁
  have hu₂ : 0 ≤ u₂ := unifNormSq_nonneg h₂
  have hu₃ : 0 ≤ u₃ := unifNormSq_nonneg k
  set n₀ := Real.sqrt u₀
  set n₁ := Real.sqrt u₁
  set n₂ := Real.sqrt u₂
  set n₃ := Real.sqrt u₃
  have sq₀ : n₀ ^ 2 = u₀ := Real.sq_sqrt hu₀
  have sq₁ : n₁ ^ 2 = u₁ := Real.sq_sqrt hu₁
  have sq₂ : n₂ ^ 2 = u₂ := Real.sq_sqrt hu₂
  have sq₃ : n₃ ^ 2 = u₃ := Real.sq_sqrt hu₃
  set ρ₁ := Real.sqrt (rho01sq (F := F))
  set ρ₂ := Real.sqrt (rho02sq (F := F))
  have hρ₁ : 0 ≤ ρ₁ := Real.sqrt_nonneg _
  have hρ₂ : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hg03 : 0 ≤ g03 (F := F) := by unfold g03; positivity
  have hg13 : 0 ≤ g13 (F := F) := by unfold g13; positivity
  -- AM–GM on each pair
  have amgm : ∀ {G x y : ℝ}, 0 ≤ G → 2 * G * (x * y) ≤ G * (x ^ 2 + y ^ 2) := by
    intro G x y hG
    nlinarith [mul_nonneg hG (sq_nonneg (x - y))]
  have a01 := amgm (x := n₀) (y := n₁) hρ₁
  have a02 := amgm (x := n₀) (y := n₂) hρ₂
  have a03 := amgm (x := n₀) (y := n₃) hg03
  have a12 := amgm (x := n₁) (y := n₂) hρ₁
  have a13 := amgm (x := n₁) (y := n₃) hg13
  have a23 := amgm (x := n₂) (y := n₃) hg13
  rw [sq₀, sq₁] at a01
  rw [sq₀, sq₂] at a02
  rw [sq₀, sq₃] at a03
  rw [sq₁, sq₂] at a12
  rw [sq₁, sq₃] at a13
  rw [sq₂, sq₃] at a23
  nlinarith [mul_nonneg hρ₂ hu₁, mul_nonneg hρ₁ hu₀, mul_nonneg hρ₁ hu₁, mul_nonneg hρ₁ hu₂,
    mul_nonneg hρ₁ hu₃, mul_nonneg hρ₂ hu₃, mul_nonneg hg03 hu₁, mul_nonneg hg03 hu₂,
    mul_nonneg hg13 hu₀, mul_nonneg hg13 hu₁, mul_nonneg hg13 hu₂, mul_nonneg hg13 hu₃,
    mul_nonneg hρ₂ hu₀, mul_nonneg hρ₂ hu₂, mul_nonneg hg03 hu₀, mul_nonneg hg03 hu₃]

/-! ## Comparison with the paper's `Γ_A` -/

/-- The paper's `Γ_A` as a function of `(q, r)`. -/
noncomputable def GammaA (q r : ℝ) : ℝ :=
  1 + r * Real.sqrt (1 + q) / (1 - q) +
    2 * (q / (1 - q) * Real.sqrt (1 + 4 * q / (1 - 4 * q) ^ 2)) +
    q * r * (1 + 4 * q) / ((1 - q) * (1 - 4 * q)) + 2 * q * r / (1 - q) +
    4 * q ^ 2 / ((1 - q) * (1 - 4 * q))

omit [DecidableEq F] in
/-- **`Γ ≤ Γ_A`** at `q = 1/p`, `r = √q`: the first three terms agree, `g₀₃` is the paper's
`qr(1 + 4q)/((1 - q)(1 - 4q))`, and `g₁₃ ≤ qr/(1 - q) + 2q²/((1 - q)(1 - 4q))`. -/
theorem gamma_le_GammaA (h7 : 7 ≤ qF) :
    1 + Real.sqrt (rho02sq (F := F)) + 2 * Real.sqrt (rho01sq (F := F)) + g03 (F := F) +
        2 * g13 (F := F) ≤ GammaA (1 / qF) (Real.sqrt (1 / qF)) := by
  have h0 : 0 < qF := by linarith
  have h1 : 0 < qF - 1 := by linarith
  have h4 : 0 < qF - 4 := by linarith
  set s := Real.sqrt qF with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr h0
  have hs2 : s ^ 2 = qF := Real.sq_sqrt h0.le
  have hr : Real.sqrt (1 / qF) = 1 / s := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  have hq1 : 0 < 1 - 1 / qF := by
    rw [sub_pos, div_lt_one h0]; linarith
  have hq4 : 0 < 1 - 4 * (1 / qF) := by
    rw [sub_pos, mul_one_div, div_lt_one h0]; linarith
  -- the `ϱ₀₂` term
  have e02 : Real.sqrt (rho02sq (F := F)) = Real.sqrt (1 / qF) * Real.sqrt (1 + 1 / qF) /
      (1 - 1 / qF) := by
    unfold rho02sq
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hq1.le]
  -- the `ϱ₀₁` term
  have e01 : Real.sqrt (rho01sq (F := F)) =
      1 / qF / (1 - 1 / qF) * Real.sqrt (1 + 4 * (1 / qF) / (1 - 4 * (1 / qF)) ^ 2) := by
    unfold rho01sq
    rw [rho01_sq_eq h7, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- the `g₀₃` term
  have e03 : g03 (F := F) = 1 / qF * Real.sqrt (1 / qF) * (1 + 4 * (1 / qF)) /
      ((1 - 1 / qF) * (1 - 4 * (1 / qF))) := by
    unfold g03
    rw [hr, ← hs_def]
    field_simp
    exact hs2
  -- the `g₁₃` term
  have h13 : g13 (F := F) ≤ 1 / qF * Real.sqrt (1 / qF) / (1 - 1 / qF) +
      2 * (1 / qF) ^ 2 / ((1 - 1 / qF) * (1 - 4 * (1 / qF))) := by
    unfold g13
    have hmu : 0 ≤ muF (F := F) := by unfold muF; positivity
    have hsq : Real.sqrt (1 + muF (F := F) ^ 2 * qF) ≤ 1 + muF (F := F) * s := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [mul_nonneg hmu hs.le]
    have hden : 0 < qF * (qF - 1) := by positivity
    calc Real.sqrt (1 + muF (F := F) ^ 2 * qF) * Real.sqrt qF / (qF * (qF - 1))
        ≤ (1 + muF (F := F) * s) * s / (qF * (qF - 1)) := by
          rw [← hs_def]
          gcongr
      _ = _ := by
          rw [hr]
          unfold muF
          field_simp
          rw [← hs2]
  unfold GammaA
  rw [e02, e01, e03]
  have hsplit : 2 * (1 / qF) * Real.sqrt (1 / qF) / (1 - 1 / qF) +
      4 * (1 / qF) ^ 2 / ((1 - 1 / qF) * (1 - 4 * (1 / qF))) =
      2 * (1 / qF * Real.sqrt (1 / qF) / (1 - 1 / qF) +
        2 * (1 / qF) ^ 2 / ((1 - 1 / qF) * (1 - 4 * (1 / qF)))) := by ring
  linarith [h13, hsplit]

end Sarkozy.MiddleRecords
