module

public import Sarkozy.MiddleRecords.Mirror

/-!
# Rectangular stars (`lem:record:projected-nonstar`(b), first part)

`paper/sections/21_middle_records.tex`, `subsec:record:f_remainders`,
`lem:record:projected-nonstar`(b). For independent uniform labels `z, u, v` and real
`a₁, a₂, a₃`, the rectangular star `k = a₁ χ(u - z) + a₂ χ(v - z) + a₃ χ(u - z) χ(v - z)`
(`rectStar`, from `Sarkozy.MiddleRecords.Mirror`) acts from functions of `z` to functions of
`(u, v)` by `(T g)(u, v) = E_z k(z, u, v) g(z)` (`rectOp`). Its Gram kernel is
`E_{u,v} k(z, ·) k(z', ·) = (a₁² + a₂²)(δ - q) + a₃² (δ - q)²`, `δ = [z = z']`
(`sum_uv_rect`); hence (`rect_gram`)
`‖T g‖² = q (a₁² + a₂² + a₃² - 2q a₃²) ‖g‖²` on mean-zero `g` (`rect_gram_meanZero`),
`‖T g‖² = a₃² q (1 - q) ‖g‖²` on the constants (`rect_gram_const`), and
`‖T g‖² ≤ q (a₁² + a₂² + a₃²) ‖g‖²` for every `g` (`rect_norm_le`): the norm is at most
`r (a₁² + a₂² + a₃²)^{1/2}`. Norms are those of the uniform laws (`E_z`, `E_{u,v}`). This
holds over any finite field of odd characteristic.

With `a₁ = a₂ = 0`, `a₃ = 1` and `(u, v) = (x₁, x₀)` the operator is the pair-star map `𝒯_E`
of `lem:record:e-orthogonal`(a) for independent labels: its Gram on mean-zero functions is
`q(1 - 2q)` (`pairStar_gram_meanZero`), the paper's "exactly `(q(1 - 2q))^{1/2}`".

The density factor `1/(1 - q)` of `lem:record:e-orthogonal`(a) is in
`Sarkozy.MiddleRecords.EOrthogonal` (`TE_norm_le`). **Not formalized:** the product of two
rectangular stars on disjoint labels, the restriction to `H_F × H_F` (the factor `2/Z` of
`lem:record:projection`), and part (a) of `lem:record:projected-nonstar`.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

theorem sumR_chi_shift (hF : ringChar F ≠ 2) (z : F) : ∑ u, (χ (u - z) : ℝ) = 0 := by
  have := sum_chi_shift hF z
  exact_mod_cast this

/-- `S(z, z') = ∑_t χ(t - z) χ(t - z') = p [z = z'] - 1`. -/
theorem sumR_chi_chi (hF : ringChar F ≠ 2) (z z' : F) :
    ∑ t, (χ (t - z) : ℝ) * (χ (t - z') : ℝ) = qF * (if z = z' then 1 else 0) - 1 := by
  have h := sum_chi_mul_chi hF z z'
  have e : ∑ t, (χ (t - z) : ℝ) * (χ (t - z') : ℝ) = ((∑ t, χ (t - z) * χ (t - z') : ℤ) : ℝ) := by
    push_cast; rfl
  rw [e, h]
  split_ifs <;> push_cast <;> ring

/-- **The `v`-sum** of a product of two rectangular stars with the same `u`. -/
theorem sum_v_rect (hF : ringChar F ≠ 2) (a₁ a₂ a₃ : ℝ) (z z' u : F) :
    ∑ v, rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v =
      qF * a₁ ^ 2 * ((χ (u - z) : ℝ) * (χ (u - z') : ℝ)) +
        (a₂ + a₃ * (χ (u - z) : ℝ)) * (a₂ + a₃ * (χ (u - z') : ℝ)) *
          (qF * (if z = z' then 1 else 0) - 1) := by
  set X : ℝ := (χ (u - z) : ℝ)
  set X' : ℝ := (χ (u - z') : ℝ)
  have e : ∀ v, rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v =
      a₁ ^ 2 * (X * X') + a₁ * X * (a₂ + a₃ * X') * (χ (v - z') : ℝ) +
        a₁ * X' * (a₂ + a₃ * X) * (χ (v - z) : ℝ) +
        (a₂ + a₃ * X) * (a₂ + a₃ * X') * ((χ (v - z) : ℝ) * (χ (v - z') : ℝ)) := by
    intro v; unfold rectStar; ring
  rw [sum_congr rfl fun v _ => e v, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have s0 : ∑ _v : F, a₁ ^ 2 * (X * X') = qF * (a₁ ^ 2 * (X * X')) := by
    rw [sum_const, card_univ, nsmul_eq_mul]
  have s1 : ∑ v : F, a₁ * X * (a₂ + a₃ * X') * (χ (v - z') : ℝ) = 0 := by
    rw [← mul_sum, sumR_chi_shift hF, mul_zero]
  have s2 : ∑ v : F, a₁ * X' * (a₂ + a₃ * X) * (χ (v - z) : ℝ) = 0 := by
    rw [← mul_sum, sumR_chi_shift hF, mul_zero]
  have s3 : ∑ v : F, (a₂ + a₃ * X) * (a₂ + a₃ * X') * ((χ (v - z) : ℝ) * (χ (v - z') : ℝ)) =
      (a₂ + a₃ * X) * (a₂ + a₃ * X') * (qF * (if z = z' then 1 else 0) - 1) := by
    rw [← mul_sum, sumR_chi_chi hF]
  rw [s0, s1, s2, s3]
  ring

/-- **The Gram kernel of a rectangular star**:
`∑_{u,v} k(z, u, v) k(z', u, v) = p (a₁² + a₂²) S + a₃² S²`, `S = p [z = z'] - 1`. -/
theorem sum_uv_rect (hF : ringChar F ≠ 2) (a₁ a₂ a₃ : ℝ) (z z' : F) :
    ∑ u, ∑ v, rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v =
      qF * (a₁ ^ 2 + a₂ ^ 2) * (qF * (if z = z' then 1 else 0) - 1) +
        a₃ ^ 2 * (qF * (if z = z' then 1 else 0) - 1) ^ 2 := by
  simp only [sum_v_rect hF]
  set S : ℝ := qF * (if z = z' then 1 else 0) - 1 with hS
  have e : ∀ u, qF * a₁ ^ 2 * ((χ (u - z) : ℝ) * (χ (u - z') : ℝ)) +
      (a₂ + a₃ * (χ (u - z) : ℝ)) * (a₂ + a₃ * (χ (u - z') : ℝ)) * S =
      a₂ ^ 2 * S + a₂ * a₃ * S * (χ (u - z) : ℝ) + a₂ * a₃ * S * (χ (u - z') : ℝ) +
        (qF * a₁ ^ 2 + a₃ ^ 2 * S) * ((χ (u - z) : ℝ) * (χ (u - z') : ℝ)) := by
    intro u; ring
  rw [sum_congr rfl fun u _ => e u, sum_add_distrib, sum_add_distrib, sum_add_distrib]
  have s0 : ∑ _u : F, a₂ ^ 2 * S = qF * (a₂ ^ 2 * S) := by
    rw [sum_const, card_univ, nsmul_eq_mul]
  have s1 : ∑ u : F, a₂ * a₃ * S * (χ (u - z) : ℝ) = 0 := by
    rw [← mul_sum, sumR_chi_shift hF, mul_zero]
  have s2 : ∑ u : F, a₂ * a₃ * S * (χ (u - z') : ℝ) = 0 := by
    rw [← mul_sum, sumR_chi_shift hF, mul_zero]
  have s3 : ∑ u : F, (qF * a₁ ^ 2 + a₃ ^ 2 * S) * ((χ (u - z) : ℝ) * (χ (u - z') : ℝ)) =
      (qF * a₁ ^ 2 + a₃ ^ 2 * S) * S := by
    rw [← mul_sum, sumR_chi_chi hF, ← hS]
  rw [s0, s1, s2, s3]
  ring

/-- **The counting Gram identity** of a rectangular star:
`∑_{u,v} (∑_z k(z, u, v) g(z))² =
((a₁² + a₂²) p² + a₃² (p² - 2p)) ∑ g² + (a₃² - (a₁² + a₂²) p) (∑ g)²`. -/
theorem rect_gram (hF : ringChar F ≠ 2) (a₁ a₂ a₃ : ℝ) (g : F → ℝ) :
    ∑ u, ∑ v, (∑ z, rectStar a₁ a₂ a₃ z u v * g z) ^ 2 =
      ((a₁ ^ 2 + a₂ ^ 2) * qF ^ 2 + a₃ ^ 2 * (qF ^ 2 - 2 * qF)) * ∑ z, g z ^ 2 +
        (a₃ ^ 2 - (a₁ ^ 2 + a₂ ^ 2) * qF) * (∑ z, g z) ^ 2 := by
  have hsq : ∀ u v, (∑ z, rectStar a₁ a₂ a₃ z u v * g z) ^ 2 =
      ∑ z, ∑ z', g z * g z' * (rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v) := by
    intro u v
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun z _ => sum_congr rfl fun z' _ => by ring
  simp only [hsq]
  -- bring `z, z'` outside
  have hswap : ∑ u, ∑ v, ∑ z, ∑ z', g z * g z' *
      (rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v) =
      ∑ z, ∑ z', g z * g z' * ∑ u, ∑ v, rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v := by
    calc ∑ u, ∑ v, ∑ z, ∑ z', g z * g z' *
          (rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v)
        = ∑ u, ∑ z, ∑ z', ∑ v, g z * g z' *
          (rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v) :=
          sum_congr rfl fun u _ => by
            rw [sum_comm]; exact sum_congr rfl fun z _ => by rw [sum_comm]
      _ = ∑ z, ∑ z', ∑ u, ∑ v, g z * g z' *
          (rectStar a₁ a₂ a₃ z u v * rectStar a₁ a₂ a₃ z' u v) := by
          rw [sum_comm]; exact sum_congr rfl fun z _ => by rw [sum_comm]
      _ = _ := sum_congr rfl fun z _ => sum_congr rfl fun z' _ => by
          rw [mul_sum]; exact sum_congr rfl fun u _ => by rw [mul_sum]
  rw [hswap]
  simp only [sum_uv_rect hF]
  have e : ∀ z z' : F, g z * g z' * (qF * (a₁ ^ 2 + a₂ ^ 2) * (qF * (if z = z' then 1 else 0) - 1)
      + a₃ ^ 2 * (qF * (if z = z' then 1 else 0) - 1) ^ 2) =
      ((a₁ ^ 2 + a₂ ^ 2) * qF ^ 2 + a₃ ^ 2 * (qF ^ 2 - 2 * qF)) *
          (g z * g z' * (if z = z' then 1 else 0)) +
        (a₃ ^ 2 - (a₁ ^ 2 + a₂ ^ 2) * qF) * (g z * g z') := by
    intro z z'
    split_ifs <;> ring
  simp only [e, sum_add_distrib, ← mul_sum]
  have hdiag : ∑ z, ∑ z', g z * g z' * (if z = z' then (1 : ℝ) else 0) = ∑ z, g z ^ 2 := by
    refine sum_congr rfl fun z _ => ?_
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
    ring
  rw [hdiag, ← sum_mul]
  ring

/-- The operator `(T g)(u, v) = E_z k(z, u, v) g(z)`. -/
noncomputable def rectOp (a₁ a₂ a₃ : ℝ) (g : F → ℝ) (u v : F) : ℝ :=
  qF⁻¹ * ∑ z, rectStar a₁ a₂ a₃ z u v * g z

/-- The squared norm `E_{u,v} (T g)²` in the uniform law of `(u, v)`. -/
noncomputable def rectNormSq (a₁ a₂ a₃ : ℝ) (g : F → ℝ) : ℝ :=
  qF⁻¹ ^ 2 * ∑ u, ∑ v, rectOp a₁ a₂ a₃ g u v ^ 2

/-- The squared norm `E_z g²`. -/
noncomputable def unifNormSq (g : F → ℝ) : ℝ := qF⁻¹ * ∑ z, g z ^ 2

theorem rectNormSq_eq (hF : ringChar F ≠ 2) (a₁ a₂ a₃ : ℝ) (g : F → ℝ) :
    rectNormSq a₁ a₂ a₃ g = qF⁻¹ ^ 4 *
      (((a₁ ^ 2 + a₂ ^ 2) * qF ^ 2 + a₃ ^ 2 * (qF ^ 2 - 2 * qF)) * ∑ z, g z ^ 2 +
        (a₃ ^ 2 - (a₁ ^ 2 + a₂ ^ 2) * qF) * (∑ z, g z) ^ 2) := by
  unfold rectNormSq rectOp
  simp only [mul_pow, ← mul_sum]
  rw [rect_gram hF]
  ring

/-- **`lem:record:projected-nonstar`(b): the Gram on mean-zero functions** is
`q (a₁² + a₂² + a₃² - 2q a₃²)`, `q = 1/p`. -/
theorem rect_gram_meanZero (hF : ringChar F ≠ 2) (a₁ a₂ a₃ : ℝ) (g : F → ℝ)
    (hg : ∑ z, g z = 0) :
    rectNormSq a₁ a₂ a₃ g = qF⁻¹ * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 - 2 * qF⁻¹ * a₃ ^ 2) *
      unifNormSq g := by
  rw [rectNormSq_eq hF, hg, unifNormSq]
  have h0 : qF ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  field_simp
  ring

/-- **`lem:record:projected-nonstar`(b): the Gram on the constants** is `a₃² q (1 - q)`. -/
theorem rect_gram_const (hF : ringChar F ≠ 2) (a₁ a₂ a₃ c : ℝ) :
    rectNormSq a₁ a₂ a₃ (fun _ : F => c) = a₃ ^ 2 * qF⁻¹ * (1 - qF⁻¹) *
      unifNormSq (fun _ : F => c) := by
  rw [rectNormSq_eq hF, unifNormSq]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  have h0 : qF ≠ 0 := by
    have := Fintype.card_pos (α := F)
    positivity
  field_simp
  ring

/-- **`lem:record:projected-nonstar`(b): the norm bound** `‖T g‖² ≤ q (a₁² + a₂² + a₃²) ‖g‖²`
for every `g`, i.e. `‖T‖ ≤ r (a₁² + a₂² + a₃²)^{1/2}`. -/
theorem rect_norm_le (hF : ringChar F ≠ 2) (a₁ a₂ a₃ : ℝ) (g : F → ℝ) :
    rectNormSq a₁ a₂ a₃ g ≤ qF⁻¹ * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * unifNormSq g := by
  rw [rectNormSq_eq hF, unifNormSq]
  have hp : (1 : ℝ) ≤ qF := by exact_mod_cast Fintype.card_pos (α := F)
  have hp0 : 0 < qF := by linarith
  -- Cauchy–Schwarz: `(∑ g)² ≤ p ∑ g²`
  have hcs : (∑ z, g z) ^ 2 ≤ qF * ∑ z, g z ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset F)) (f := g)
    simpa [card_univ] using this
  have hG : 0 ≤ ∑ z, g z ^ 2 := sum_nonneg fun z _ => sq_nonneg _
  have hS0 : 0 ≤ (∑ z, g z) ^ 2 := sq_nonneg _
  have hq4 : 0 < qF⁻¹ ^ 4 := by positivity
  -- the bracket is at most `(a₁² + a₂² + a₃²) p² ∑ g²`
  have hbr : ((a₁ ^ 2 + a₂ ^ 2) * qF ^ 2 + a₃ ^ 2 * (qF ^ 2 - 2 * qF)) * ∑ z, g z ^ 2 +
      (a₃ ^ 2 - (a₁ ^ 2 + a₂ ^ 2) * qF) * (∑ z, g z) ^ 2 ≤
      (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * qF ^ 2 * ∑ z, g z ^ 2 := by
    have h1 : (a₃ ^ 2 - (a₁ ^ 2 + a₂ ^ 2) * qF) * (∑ z, g z) ^ 2 ≤ a₃ ^ 2 * (∑ z, g z) ^ 2 := by
      have : 0 ≤ (a₁ ^ 2 + a₂ ^ 2) * qF * (∑ z, g z) ^ 2 := by positivity
      nlinarith
    have h2 : a₃ ^ 2 * (∑ z, g z) ^ 2 ≤ a₃ ^ 2 * (qF * ∑ z, g z ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    have h3 : 0 ≤ a₃ ^ 2 * qF * ∑ z, g z ^ 2 := by positivity
    nlinarith
  calc qF⁻¹ ^ 4 * (((a₁ ^ 2 + a₂ ^ 2) * qF ^ 2 + a₃ ^ 2 * (qF ^ 2 - 2 * qF)) * ∑ z, g z ^ 2 +
        (a₃ ^ 2 - (a₁ ^ 2 + a₂ ^ 2) * qF) * (∑ z, g z) ^ 2)
      ≤ qF⁻¹ ^ 4 * ((a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * qF ^ 2 * ∑ z, g z ^ 2) :=
        mul_le_mul_of_nonneg_left hbr hq4.le
    _ = qF⁻¹ * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * (qF⁻¹ * ∑ z, g z ^ 2) := by
        field_simp

/-- **`lem:record:e-orthogonal`(a), independent labels**: the pair-star map
`𝒯_E g(x) = E_t χ(t - x₁) χ(t - x₀) g(t)` is the rectangular star `(0, 0, 1)` with centre `t`
and leaves `(x₁, x₀)`; on mean-zero functions its Gram is `q(1 - 2q)`. -/
theorem pairStar_gram_meanZero (hF : ringChar F ≠ 2) (g : F → ℝ) (hg : ∑ z, g z = 0) :
    rectNormSq 0 0 1 g = qF⁻¹ * (1 - 2 * qF⁻¹) * unifNormSq g := by
  rw [rect_gram_meanZero hF 0 0 1 g hg]
  ring

/-- The kernel of `𝒯_E` is the rectangular star `(0, 0, 1)`: `χ(t - x₁) χ(t - x₀)`. -/
theorem rectStar_pairStar (h3 : Fintype.card F % 4 = 3) (t x₁ x₀ : F) :
    rectStar 0 0 1 t x₁ x₀ = (χ (t - x₁) : ℝ) * (χ (t - x₀) : ℝ) := by
  unfold rectStar
  rw [chi_swap h3 t x₁, chi_swap h3 t x₀]
  push_cast
  ring

end Sarkozy.MiddleRecords
