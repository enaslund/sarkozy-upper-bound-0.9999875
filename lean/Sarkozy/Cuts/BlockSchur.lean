module

public import Sarkozy.Cuts.Envelope

/-!
# Cuts, VII″: the Schur complement (`lem:block-completion` (a))

`13_cuts_correlations.tex`, `lem:block-completion` (a). Let `T = [[A, B*], [B, D]]` on
`H₁ ⊕ H₂` (real inner product spaces). `T` enters through its quadratic form
`⟨(x, y), T(x, y)⟩ = ⟨x, Ax⟩ + 2⟨y, Bx⟩ + ⟨y, Dy⟩` (`blockQ`). The data are:
* `A` self-adjoint, with a right inverse `A⁻¹` (which exists when `A ⪰ sI`, `s > 0`, on a
  finite-dimensional space);
* `B*` the adjoint of `B`.

Writing `u = A⁻¹B*y`, the identity `‖A^{1/2}x + A^{-1/2}B*y‖² = ⟨x + u, A(x + u)⟩` removes the
square roots.

* `block_schur_identity`: `⟨(x,y), T(x,y)⟩ = ⟨x + u, A(x + u)⟩ + ⟨y, (D - BA⁻¹B*) y⟩`.
* `block_nonneg_iff`: `T ⪰ 0` iff `D - BA⁻¹B* ⪰ 0` (for `A ⪰ 0`).
* `schur_complement_ge`: `D - BA⁻¹B* ⪰ D - (b²/s) I` for `A ⪰ sI` and `‖B‖ ≤ b` (`b ≥ 0`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- The quadratic form `⟨(x, y), T(x, y)⟩` of `T = [[A, B*], [B, D]]`. -/
noncomputable def blockQ (A : E₁ →ₗ[ℝ] E₁) (B : E₁ →ₗ[ℝ] E₂) (D : E₂ →ₗ[ℝ] E₂) (x : E₁)
    (y : E₂) : ℝ :=
  inner ℝ x (A x) + 2 * inner ℝ y (B x) + inner ℝ y (D y)

/-- **`lem:block-completion` (a), the identity.** With `u = A⁻¹B*y`,
`⟨(x,y), T(x,y)⟩ = ⟨x + u, A(x + u)⟩ + ⟨y, (D - BA⁻¹B*) y⟩`. -/
theorem block_schur_identity (A Ainv : E₁ →ₗ[ℝ] E₁) (B : E₁ →ₗ[ℝ] E₂) (Bstar : E₂ →ₗ[ℝ] E₁)
    (D : E₂ →ₗ[ℝ] E₂) (hA : ∀ x x', inner ℝ x (A x') = inner ℝ (A x) x')
    (hAinv : ∀ x, A (Ainv x) = x) (hB : ∀ x y, inner ℝ y (B x) = inner ℝ (Bstar y) x)
    (x : E₁) (y : E₂) :
    blockQ A B D x y = inner ℝ (x + Ainv (Bstar y)) (A (x + Ainv (Bstar y))) +
      (inner ℝ y (D y) - inner ℝ y (B (Ainv (Bstar y)))) := by
  unfold blockQ
  set u := Ainv (Bstar y) with hu
  have hAu : A u = Bstar y := hAinv _
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hAu, hB u y, hB x y,
    hA u x, hAu, real_inner_comm u (Bstar y), real_inner_comm (Bstar y) x]
  ring

/-- **`lem:block-completion` (a).** If `A ⪰ 0`, then `T ⪰ 0` iff `D - BA⁻¹B* ⪰ 0`. -/
theorem block_nonneg_iff (A Ainv : E₁ →ₗ[ℝ] E₁) (B : E₁ →ₗ[ℝ] E₂) (Bstar : E₂ →ₗ[ℝ] E₁)
    (D : E₂ →ₗ[ℝ] E₂) (hA : ∀ x x', inner ℝ x (A x') = inner ℝ (A x) x')
    (hAinv : ∀ x, A (Ainv x) = x) (hB : ∀ x y, inner ℝ y (B x) = inner ℝ (Bstar y) x)
    (hA0 : ∀ x, 0 ≤ inner ℝ x (A x)) :
    (∀ x y, 0 ≤ blockQ A B D x y) ↔
      ∀ y, 0 ≤ inner ℝ y (D y) - inner ℝ y (B (Ainv (Bstar y))) := by
  constructor
  · intro h y
    have := h (-Ainv (Bstar y)) y
    rw [block_schur_identity A Ainv B Bstar D hA hAinv hB, neg_add_cancel, map_zero,
      inner_zero_left, zero_add] at this
    exact this
  · intro h x y
    rw [block_schur_identity A Ainv B Bstar D hA hAinv hB]
    exact add_nonneg (hA0 _) (h y)

/-- **`lem:block-completion` (a).** If `A ⪰ sI` with `s > 0` and `‖B‖ ≤ b`, then
`D - BA⁻¹B* ⪰ D - (b²/s) I`. -/
theorem schur_complement_ge (A Ainv : E₁ →ₗ[ℝ] E₁) (B : E₁ →ₗ[ℝ] E₂) (Bstar : E₂ →ₗ[ℝ] E₁)
    (D : E₂ →ₗ[ℝ] E₂) (hAinv : ∀ x, A (Ainv x) = x)
    (hB : ∀ x y, inner ℝ y (B x) = inner ℝ (Bstar y) x) {s b : ℝ} (hs : 0 < s) (hb : 0 ≤ b)
    (hAs : ∀ x, s * ‖x‖ ^ 2 ≤ inner ℝ x (A x)) (hBn : ∀ x, ‖B x‖ ≤ b * ‖x‖) (y : E₂) :
    inner ℝ y (D y) - b ^ 2 / s * ‖y‖ ^ 2 ≤ inner ℝ y (D y) - inner ℝ y (B (Ainv (Bstar y))) := by
  -- `‖B* y‖ ≤ b ‖y‖`
  have hBs : ‖Bstar y‖ ≤ b * ‖y‖ := by
    have h1 : ‖Bstar y‖ ^ 2 = inner ℝ y (B (Bstar y)) := by
      rw [hB, real_inner_self_eq_norm_sq]
    have h2 : inner ℝ y (B (Bstar y)) ≤ ‖y‖ * (b * ‖Bstar y‖) :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hBn _) (norm_nonneg _))
    have h0 := norm_nonneg (Bstar y)
    have hy0 := norm_nonneg y
    by_contra hlt
    push Not at hlt
    have hb0 : 0 ≤ b * ‖y‖ := mul_nonneg hb hy0
    have hpos : 0 < ‖Bstar y‖ := lt_of_le_of_lt hb0 hlt
    have := mul_lt_mul_of_pos_left hlt hpos
    nlinarith
  -- `⟨z, A⁻¹ z⟩ ≤ ‖z‖²/s`
  set z := Bstar y
  set w := Ainv z
  have hAw : A w = z := hAinv z
  have hw : s * ‖w‖ ^ 2 ≤ inner ℝ z w := by
    have := hAs w
    rw [hAw, real_inner_comm] at this
    exact this
  have hzw : inner ℝ z w ≤ ‖z‖ * ‖w‖ := real_inner_le_norm _ _
  have hw0 := norm_nonneg w
  have hz0 := norm_nonneg z
  have hwn : ‖w‖ ≤ ‖z‖ / s := by
    rw [le_div_iff₀ hs]
    rcases hw0.lt_or_eq with hpos | h0
    · have h := hw.trans hzw
      nlinarith
    · rw [← h0, zero_mul]
      exact hz0
  have hkey : inner ℝ y (B w) ≤ b ^ 2 / s * ‖y‖ ^ 2 := by
    rw [hB]
    calc inner ℝ z w ≤ ‖z‖ * ‖w‖ := hzw
      _ ≤ ‖z‖ * (‖z‖ / s) := mul_le_mul_of_nonneg_left hwn hz0
      _ = ‖z‖ ^ 2 / s := by ring
      _ ≤ (b * ‖y‖) ^ 2 / s := by
          apply div_le_div_of_nonneg_right _ hs.le
          exact pow_le_pow_left₀ hz0 hBs 2
      _ = b ^ 2 / s * ‖y‖ ^ 2 := by ring
  linarith

end Sarkozy.Cuts
