module

public import Sarkozy.Spectral.RouteB
public import Mathlib.Algebra.BigOperators.Field

/-!
# `cor:spec2:coupling`: the coupling bound `eq:spec:coupling`

`paper/sections/14_spectral.tex`, `cor:spec2:coupling`, the second display (`eq:spec:coupling`),
in abstract form: the Hilbert-space argument of its proof (Step 1, Step 2 and the conclusion).

The cut operator `Op` is an abstract operator `T` on a finite-dimensional inner product space
`H`, `V` is the degree-one space and `F = F_V`, with Fourier coefficients `ĝ(ξ)` on a set `s` of
modes. The inputs:
* Step 1 (`lem:coupling-modes` and the first display of the lemma):
  `‖Op F_V‖² ≤ r² κ ∑_ξ ĝ^*(𝐇⁺ + e I) ĝ` with `κ = R₊ p/(p-1) ≥ 1`,
  `e = ε_H + ε_≠ + ε_rem + ε_par`, and `𝐇⁺ ⪯ Λ₊ I`;
* Step 2 (`lem:spec:degone` (a), (c)): a `v ∈ 𝒱` (coefficients `𝐐(ξ) ĝ(ξ)`) with
  `⟪v, Op F_V⟫ = ∑_ξ |𝐐 ĝ|²` and `‖v‖² ≤ (1 + ε_V) ∑_ξ |𝐐 ĝ|²`;
* (`lem:spec:degone` (b)): `|𝐐 ĝ|² ≥ r² (|A ĝ|² - 2 Λ_D η_Q |ĝ|²)` and `|A ĝ| ≤ Λ_D |ĝ|`.

The first display, `𝐌(ξ) ⪯ (H̃ + [p ≡ 1]𝐇^cov + (ε_≠ + ε_rem + ε_par) I)/(p - 1) ⪯ Λ_M/(p - 1)`, is
`coupling_M_bound` (for one vector, from the cited bounds).

Conclusion (`coupling_block`): `‖(I - Π_𝒱) Op F_V‖² ≤ r² ∑_ξ ĝ^*(𝐇⁺ - A^*A + η_B I) ĝ` with
`η_B = (κ - 1) Λ₊ + κ e + ε_V Λ_D² + 2 Λ_D η_Q` (`eq:spec:etaB`). This is the norm bound of the
field `coupling` of `Sarkozy.Spectral.RouteAInputs` (with `qX ξ x = x^*𝐇⁺x - |A(ξ) x|²`).
-/

@[expose] public section

open scoped InnerProductSpace Matrix
open RCLike

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] {Ξ : Type*}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

omit [Fintype n] in
/-- `x^*(𝐇⁺ - A^*A) x = x^*𝐇⁺x - |A x|²`: the form `qX` of `RouteAInputs` in terms of the
conclusion of `coupling_block`. -/
theorem qform_sub_conjTranspose_mul [Fintype n] (Hp A : Matrix n n 𝕜) (x : n → 𝕜) :
    qform (Hp - Aᴴ * A) x x = qform Hp x x - sqn (A *ᵥ x) := by
  have e : star x ⬝ᵥ (Aᴴ *ᵥ (A *ᵥ x)) = star (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  unfold qform
  rw [Matrix.sub_mulVec, dotProduct_sub, map_sub, ← Matrix.mulVec_mulVec, e,
    re_star_dotProduct_self]

/-- **`cor:spec2:coupling`, `eq:spec:coupling`**, abstract form. -/
theorem coupling_block [FiniteDimensional 𝕜 H] (T : H →ₗ[𝕜] H) (V : Submodule 𝕜 H) (F : H)
    (s : Finset Ξ) (g : Ξ → n → 𝕜) (Hp : Matrix n n 𝕜) (A Qm : Ξ → Matrix n n 𝕜)
    {r κ e Λp Λ ηQ εV : ℝ} (hκ : 1 ≤ κ) (hΛp : ∀ x, qform Hp x x ≤ Λp * sqn x)
    (hstep1 : ‖T F‖ ^ 2 ≤ r ^ 2 * (κ * ∑ ξ ∈ s, (qform Hp (g ξ) (g ξ) + e * sqn (g ξ))))
    (v : H) (hv : v ∈ V) (hvT : ⟪v, T F⟫ = ((∑ ξ ∈ s, sqn (Qm ξ *ᵥ g ξ) : ℝ) : 𝕜))
    (hvnorm : ‖v‖ ^ 2 ≤ (1 + εV) * ∑ ξ ∈ s, sqn (Qm ξ *ᵥ g ξ))
    (hQ : ∀ ξ ∈ s, r ^ 2 * (sqn (A ξ *ᵥ g ξ) - 2 * Λ * ηQ * sqn (g ξ)) ≤ sqn (Qm ξ *ᵥ g ξ))
    (hA : ∀ ξ ∈ s, sqn (A ξ *ᵥ g ξ) ≤ Λ ^ 2 * sqn (g ξ))
    (hεV : 0 ≤ εV) (hΛ : 0 ≤ Λ) (hηQ : 0 ≤ ηQ) :
    ‖T F - V.starProjection (T F)‖ ^ 2 ≤
      r ^ 2 * ∑ ξ ∈ s, (qform Hp (g ξ) (g ξ) - sqn (A ξ *ᵥ g ξ) +
        ((κ - 1) * Λp + κ * e + εV * Λ ^ 2 + 2 * Λ * ηQ) * sqn (g ξ)) := by
  set x := T F with hx
  set P := V.starProjection x with hP
  set S := ∑ ξ ∈ s, sqn (Qm ξ *ᵥ g ξ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun ξ _ => sqn_nonneg _
  -- Pythagoras
  have hpy : ‖x‖ ^ 2 = ‖P‖ ^ 2 + ‖x - P‖ ^ 2 := by
    have h0 : ⟪P, x - P⟫ = 0 := by
      rw [inner_eq_zero_symm]
      exact Submodule.starProjection_inner_eq_zero x P (V.starProjection_apply_mem x)
    have h := norm_add_sq (𝕜 := 𝕜) P (x - P)
    rw [h0, map_zero, mul_zero, add_zero, add_sub_cancel] at h
    exact h
  -- Step 2: the projection onto `𝒱` is large
  have hproj : S / (1 + εV) ≤ ‖P‖ ^ 2 := by
    have h1 : ⟪v, x⟫ = ⟪v, P⟫ := by
      have h := Submodule.starProjection_inner_eq_zero x v hv
      rw [inner_eq_zero_symm, inner_sub_right, sub_eq_zero] at h
      exact h
    have h2 : S ≤ ‖v‖ * ‖P‖ := by
      have h := norm_inner_le_norm (𝕜 := 𝕜) v P
      rw [← h1, hx, hvT, RCLike.norm_ofReal, abs_of_nonneg hS0] at h
      exact h
    have h3 : S ^ 2 ≤ (1 + εV) * S * ‖P‖ ^ 2 := by
      have h := pow_le_pow_left₀ hS0 h2 2
      rw [mul_pow] at h
      exact h.trans (mul_le_mul_of_nonneg_right hvnorm (sq_nonneg _))
    rcases hS0.eq_or_lt with h | h
    · rw [← h, zero_div]
      positivity
    · rw [div_le_iff₀ (by linarith)]
      nlinarith
  -- the conclusion, per mode
  have hmode : ∀ ξ ∈ s, r ^ 2 * (sqn (A ξ *ᵥ g ξ) - (2 * Λ * ηQ + εV * Λ ^ 2) * sqn (g ξ)) ≤
      sqn (Qm ξ *ᵥ g ξ) / (1 + εV) := by
    intro ξ hξ
    have hG0 : 0 ≤ sqn (g ξ) := sqn_nonneg _
    have hY0 : 0 ≤ 2 * Λ * ηQ * sqn (g ξ) := by positivity
    have hXA := hA ξ hξ
    have hqQ := hQ ξ hξ
    rw [le_div_iff₀ (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg r) hεV) (sub_nonneg.mpr hXA),
      mul_nonneg (mul_nonneg (sq_nonneg r) hεV) hY0,
      mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg εV)) (mul_nonneg (sq_nonneg Λ) hG0)]
  have hA2 : r ^ 2 * ∑ ξ ∈ s, (sqn (A ξ *ᵥ g ξ) - (2 * Λ * ηQ + εV * Λ ^ 2) * sqn (g ξ)) ≤
      ‖P‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hmode).trans ?_
    rw [← Finset.sum_div]
    exact hproj
  -- Step 1
  have hA1 : ‖x‖ ^ 2 ≤ r ^ 2 * ∑ ξ ∈ s, (qform Hp (g ξ) (g ξ) +
      ((κ - 1) * Λp + κ * e) * sqn (g ξ)) := by
    refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg r))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ξ _ => ?_
    have h := mul_le_mul_of_nonneg_left (hΛp (g ξ)) (by linarith : (0 : ℝ) ≤ κ - 1)
    nlinarith [h]
  have hfin : r ^ 2 * ∑ ξ ∈ s, (qform Hp (g ξ) (g ξ) + ((κ - 1) * Λp + κ * e) * sqn (g ξ)) -
      r ^ 2 * ∑ ξ ∈ s, (sqn (A ξ *ᵥ g ξ) - (2 * Λ * ηQ + εV * Λ ^ 2) * sqn (g ξ)) =
      r ^ 2 * ∑ ξ ∈ s, (qform Hp (g ξ) (g ξ) - sqn (A ξ *ᵥ g ξ) +
        ((κ - 1) * Λp + κ * e + εV * Λ ^ 2 + 2 * Λ * ηQ) * sqn (g ξ)) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun ξ _ => by ring
  rw [← hfin]
  linarith

omit [Fintype n] in
/-- **`cor:spec2:coupling`, the first display** (the matrix `𝐌(ξ)`), for one vector `w`: with
`w^*𝐌(ξ)w = (w^*H̃w + δ)/(p - 1)` (`lem:coupling-modes`, `δ = p c_ξ w^*𝐃w`),
`|δ| ≤ [p ≡ 1] (w^*𝐇^cov w + ζ̄ w^*𝐇^nc w) + (ε_≠ + ε_rem)|w|²` (`lem:spec2:paley` (b), (c) and
`p|c_ξ| r = 1`), `w^*𝐇^nc w ≤ Λ_nc|w|²`, `w^*H̃w ≤ w^*𝐇w + ε_H|w|²` (`lem:spec2:gram`) and
`w^*𝐇⁺w = w^*𝐇w + [p ≡ 1] w^*𝐇^cov w ≤ Λ₊|w|²`: then
`w^*𝐌w ≤ (w^*H̃w + [p ≡ 1] w^*𝐇^cov w + (ε_≠ + ε_rem + ε_par)|w|²)/(p - 1) ≤ Λ_M|w|²/(p - 1)` with
`ε_par = [p ≡ 1] ζ̄ Λ_nc` and `Λ_M = Λ₊ + ε_H + ε_≠ + ε_rem + ε_par`. The indicator `[p ≡ 1]` is
`ind ∈ {0, 1}`. -/
theorem coupling_M_bound {p wMw ht δ hcov hnc hH sw ind ζ εne εrem Λnc εH Λp : ℝ}
    (hp : 1 < p) (hM : wMw = (ht + δ) / (p - 1))
    (hδ : |δ| ≤ ind * (hcov + ζ * hnc) + (εne + εrem) * sw) (hind : 0 ≤ ind)
    (hζ : 0 ≤ ζ) (hnc' : hnc ≤ Λnc * sw) (hht : ht ≤ hH + εH * sw)
    (hplus : hH + ind * hcov ≤ Λp * sw) :
    wMw ≤ (ht + ind * hcov + (εne + εrem + ind * ζ * Λnc) * sw) / (p - 1) ∧
    wMw ≤ (Λp + εH + εne + εrem + ind * ζ * Λnc) * sw / (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  have h1 : δ ≤ ind * hcov + (εne + εrem + ind * ζ * Λnc) * sw := by
    have h := (le_abs_self δ).trans hδ
    have h2 : ind * (ζ * hnc) ≤ ind * (ζ * (Λnc * sw)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnc' hζ) hind
    nlinarith [h, h2]
  have hfirst : wMw ≤ (ht + ind * hcov + (εne + εrem + ind * ζ * Λnc) * sw) / (p - 1) := by
    rw [hM]
    exact div_le_div_of_nonneg_right (by linarith) hp1.le
  refine ⟨hfirst, hfirst.trans ?_⟩
  exact div_le_div_of_nonneg_right (by nlinarith [hht, hplus]) hp1.le

end Sarkozy.Spectral
