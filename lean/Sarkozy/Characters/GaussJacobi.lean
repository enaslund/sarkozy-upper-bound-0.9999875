module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Gauss and Jacobi sums (`thm:gauss`, `thm:jacobi`)

`paper/sections/04_notation.tex`. The paper cites these classical facts (Ireland–Rosen, Berndt–
Evans–Williams) and also proves them; here they are derived from Mathlib's `gaussSum` and
`jacobiSum` with the standard additive character `e(t) = exp(2πi t/p)` of `ℤ/pℤ`
(`ZMod.stdAddChar`), so they need not remain external inputs.

* `gaussSumAt ψ s = g_s(ψ) = ∑_t ψ(t) e(st)`.
* `gaussSumAt_zero`, `gaussSumAt_twist`: `thm:gauss`(i), `g_0(ψ) = 0` and `g_s(ψ) = ψ̄(s) g(ψ)`
  (`ψ̄ = ψ⁻¹` for complex characters of a finite group).
* `norm_gaussSum`: `thm:gauss`(ii), `|g(ψ)| = √p`.
* `quadratic_gaussSum_sq`: `thm:gauss`(iii), `G_χ² = χ(-1) p` for the quadratic character.
* `jacobiSum_eq` and `norm_jacobiSum`: `thm:jacobi`, `J(ψ₁, ψ₂) = g(ψ₁)g(ψ₂)/g(ψ₁ψ₂)` and
  `|J(ψ₁, ψ₂)| = √p` when `ψ₁, ψ₂, ψ₁ψ₂` are nontrivial.
-/

@[expose] public section

namespace Sarkozy.Characters

open AddChar MulChar

variable {p : ℕ} [hp : Fact p.Prime]

/-- `g_s(ψ) = ∑_t ψ(t) e(st/p)`. -/
noncomputable def gaussSumAt (ψ : MulChar (ZMod p) ℂ) (s : ZMod p) : ℂ :=
  gaussSum ψ ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift s)

/-- **`thm:gauss`(i), first part**: `g_0(ψ) = 0` for nontrivial `ψ`. -/
theorem gaussSumAt_zero {ψ : MulChar (ZMod p) ℂ} (hψ : ψ ≠ 1) : gaussSumAt ψ 0 = 0 := by
  unfold gaussSumAt gaussSum
  simp only [mulShift_apply, zero_mul, map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one hψ

/-- **`thm:gauss`(i), twist**: `g_s(ψ) = ψ⁻¹(s) g(ψ)` for `s ≠ 0`. -/
theorem gaussSumAt_twist (ψ : MulChar (ZMod p) ℂ) {s : ZMod p} (hs : s ≠ 0) :
    gaussSumAt ψ s = ψ⁻¹ s * gaussSum ψ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
  unfold gaussSumAt
  have := gaussSum_mulShift_eq ψ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) (Units.mk0 s hs)
  simpa using this

/-- **`thm:gauss`(ii)**: `|g(ψ)| = √p` for nontrivial `ψ`. -/
theorem norm_gaussSum {ψ : MulChar (ZMod p) ℂ} (hψ : ψ ≠ 1) :
    ‖gaussSum ψ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)‖ = Real.sqrt p := by
  have hprim := ZMod.isPrimitive_stdAddChar p
  have h := gaussSum_mul_gaussSum_eq_card hψ hprim
  rw [← star_gaussSum_eq, ZMod.card] at h
  -- `g * conj g = |g|²`
  have hsq : ‖gaussSum ψ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)‖ ^ 2 = p := by
    rw [Complex.star_def, Complex.mul_conj'] at h
    exact_mod_cast h
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- The complex-valued quadratic character `χ_p`. -/
noncomputable def chiC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- **`thm:gauss`(iii)**: `G_χ² = χ(-1) p` for the quadratic character at an odd prime. -/
theorem quadratic_gaussSum_sq (hp2 : p ≠ 2) :
    gaussSum (chiC p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ^ 2 = chiC p (-1) * p := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hne : chiC p ≠ 1 := by
    unfold chiC
    exact (ringHomComp_ne_one_iff (RingHom.injective_int (Int.castRingHom ℂ))).mpr
      (quadraticChar_ne_one hF)
  have hquad : (chiC p).IsQuadratic := (quadraticChar_isQuadratic (ZMod p)).comp _
  have h := gaussSum_sq hne hquad (ZMod.isPrimitive_stdAddChar p)
  rwa [ZMod.card] at h

/-- **`thm:jacobi`**: `J(ψ₁, ψ₂) = g(ψ₁) g(ψ₂) / g(ψ₁ψ₂)` when `ψ₁ψ₂` is nontrivial. -/
theorem jacobiSum_eq {ψ₁ ψ₂ : MulChar (ZMod p) ℂ} (h12 : ψ₁ * ψ₂ ≠ 1) :
    jacobiSum ψ₁ ψ₂ = gaussSum ψ₁ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
      gaussSum ψ₂ ZMod.stdAddChar / gaussSum (ψ₁ * ψ₂) ZMod.stdAddChar := by
  have hcard : ((Fintype.card (ZMod p) : ℕ) : ℂ) ≠ 0 := by
    rw [ZMod.card]; exact_mod_cast hp.out.ne_zero
  exact jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum hcard h12 (ZMod.isPrimitive_stdAddChar p)

/-- **`thm:jacobi`, modulus**: `|J(ψ₁, ψ₂)| = √p` when `ψ₁`, `ψ₂`, `ψ₁ψ₂` are nontrivial. -/
theorem norm_jacobiSum {ψ₁ ψ₂ : MulChar (ZMod p) ℂ} (h1 : ψ₁ ≠ 1) (h2 : ψ₂ ≠ 1)
    (h12 : ψ₁ * ψ₂ ≠ 1) : ‖jacobiSum ψ₁ ψ₂‖ = Real.sqrt p := by
  rw [jacobiSum_eq h12, norm_div, norm_mul, norm_gaussSum h1, norm_gaussSum h2,
    norm_gaussSum h12]
  have : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)).ne'
  field_simp

end Sarkozy.Characters
