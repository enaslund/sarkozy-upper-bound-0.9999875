module

public import Sarkozy.Kernel.CompleteWeights

@[expose] public section

/-!
# Square classes and root-class data

Definitions shared by the kernel estimate for general moduli.

* `IsStrictSquareClass d r` (`def:strict-square-class`): for `D = 8d`, `d` odd, the
  residue `r` is `≡ 1 mod 8` and a nonzero square modulo every prime dividing `d`.
* `IsNonvanishingSquareClass D r` (`def:nonvanishing-square-class`): `v₂(D) ≥ 3`; at
  each odd `p ∣ D`, `r mod p^{v_p(D)}` has valuation `2j < v_p(D)` and a square unit
  part; at `2`, valuation `2j` with `v₂(D) - 2j ≥ 3` and unit part `≡ 1 mod 8`.
* `classWeight D' m₀`: the normalized indicator `D' · 1_{m ≡ m₀ (mod D')}`.
* `RootClassDatum D r`: a root class `m₀ mod D'`, `D' ∣ D`, whose elements square to `r`
  modulo `D`, and against which the quadratic phases `e(α m²)` with denominator built
  from the primes of `D` but not dividing `D` have mean zero. This is the content of the
  paper's `lem:kernel-depth-classes` used in Appendix C (the local rule of
  `lem:record:prime-power-lift`(a)).

New material for this paper.
-/

namespace Sarkozy

namespace Kernel

/-- Strict square classes modulo `D = 8d` (`def:strict-square-class`): `r ≡ 1 mod 8` and
`r` is a nonzero square modulo every prime dividing `d`. -/
def IsStrictSquareClass (d : ℕ) (r : ℤ) : Prop :=
  r ≡ 1 [ZMOD 8] ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ d → (r : ZMod ℓ) ≠ 0 ∧ IsSquare (r : ZMod ℓ)

/-- Nonvanishing square classes modulo `D` (`def:nonvanishing-square-class`), with
`D = 2^{h₂} ∏_{p odd} p^{h_p}`, `h₂ ≥ 3`, `h_p = D.factorization p`: at every prime
`p ∣ D` the reduction of `r` modulo `p^{h_p}` is `p^{2j} u` with `p ∤ u`, where at odd
`p` one has `2j < h_p` and `u` a square modulo `p`, and at `p = 2` one has
`h₂ - 2j ≥ 3` and `u ≡ 1 mod 8`. -/
def IsNonvanishingSquareClass (D : ℕ) (r : ℤ) : Prop :=
  3 ≤ D.factorization 2 ∧
  ∀ p : ℕ, p.Prime → p ∣ D →
    ∃ j : ℕ, ∃ u : ℤ, ¬ (p : ℤ) ∣ u ∧
      r ≡ (p : ℤ) ^ (2 * j) * u [ZMOD (p : ℤ) ^ (D.factorization p)] ∧
      (if p = 2 then 2 * j + 3 ≤ D.factorization 2 ∧ u ≡ 1 [ZMOD 8]
        else 2 * j < D.factorization p ∧ IsSquare (u : ZMod p))

/-- The normalized indicator `D' · 1_{m ≡ m₀ (mod D')}` of a residue class. -/
noncomputable def classWeight (D' m₀ m : ℕ) : ℂ :=
  if m ≡ m₀ [MOD D'] then (D' : ℂ) else 0

/-- A root class for the square class `r` modulo `D` (paper: `lem:kernel-depth-classes`):
the class `m₀ mod D'` with `D' ∣ D`, every element of which squares to `r` modulo `D`,
and such that for every `α` whose reduced denominator is built from primes of `D` but
does not divide `D`, the phase `e(α m²)` has mean zero against the class weight. -/
structure RootClassDatum (D : ℕ) (r : ℤ) where
  period : ℕ
  base : ℕ
  period_pos : 0 < period
  period_dvd : period ∣ D
  root : ∀ m : ℕ, m ≡ base [MOD period] → (D : ℤ) ∣ (m : ℤ) ^ 2 - r
  vanish : ∀ α : ℚ, (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ α.den → ℓ ∣ D) → ¬ α.den ∣ D →
    periodicMean (fun m => classWeight period base m * expPhase ((α : ℝ) * (m : ℝ) ^ 2))
      (α.den * period) = 0

end Kernel

end Sarkozy
