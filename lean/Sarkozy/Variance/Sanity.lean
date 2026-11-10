module

public import Sarkozy.Variance.Eligible

/-!
# Non-vacuity of the Section 22 predicates

Toy instances for the predicates introduced in `Sarkozy/Variance/`:
* `centredNormLe_indepLaw`: the product law `J_c(m)` has Markov operator `𝒥`, so
  `CentredNormLe c (J_c(m)) m 0`; with (P3) this gives `J ⪯ J`.
* `centredNormLe_diagonalLaw`: the diagonal copy `Diag_c(m)` (operator `I`) satisfies
  `CentredNormLe c (Diag_c(m)) m 1` for `m ≥ 0`: `‖I - 𝒥‖ ≤ 1` on `L²(m)`. This is the case
  `κ₀ = 1` of (P3) for `π = Diag(m)`.
* `hasHalfMarginals_diagonalLaw`, `hasHalfMarginals_indepLaw`: both have half marginal `m`
  (for `J_c(m)` when `∑ m = 1`).
* `isRepair_self`: a nonnegative record weight with both half marginals `m`, of mass one and
  satisfying the invariance predicate, is a repair of itself (`def:record:eligible`).
* `rootDensityA_refl` (in `Eligible.lean`): `ν = λ` satisfies `hyp:variance:A` with `M = 1`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

section Toys

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
/-- `J_c(m)` has centred norm `0` relative to `m`. -/
theorem centredNormLe_indepLaw (c : ReflectionCut W) (m : (c.Half → Y) → ℝ) :
    CentredNormLe c (indepLaw c m) m 0 := by
  intro f g
  rw [form_indepLaw, sub_self, abs_zero, zero_mul, zero_mul]

omit [DecidableEq Y] in
/-- `Diag_c(m)` has centred norm at most `1` relative to `m ≥ 0`, `∑ m > 0`. -/
theorem centredNormLe_diagonalLaw (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm : ∀ x, 0 ≤ m x) (hS : 0 < ∑ x, m x) : CentredNormLe c (c.diagonalLaw m) m 1 := by
  intro f g
  rw [c.form_diagonalLaw, one_mul]
  set S := ∑ x, m x with hSdef
  set a := (∑ x, m x * f x) / S
  set b := (∑ x, m x * g x) / S
  -- the centred form is `∑ m (f - a)(g - b)`
  have hcen : ∑ x, m x * (f x * g x) - (∑ x, m x * f x) * (∑ y, m y * g y) / S =
      ∑ x, (Real.sqrt (m x) * (f x - a)) * (Real.sqrt (m x) * (g x - b)) := by
    have hpt : ∀ x, (Real.sqrt (m x) * (f x - a)) * (Real.sqrt (m x) * (g x - b)) =
        m x * (f x * g x) - b * (m x * f x) - a * (m x * g x) + a * b * m x := by
      intro x
      have := Real.mul_self_sqrt (hm x)
      rw [show Real.sqrt (m x) * (f x - a) * (Real.sqrt (m x) * (g x - b)) =
        (Real.sqrt (m x) * Real.sqrt (m x)) * ((f x - a) * (g x - b)) by ring, this]
      ring
    simp_rw [hpt]
    rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
      ← hSdef]
    simp only [a, b]
    field_simp
    ring
  -- the centred norms are at most the uncentred ones
  have hvar : ∀ (h : (c.Half → Y) → ℝ) (t : ℝ), t = (∑ x, m x * h x) / S →
      ∑ x, (Real.sqrt (m x) * (h x - t)) ^ 2 ≤ ∑ x, m x * h x ^ 2 := by
    intro h t ht
    have hpt : ∀ x, (Real.sqrt (m x) * (h x - t)) ^ 2 =
        m x * h x ^ 2 - 2 * t * (m x * h x) + t ^ 2 * m x := by
      intro x
      rw [mul_pow, Real.sq_sqrt (hm x)]
      ring
    simp_rw [hpt]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← hSdef]
    have hh : ∑ x, m x * h x = t * S := by
      rw [ht]
      field_simp
    rw [hh]
    nlinarith [mul_nonneg (sq_nonneg t) hS.le]
  rw [hcen]
  have hcs2 := Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (m x) * (f x - a))
    (fun x => Real.sqrt (m x) * (g x - b))
  have hcs : |∑ x, (Real.sqrt (m x) * (f x - a)) * (Real.sqrt (m x) * (g x - b))| ≤
      Real.sqrt (∑ x, (Real.sqrt (m x) * (f x - a)) ^ 2) *
        Real.sqrt (∑ x, (Real.sqrt (m x) * (g x - b)) ^ 2) := by
    rw [← Real.sqrt_mul (sum_nonneg fun x _ => sq_nonneg _)]
    exact Real.abs_le_sqrt hcs2
  refine hcs.trans ?_
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (hvar f a rfl)
  · exact Real.sqrt_le_sqrt (hvar g b rfl)
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

omit [DecidableEq Y] in
/-- `Diag_c(m)` has half marginal `m`. -/
theorem hasHalfMarginals_diagonalLaw (c : ReflectionCut W) (m : (c.Half → Y) → ℝ) :
    HasHalfMarginals c (c.diagonalLaw m) m :=
  ⟨fun F => by rw [c.form_diagonalLaw]; simp, fun G => by rw [c.form_diagonalLaw]; simp⟩

omit [DecidableEq Y] in
/-- `J_c(m)` has half marginal `m` when `∑ m = 1`. -/
theorem hasHalfMarginals_indepLaw (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm1 : ∑ x, m x = 1) : HasHalfMarginals c (indepLaw c m) m :=
  ⟨fun F => by rw [form_indepLaw, hm1]; simp [hm1], fun G => by rw [form_indepLaw, hm1]; simp [hm1]⟩

/-- A nonnegative record weight with both half marginals `m`, of mass one and satisfying the
invariance predicate, is a repair of itself. -/
theorem isRepair_self (c : ReflectionCut W) (Inv : (((W → Y) → ℝ) →ₗ[ℝ] ℝ) → Prop)
    {w : (W → Y) → ℝ} {m : (c.Half → Y) → ℝ} (hw : ∀ z, 0 ≤ w z)
    (hinv : Inv (signedIntegral w)) (hp : plusMarginal c w = m) (hn : minusMarginal c w = m)
    (hmass : signedIntegral w (fun _ => 1) = 1) :
    IsRepair c Inv m (signedIntegral w) := by
  refine ⟨⟨1, fun _ => 1, fun _ => w, fun _ z => hw z, fun _ => hinv, fun _ => ⟨hp, hn⟩, ?_⟩,
    hmass⟩
  simp

end Toys

end Sarkozy.Variance
