module

public import Sarkozy.TheoremC.Defs
public import Sarkozy.Variance.Eligible

@[expose] public section

/-!
# The variance form of a record difference from its norm envelope

`paper/sections/10_comparison_lemmas.tex`, `lem:record:variance-interface`(i) (the hypothesis
`‖Δ_𝔅‖ ≤ γ_𝔅` with `Δ_𝔅 1 = Δ_𝔅^* 1 = 0`); `paper/sections/09_comparison_theorem.tex`,
`def:record:comparison-law`(b) (the norm envelopes `D^ε_{𝔅,t}`, "diagonal copies of actual half
marginals of `t`, in the applications"); `paper/sections/22_variance.tex`, proof of
`lem:var-gain`(b) ("the change … has, relative to `m_{φ,𝔅}`, a cut operator … that annihilates the
constants on both sides by `eq:record:zero-marginal`, and has norm at most the coefficient `π̃_𝔅` of
its norm envelope").

Generic facts at one cut `c`:

* `ZeroMarginals c ζ`: `Q_ζ(F, 1) = Q_ζ(1, G) = 0` (`eq:record:zero-marginal` in form language);
  it passes to the symmetric and skew parts (`zeroMarginals_symPart`, `zeroMarginals_skewPart`)
  and to differences of measures with equal half marginals (`zeroMarginals_of_halfMarginals`);
* `form_smul_law`: the cut form is linear in the law;
* **`abs_form_le_variance_of_bracket`**: a norm-envelope bracket
  `(π̃ Diag(m)  ζ; ζ*  π̃ Diag(m)) ⪰_c 0` and zero marginals give the bilinear bound
  `|Q_ζ(G, H)| ≤ π̃ ‖G − E_m G‖_m ‖H − E_m H‖_m` against the variance form `Diag(m) − J(m)`. This is
  the hypothesis `hζ` of B10's `abs_term_le_variance`;
* **`eq_diagonalLaw_of_isDiagonalAt`**: a measure carried by the labellings fixed by the reflection
  of `c` (`TheoremC.IsDiagonalAt`) is the diagonal copy `Diag_c(m)` of its plus-half marginal. So
  every reserved-diagonal norm envelope of (CP4)(b) is `Diag_ι(m)` for an explicit `m ≥ 0`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.RecordExpansion Sarkozy.Variance Sarkozy.TheoremC

section Generic

variable {W Y : Type*} [Fintype W] [DecidableEq W]

/-- **Zero marginals** (`eq:record:zero-marginal`, `Δ 1 = Δ^* 1 = 0`) in form language:
`Q_ζ(F, 1) = 0` and `Q_ζ(1, G) = 0` for all `F, G`. -/
def ZeroMarginals (c : ReflectionCut W) (ζ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  (∀ F : (c.Half → Y) → ℝ, c.form ζ F 1 = 0) ∧ ∀ G : (c.Half → Y) → ℝ, c.form ζ 1 G = 0

/-- The cut form is linear in the law: `Q_{a L}(F, G) = a Q_L(F, G)`. -/
theorem form_smul_law (c : ReflectionCut W) (a : ℝ) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → Y) → ℝ) : c.form (a • L) F G = a * c.form L F G := by
  unfold ReflectionCut.form
  rw [LinearMap.smul_apply, smul_eq_mul]

/-- The cut form of a difference of laws. -/
theorem form_sub_law (c : ReflectionCut W) (L M : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → Y) → ℝ) : c.form (L - M) F G = c.form L F G - c.form M F G := by
  unfold ReflectionCut.form
  rw [LinearMap.sub_apply]

/-- The cut form of a sum of laws. -/
theorem form_add_law (c : ReflectionCut W) (L M : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → Y) → ℝ) : c.form (L + M) F G = c.form L F G + c.form M F G := by
  unfold ReflectionCut.form
  rw [LinearMap.add_apply]

/-- The symmetric part of a law with zero marginals has zero marginals. -/
theorem zeroMarginals_symPart (c : ReflectionCut W) {ζ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : ZeroMarginals c ζ) : ZeroMarginals c (symPart c ζ) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro F
    change (1 / 2 : ℝ) * (c.form ζ F 1 + c.form (reflect c ζ) F 1) = 0
    rw [form_reflect, h1, h2]
    ring
  · intro G
    change (1 / 2 : ℝ) * (c.form ζ 1 G + c.form (reflect c ζ) 1 G) = 0
    rw [form_reflect, h1, h2]
    ring

/-- The skew part of a law with zero marginals has zero marginals. -/
theorem zeroMarginals_skewPart (c : ReflectionCut W) {ζ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : ZeroMarginals c ζ) : ZeroMarginals c (skewPart c ζ) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro F
    change (1 / 2 : ℝ) * (c.form ζ F 1 - c.form (reflect c ζ) F 1) = 0
    rw [form_reflect, h1, h2]
    ring
  · intro G
    change (1 / 2 : ℝ) * (c.form ζ 1 G - c.form (reflect c ζ) 1 G) = 0
    rw [form_reflect, h1, h2]
    ring

/-- **`eq:record:zero-marginal`**: the difference of two laws with the same half marginal `m` (on
both sides) has zero marginals (W1's `zero_marginal`). -/
theorem zeroMarginals_of_halfMarginals [Fintype Y] [DecidableEq Y] (c : ReflectionCut W)
    {Pr Pr' : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} {m : (c.Half → Y) → ℝ} (hPr : HasHalfMarginals c Pr m)
    (hPr' : HasHalfMarginals c Pr' m) : ZeroMarginals c (Pr' - Pr) :=
  zero_marginal c hPr hPr'

variable [Fintype Y]

/-- The centred second moment: `∑ m (G − a)² = ∑ m G² − (∑ m G)²/∑ m` for `a = E_m G`
(`∑ m > 0`). -/
theorem sum_centred_sq {c : ReflectionCut W} {m : (c.Half → Y) → ℝ} (hpos : 0 < ∑ x, m x)
    (G : (c.Half → Y) → ℝ) :
    ∑ x, m x * ((G x - (∑ y, m y * G y) / ∑ y, m y) * (G x - (∑ y, m y * G y) / ∑ y, m y)) =
      ∑ x, m x * (G x * G x) - (∑ x, m x * G x) * (∑ y, m y * G y) / ∑ x, m x := by
  set μG := (∑ y, m y * G y) / ∑ y, m y
  have h1 : ∑ x, m x * ((G x - μG) * (G x - μG)) =
      ∑ x, m x * (G x * G x) - 2 * μG * ∑ x, m x * G x + μG * μG * ∑ x, m x := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    ring
  rw [h1]
  have hne : (∑ x, m x) ≠ 0 := hpos.ne'
  simp only [μG]
  field_simp
  ring

/-- **The variance bound from a norm-envelope bracket**: if
`(π̃ Diag_c(m)  ζ; ζ*  π̃ Diag_c(m)) ⪰_c 0` with `m ≥ 0`, `π̃ ≥ 0`, and `ζ` has zero marginals,
then `|Q_ζ(G, H)| ≤ π̃ √(Q_{Diag(m) − J(m)}(G, G)) √(Q_{Diag(m) − J(m)}(H, H))`. -/
theorem abs_form_le_variance_of_bracket (c : ReflectionCut W) {ζ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    {m : (c.Half → Y) → ℝ} {π : ℝ} (hm : ∀ x, 0 ≤ m x) (hπ : 0 ≤ π)
    (hb : c.Bracket (π • c.diagonalLaw m) ζ (π • c.diagonalLaw m)) (hz : ZeroMarginals c ζ)
    (G H : (c.Half → Y) → ℝ) :
    |c.form ζ G H| ≤ π * Real.sqrt (c.form (c.diagonalLaw m - indepLaw c m) G G) *
      Real.sqrt (c.form (c.diagonalLaw m - indepLaw c m) H H) := by
  set a := (∑ y, m y * G y) / ∑ y, m y
  set b := (∑ y, m y * H y) / ∑ y, m y
  have hc := form_centred_of_zero_marginal c hz.1 hz.2 G H a b
  have hab := hb.abs_form_le (fun x => G x - a) (fun x => H x - b)
  rw [← hc, form_smul_law, form_smul_law, c.form_diagonalLaw, c.form_diagonalLaw] at hab
  rw [form_diagonal_sub_indep, form_diagonal_sub_indep]
  by_cases h0 : ∑ x, m x = 0
  · have hz0 : ∀ x, m x = 0 := fun x =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hm x)).mp h0 x (mem_univ x)
    simp only [hz0, zero_mul, sum_const_zero, mul_zero, Real.sqrt_zero] at hab
    simp only [hz0, zero_mul, sum_const_zero, zero_div, sub_zero, Real.sqrt_zero, mul_zero]
    exact hab
  · have hpos : 0 < ∑ x, m x := lt_of_le_of_ne (sum_nonneg fun x _ => hm x) (Ne.symm h0)
    have eG := sum_centred_sq hpos G
    have eH := sum_centred_sq hpos H
    rw [eG, eH] at hab
    set A := ∑ x, m x * (G x * G x) - (∑ x, m x * G x) * (∑ y, m y * G y) / ∑ x, m x
    set B := ∑ x, m x * (H x * H x) - (∑ x, m x * H x) * (∑ y, m y * H y) / ∑ x, m x
    have hA : 0 ≤ A := by
      rw [← eG]
      exact sum_nonneg fun x _ => mul_nonneg (hm x) (mul_self_nonneg _)
    have hB : 0 ≤ B := by
      rw [← eH]
      exact sum_nonneg fun x _ => mul_nonneg (hm x) (mul_self_nonneg _)
    rw [Real.sqrt_mul hπ, Real.sqrt_mul hπ] at hab
    have hpp : Real.sqrt π * Real.sqrt A * (Real.sqrt π * Real.sqrt B) =
        π * Real.sqrt A * Real.sqrt B := by
      have h := Real.mul_self_sqrt hπ
      calc Real.sqrt π * Real.sqrt A * (Real.sqrt π * Real.sqrt B)
          = (Real.sqrt π * Real.sqrt π) * Real.sqrt A * Real.sqrt B := by ring
        _ = π * Real.sqrt A * Real.sqrt B := by rw [h]
    linarith [hab, hpp]

end Generic

section Diagonal

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **A reserved-diagonal measure is the diagonal copy of its plus-half marginal**: if `κ` is
carried by the labellings fixed by the reflection of `c` (`IsDiagonalAt c κ`), then
`κ = Diag_c(m)` with `m = halfMarginalPlus c κ`. -/
theorem eq_diagonalLaw_of_isDiagonalAt (c : ReflectionCut Slot) {κ : SlotMeasure X}
    (hκ : IsDiagonalAt c κ) : κ = c.diagonalLaw (Comparison.halfMarginalPlus c κ) := by
  apply LinearMap.ext
  intro f
  -- the plus-half marginal as a sum of densities
  have hm : ∀ x : c.Half → X, Comparison.halfMarginalPlus c κ x =
      ∑ z, lawDensity κ z * (if (fun v : c.Half => z v.1) = x then 1 else 0) := by
    intro x
    unfold Comparison.halfMarginalPlus
    rw [linearFunctional_density κ]
    rfl
  have hdiag : c.diagonalLaw (Comparison.halfMarginalPlus c κ) f =
      ∑ x, Comparison.halfMarginalPlus c κ x * f (c.join x x) := rfl
  rw [hdiag, linearFunctional_density κ f]
  simp_rw [hm, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  have hsum : ∑ x : c.Half → X, lawDensity κ z *
      (if (fun v : c.Half => z v.1) = x then (1 : ℝ) else 0) * f (c.join x x) =
      lawDensity κ z * f (c.join (fun v : c.Half => z v.1) (fun v : c.Half => z v.1)) := by
    rw [sum_eq_single (fun v : c.Half => z v.1)]
    · simp
    · intro x _ hx
      simp only [Ne.symm hx, ite_false, mul_zero, zero_mul]
    · intro h
      exact absurd (mem_univ _) h
  change κ (fun y => if y = z then 1 else 0) * f z = _
  change lawDensity κ z * f z = _
  rw [hsum]
  by_cases hd : lawDensity κ z = 0
  · rw [hd, zero_mul, zero_mul]
  · have hfix := hκ z hd
    have hj : z = c.join (fun v : c.Half => z v.1) (fun v : c.Half => z v.1) := by
      rw [← c.halves_eq_iff]
      refine ⟨rfl, ?_⟩
      funext v
      exact hfix v.1
    rw [← hj]

end Diagonal

end Sarkozy.OpsVariance
