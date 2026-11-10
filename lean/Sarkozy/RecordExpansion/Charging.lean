module

public import Sarkozy.RecordExpansion.Bound
public import Sarkozy.Reflection.Transport

/-!
# Charging rules for record changes

`rem:cp:charging` (i), (ii) of the paper (Section 9) produce the brackets of
(CP4)(b) for deleted and replaced records. Here a nonnegative measure `κ` on
`V → X` is a weight `w ≥ 0` (`signedIntegral w`), its half marginals at a cut
`c` are `plusMarginal c w` and `minusMarginal c w` (the minus half read on the
plus half through the reflection), and `Diag_c(m)` is
`ReflectionCut.diagonalLaw c m` (`Sarkozy/Reflection/Transport.lean`).

* `bracket_diagonal_marginals`: (P1) of `lem:energy-toolkit`, first step:
  `(Diag(m_+)  κ; κ*  Diag(m_-)) ⪰_c 0`, since its form at `(F, G)` is
  `∫ (F(z_+) + G(z̃_-))² dκ`.
* `bracket_delete`: charging rule (i). If `κ` is symmetric at `c`, its two half
  marginals agree, and a deleted record `w κ` (change `-w κ`) has the bracket
  `(w Diag(m)  -wκ; -wκ  w Diag(m)) ⪰_c 0`: it is charged its mass `w` with the
  norm envelope `Diag(m)`.
* `bracket_of_norm_bound`: charging rule (ii). A signed change `Δ` whose cut
  form satisfies `|Q_Δ(F, G)| ≤ a ‖F‖_m ‖G‖_m` (operator norm at most `a` on
  `L²(m)`) has the bracket `(a Diag(m)  Δ; Δ*  a Diag(m)) ⪰_c 0`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y] [DecidableEq Y]

/-- The plus-half marginal `m_+(x) = κ(z_{V_+} = x)` of a weight. -/
noncomputable def plusMarginal (c : ReflectionCut W) (w : (W → Y) → ℝ) (x : c.Half → Y) : ℝ :=
  ∑ z, if (fun v : c.Half => z v.1) = x then w z else 0

/-- The minus-half marginal `m_-(x) = κ(z_{c V_+} = x)`, the minus half read on the
plus half through the reflection. -/
noncomputable def minusMarginal (c : ReflectionCut W) (w : (W → Y) → ℝ) (x : c.Half → Y) :
    ℝ :=
  ∑ z, if (fun v : c.Half => z (c.flip v.1)) = x then w z else 0

omit [DecidableEq Y] in
theorem sum_marginal_mul {H : Type*} [Fintype H]
    [DecidableEq H] (proj : (W → Y) → H) (w : (W → Y) → ℝ) (f : H → ℝ) :
    ∑ x, (∑ z, if proj z = x then w z else 0) * f x = ∑ z, w z * f (proj z) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro z _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem plusMarginal_nonneg (c : ReflectionCut W) {w : (W → Y) → ℝ} (hw : ∀ z, 0 ≤ w z)
    (x : c.Half → Y) : 0 ≤ plusMarginal c w x :=
  sum_nonneg fun z _ => by split_ifs <;> simp [hw z]

theorem minusMarginal_nonneg (c : ReflectionCut W) {w : (W → Y) → ℝ} (hw : ∀ z, 0 ≤ w z)
    (x : c.Half → Y) : 0 ≤ minusMarginal c w x :=
  sum_nonneg fun z _ => by split_ifs <;> simp [hw z]

/-- **(P1), the bracket of a positive coupling with the diagonal copies of its half
marginals**: `(Diag(m_+)  κ; κ*  Diag(m_-)) ⪰_c 0` for a nonnegative weight `w`. -/
theorem bracket_diagonal_marginals (c : ReflectionCut W) {w : (W → Y) → ℝ}
    (hw : ∀ z, 0 ≤ w z) :
    c.Bracket (c.diagonalLaw (plusMarginal c w)) (signedIntegral w)
      (c.diagonalLaw (minusMarginal c w)) := by
  refine ⟨c.diagonalLaw_positive (plusMarginal_nonneg c hw),
    c.diagonalLaw_positive (minusMarginal_nonneg c hw), ?_⟩
  intro F G
  rw [c.form_diagonalLaw, c.form_diagonalLaw]
  have h1 : ∑ x, plusMarginal c w x * (F x * F x) =
      ∑ z, w z * (F (fun v => z v.1) * F (fun v => z v.1)) :=
    sum_marginal_mul (fun z (v : c.Half) => z v.1) w (fun x => F x * F x)
  have h2 : ∑ x, minusMarginal c w x * (G x * G x) =
      ∑ z, w z * (G (fun v => z (c.flip v.1)) * G (fun v => z (c.flip v.1))) :=
    sum_marginal_mul (fun z (v : c.Half) => z (c.flip v.1)) w
      (fun x => G x * G x)
  have h3 : c.form (signedIntegral w) F G =
      ∑ z, w z * (F (fun v => z v.1) * G (fun v => z (c.flip v.1))) := rfl
  rw [h1, h2, h3, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_nonneg
  intro z _
  have := mul_nonneg (hw z) (sq_nonneg (F (fun v => z v.1) + G (fun v => z (c.flip v.1))))
  nlinarith

/-- For a weight symmetric at `c` the two half marginals agree. -/
theorem minusMarginal_eq_plusMarginal (c : ReflectionCut W) {w : (W → Y) → ℝ}
    (hsym : IsSymmetricAt c (signedIntegral w)) :
    minusMarginal c w = plusMarginal c w := by
  funext x
  have h := congrArg (fun L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ =>
    L (fun z => if (fun v : c.Half => z v.1) = x then 1 else 0)) hsym
  simp only [reflect_apply] at h
  change (∑ z, w z * (if (fun v : c.Half => (z ∘ c.flip) v.1) = x then 1 else 0)) =
    ∑ z, w z * (if (fun v : c.Half => z v.1) = x then 1 else 0) at h
  simp only [mul_ite, mul_one, mul_zero, Function.comp_apply] at h
  exact h

omit [Fintype Y] [DecidableEq Y] in
/-- Negating the off-diagonal block preserves a bracket. -/
theorem bracket_neg {c : ReflectionCut W} {L K R : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Bracket L K R) : c.Bracket L (-K) R := by
  refine ⟨h.left_positive, h.right_positive, ?_⟩
  intro F G
  have h1 := h.nonneg F ((-1 : ℝ) • G)
  rw [c.form_smul_right, c.form_smul_left, c.form_smul_right] at h1
  change 0 ≤ c.form L F F + 2 * -c.form K F G + c.form R G G
  linarith

/-- **Charging rule (i)** (`rem:cp:charging` (i)): a deleted record `w κ`, `κ ≥ 0`
symmetric at `c` with half marginal `m`, has the bracket
`(w Diag(m)  -wκ; -wκ  w Diag(m)) ⪰_c 0`. -/
theorem bracket_delete (c : ReflectionCut W) {κ : (W → Y) → ℝ} (hκ : ∀ z, 0 ≤ κ z)
    (hsym : IsSymmetricAt c (signedIntegral κ)) {w : ℝ} (hw : 0 ≤ w) :
    c.Bracket (w • c.diagonalLaw (plusMarginal c κ)) (-(w • signedIntegral κ))
      (w • c.diagonalLaw (plusMarginal c κ)) := by
  have h := bracket_diagonal_marginals c hκ
  rw [minusMarginal_eq_plusMarginal c hsym] at h
  have h' := bracket_smul h hw
  exact bracket_neg h'

omit [Fintype Y] [DecidableEq Y] in
/-- **Charging rule (ii)** (`rem:cp:charging` (ii)): if the cut form of a signed
change `Δ` is bounded by `a` relative to a nonnegative half marginal `m`,
`|Q_Δ(F, G)| ≤ a ‖F‖_m ‖G‖_m` with `‖F‖_m² = ∑_x m(x) F(x)²`, then
`(a Diag(m)  Δ; Δ*  a Diag(m)) ⪰_c 0`. -/
theorem bracket_of_norm_bound [Fintype Y] (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm : ∀ x, 0 ≤ m x) {a : ℝ} (ha : 0 ≤ a) (Δ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (hΔ : ∀ F G : (c.Half → Y) → ℝ, |c.form Δ F G| ≤
      a * Real.sqrt (∑ x, m x * (F x * F x)) * Real.sqrt (∑ x, m x * (G x * G x))) :
    c.Bracket (a • c.diagonalLaw m) Δ (a • c.diagonalLaw m) := by
  have hD := c.diagonalLaw_positive hm
  refine ⟨hD.smul ha, hD.smul ha, ?_⟩
  intro F G
  have hF : 0 ≤ ∑ x, m x * (F x * F x) := sum_nonneg fun x _ => mul_nonneg (hm x) (mul_self_nonneg _)
  have hG : 0 ≤ ∑ x, m x * (G x * G x) := sum_nonneg fun x _ => mul_nonneg (hm x) (mul_self_nonneg _)
  change 0 ≤ a * c.form (c.diagonalLaw m) F F + 2 * c.form Δ F G +
    a * c.form (c.diagonalLaw m) G G
  rw [c.form_diagonalLaw, c.form_diagonalLaw]
  set p := Real.sqrt (∑ x, m x * (F x * F x))
  set q := Real.sqrt (∑ x, m x * (G x * G x))
  have hp : p * p = ∑ x, m x * (F x * F x) := Real.mul_self_sqrt hF
  have hq : q * q = ∑ x, m x * (G x * G x) := Real.mul_self_sqrt hG
  have h1 := neg_abs_le (c.form Δ F G)
  have h2 := hΔ F G
  have h3 : 0 ≤ a * ((p - q) * (p - q)) := mul_nonneg ha (mul_self_nonneg _)
  rw [← hp, ← hq]
  nlinarith

end Sarkozy.RecordExpansion
