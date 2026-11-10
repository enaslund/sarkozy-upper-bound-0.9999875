module

public import Sarkozy.Reflection.Bracket
public import Sarkozy.ProbabilityConstructions

/-!
# The deleted equality events: the bracket of `thm:density:iid-prefix`(c)

`paper/sections/30_density_moment_upgrade.tex`, proof of `thm:density:iid-prefix`(c). Fix a
reflection cut `ι` of the slots, a reference law `μ` reflection positive at `ι`, a law `h` on the
labellings of the half, and a nonnegative measure `E` (weights `e`) whose two half marginals are
both `η h` (`DeletionMarginals`). Write `D = Diag_ι(h)` for the diagonal copy (`diagLaw`: the half
labels copied to the mirror slots).

* `form_diagLaw`: the cut form of `D` is `(F, G) ↦ h(F G)`.
* `deletion_form_le`: **a positive coupling is a contraction between its marginal `L²`
  spaces**: `|E(F ⊗ G)| ≤ η ‖F‖_{L²(h)} ‖G‖_{L²(h)}`.
* `deletion_sym_skew_le`: the symmetric and skew parts of `E` have operator norm at most `η`
  between the half `L²(h)` spaces; no symmetry of `E` is assumed.
* `deletion_bracket`: **the displayed bracket of (c)**,
  `[[μ + η D, μ - E], [(μ - E)^*, μ + η D]] ⪰_ι 0` (`ReflectionCut.Bracket`): the block matrix
  `[[η D, -E], [-E^*, η D]]` is positive by the contraction, and `[[μ, μ], [μ, μ]]` is positive by
  reflection positivity of `μ`.

This module is the analytic part of (c), for any cut, reference and deleted measure, with the
marginal property `DeletionMarginals` as hypothesis. The probabilistic part, that for the
replacement prefix and the six actual queries both half marginals of the restriction to the
equality events are `η h_p` with `η = 1 - (1 - 2^{-m})^6`, is proved in
`PrefixEqualityEvents.lean` (`deletion_marginals_iid`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open ReflectionCut

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

/-- The half index of a slot: itself in the half, its mirror otherwise. -/
def halfIndex (c : ReflectionCut V) (v : V) : c.Half :=
  if hv : v ∈ c.half then ⟨v, hv⟩ else ⟨c.flip v, (c.crosses v).2 hv⟩

theorem halfIndex_half (c : ReflectionCut V) (u : c.Half) : halfIndex c u.1 = u := by
  unfold halfIndex
  rw [dite_eq_left u.2]

theorem halfIndex_flip (c : ReflectionCut V) (u : c.Half) : halfIndex c (c.flip u.1) = u := by
  unfold halfIndex
  rw [dite_eq_right (c.flip_not_mem u.2)]
  exact Subtype.ext (c.flip_flip u.1)

/-- **The diagonal copy** `Diag_ι(h)`: half labels drawn from `h` and copied to the mirror
slots. -/
noncomputable def diagLaw (c : ReflectionCut V) (h : FiniteLaw (c.Half → X)) :
    FiniteLaw (V → X) :=
  h.map (fun x v => x (halfIndex c v))

/-- The cut form of the diagonal copy is `(F, G) ↦ h(F G)`. -/
theorem form_diagLaw (c : ReflectionCut V) (h : FiniteLaw (c.Half → X))
    (F G : (c.Half → X) → ℝ) :
    c.form (signedIntegral (diagLaw c h).weight) F G = h.expect (fun x => F x * G x) := by
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, diagLaw, FiniteLaw.expect_map]
  refine h.expect_congr fun x => ?_
  have h1 : (fun v : c.Half => x (halfIndex c v.1)) = x := funext fun v => by rw [halfIndex_half]
  have h2 : (fun v : c.Half => x (halfIndex c (c.flip v.1))) = x :=
    funext fun v => by rw [halfIndex_flip]
  simp only [Function.comp_apply, h1, h2]

/-- The diagonal copy is reflection positive at its cut. -/
theorem diagLaw_positive (c : ReflectionCut V) (h : FiniteLaw (c.Half → X)) :
    c.Positive (signedIntegral (diagLaw c h).weight) := by
  constructor
  · intro F G
    rw [form_diagLaw, form_diagLaw]
    exact h.expect_congr fun x => mul_comm _ _
  · intro F
    rw [form_diagLaw]
    exact h.expect_nonneg fun x => mul_self_nonneg _

/-- **Both half marginals of the deleted measure are `η h`.** -/
def DeletionMarginals (c : ReflectionCut V) (e : (V → X) → ℝ) (η : ℝ)
    (h : FiniteLaw (c.Half → X)) : Prop :=
  (∀ F : (c.Half → X) → ℝ, ∑ z, e z * F (fun v => z v.1) = η * h.expect F) ∧
    (∀ G : (c.Half → X) → ℝ, ∑ z, e z * G (fun v => z (c.flip v.1)) = η * h.expect G)

/-- The `L²(h)` norm of a half function. -/
noncomputable def halfL2 {c : ReflectionCut V} (h : FiniteLaw (c.Half → X))
    (F : (c.Half → X) → ℝ) : ℝ :=
  Real.sqrt (h.expect (fun x => F x ^ 2))

/-- Weighted Cauchy–Schwarz for nonnegative weights. -/
theorem abs_sum_weight_mul_le {Ω : Type*} [Fintype Ω] (e : Ω → ℝ) (he : ∀ z, 0 ≤ e z)
    (a b : Ω → ℝ) :
    |∑ z, e z * (a z * b z)| ≤
      Real.sqrt (∑ z, e z * a z ^ 2) * Real.sqrt (∑ z, e z * b z ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z => Real.sqrt (e z) * a z) (fun z => Real.sqrt (e z) * b z)
  have hc (z : Ω) : (Real.sqrt (e z) * a z) * (Real.sqrt (e z) * b z) = e z * (a z * b z) := by
    calc _ = Real.sqrt (e z) ^ 2 * (a z * b z) := by ring
      _ = _ := by rw [Real.sq_sqrt (he z)]
  simp only [hc, mul_pow, Real.sq_sqrt (he _)] at h
  have h' := Real.abs_le_sqrt h
  rwa [Real.sqrt_mul (Finset.sum_nonneg fun z _ => mul_nonneg (he z) (sq_nonneg _))] at h'

omit [DecidableEq X] in
/-- **A positive coupling is a contraction between its marginal `L²` spaces** (proof of
`thm:density:iid-prefix`(c)): `|E(F ⊗ G)| ≤ η ‖F‖_{L²(h)} ‖G‖_{L²(h)}`. -/
theorem deletion_form_le (c : ReflectionCut V) {e : (V → X) → ℝ} (he : ∀ z, 0 ≤ e z) {η : ℝ}
    (hη : 0 ≤ η) {h : FiniteLaw (c.Half → X)} (hm : DeletionMarginals c e η h)
    (F G : (c.Half → X) → ℝ) :
    |c.form (signedIntegral e) F G| ≤ η * (halfL2 h F * halfL2 h G) := by
  have hcs := abs_sum_weight_mul_le e he (fun z => F (fun v => z v.1))
    (fun z => G (fun v => z (c.flip v.1)))
  have hF := hm.1 (fun x => F x ^ 2)
  have hG := hm.2 (fun x => G x ^ 2)
  rw [hF, hG, Real.sqrt_mul hη, Real.sqrt_mul hη] at hcs
  have hηη : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη
  unfold halfL2
  calc |c.form (signedIntegral e) F G| = |∑ z, e z * (F (fun v => z v.1) *
        G (fun v => z (c.flip v.1)))| := rfl
    _ ≤ Real.sqrt η * Real.sqrt (h.expect fun x => F x ^ 2) *
        (Real.sqrt η * Real.sqrt (h.expect fun x => G x ^ 2)) := hcs
    _ = (Real.sqrt η * Real.sqrt η) * (Real.sqrt (h.expect fun x => F x ^ 2) *
        Real.sqrt (h.expect fun x => G x ^ 2)) := by ring
    _ = η * (Real.sqrt (h.expect fun x => F x ^ 2) * Real.sqrt (h.expect fun x => G x ^ 2)) := by
        rw [hηη]

omit [DecidableEq X] in
/-- **The symmetric and skew parts of the deleted measure have operator norm at most `η`**
between the half `L²(h)` spaces (`thm:density:iid-prefix`(c)); no symmetry of `E` is assumed. -/
theorem deletion_sym_skew_le (c : ReflectionCut V) {e : (V → X) → ℝ} (he : ∀ z, 0 ≤ e z)
    {η : ℝ} (hη : 0 ≤ η) {h : FiniteLaw (c.Half → X)} (hm : DeletionMarginals c e η h)
    (F G : (c.Half → X) → ℝ) :
    |(c.form (signedIntegral e) F G + c.form (signedIntegral e) G F) / 2| ≤
        η * (halfL2 h F * halfL2 h G) ∧
      |(c.form (signedIntegral e) F G - c.form (signedIntegral e) G F) / 2| ≤
        η * (halfL2 h F * halfL2 h G) := by
  have h1 := deletion_form_le c he hη hm F G
  have h2 := deletion_form_le c he hη hm G F
  rw [mul_comm (halfL2 h G)] at h2
  constructor
  · rw [abs_div, abs_two, div_le_iff₀ (by norm_num)]
    calc |c.form (signedIntegral e) F G + c.form (signedIntegral e) G F|
        ≤ |c.form (signedIntegral e) F G| + |c.form (signedIntegral e) G F| := abs_add_le _ _
      _ ≤ _ := by linarith
  · rw [abs_div, abs_two, div_le_iff₀ (by norm_num)]
    calc |c.form (signedIntegral e) F G - c.form (signedIntegral e) G F|
        ≤ |c.form (signedIntegral e) F G| + |c.form (signedIntegral e) G F| := abs_sub _ _
      _ ≤ _ := by linarith

/-- **The bracket of `thm:density:iid-prefix`(c)**: with `D = Diag_ι(h)` and `ν = μ - E`,
`[[μ + η D, ν], [ν^*, μ + η D]] ⪰_ι 0`. -/
theorem deletion_bracket (c : ReflectionCut V) (μ : FiniteLaw (V → X))
    (hμ : c.Positive (signedIntegral μ.weight)) {e : (V → X) → ℝ} (he : ∀ z, 0 ≤ e z) {η : ℝ}
    (hη : 0 ≤ η) {h : FiniteLaw (c.Half → X)} (hm : DeletionMarginals c e η h) :
    c.Bracket (signedIntegral μ.weight + η • signedIntegral (diagLaw c h).weight)
      (signedIntegral μ.weight - signedIntegral e)
      (signedIntegral μ.weight + η • signedIntegral (diagLaw c h).weight) := by
  have hL := hμ.add ((diagLaw_positive c h).smul hη)
  refine ⟨hL, hL, fun F G => ?_⟩
  have hsplitL : ∀ A B : (c.Half → X) → ℝ,
      c.form (signedIntegral μ.weight + η • signedIntegral (diagLaw c h).weight) A B =
        c.form (signedIntegral μ.weight) A B + η * h.expect (fun x => A x * B x) := by
    intro A B
    rw [← form_diagLaw]
    rfl
  have hsplitK : c.form (signedIntegral μ.weight - signedIntegral e) F G =
      c.form (signedIntegral μ.weight) F G - c.form (signedIntegral e) F G := rfl
  rw [hsplitL, hsplitL, hsplitK]
  -- the `μ` block: reflection positivity
  have hμFG : 0 ≤ c.form (signedIntegral μ.weight) F F +
      2 * c.form (signedIntegral μ.weight) F G + c.form (signedIntegral μ.weight) G G := by
    have hh := hμ.nonneg (F + G)
    rw [c.form_add_left, c.form_add_right, c.form_add_right, hμ.symmetric G F] at hh
    linarith
  -- the deleted block: the contraction
  have hE := deletion_form_le c he hη hm F G
  have hF0 : 0 ≤ h.expect (fun x => F x ^ 2) := h.expect_nonneg fun x => sq_nonneg _
  have hG0 : 0 ≤ h.expect (fun x => G x ^ 2) := h.expect_nonneg fun x => sq_nonneg _
  have hFF : h.expect (fun x => F x * F x) = halfL2 h F ^ 2 := by
    unfold halfL2
    rw [Real.sq_sqrt hF0]
    exact h.expect_congr fun x => by ring
  have hGG : h.expect (fun x => G x * G x) = halfL2 h G ^ 2 := by
    unfold halfL2
    rw [Real.sq_sqrt hG0]
    exact h.expect_congr fun x => by ring
  rw [hFF, hGG]
  have hab : 2 * (halfL2 h F * halfL2 h G) ≤ halfL2 h F ^ 2 + halfL2 h G ^ 2 := by
    nlinarith [sq_nonneg (halfL2 h F - halfL2 h G)]
  have hEle : c.form (signedIntegral e) F G ≤ η * (halfL2 h F * halfL2 h G) :=
    (le_abs_self _).trans hE
  nlinarith [mul_le_mul_of_nonneg_left hab hη]

end Sarkozy.DensityMoments
