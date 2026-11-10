module

public import Sarkozy.EnvelopeInputs.FoldedExpansion
public import Sarkozy.TheoremC.Defs

/-!
# The folded laws are positive records (`lem:record:folded-energy` (b))

`paper/sections/08_scale_comparison.tex`, `lem:record:folded-energy` (b): the folded laws are
admissible positive measures, "since a fold only copies an existing slot". WP's
`Comparison.FoldedEnergy` states that part (b) is not formalized. Here it is, for the folded
factors used in `abs_tensor_sum_le_folded`: the diagonal law of a half marginal of a nonnegative
law `K`.

* `sum_halfMarginalPlus_mul`, `sum_halfMarginalMinus_mul`: integrating against a half marginal
  is integrating the half restriction under `K`;
* `diagonalLaw_halfMarginalPlus_one`, `…Minus_one`: the folded factor has the mass of `K`;
* `diagonalLaw_halfMarginalPlus_marginal`, `…Minus_marginal`: its one-slot marginal at `v` is the
  one-slot marginal of `K` at `v` or at `ι v`;
* `isPositiveRecord_foldPlus`, `isPositiveRecord_foldMinus`: the folded factors of a positive
  record (`TheoremC.IsPositiveRecord`: nonnegative with uniform one-slot marginals) are positive
  records of the same mass.

So in the folded-energy bounds of `SharpFirstFolded` and `EnvelopeSharpFolded` every folded factor
other than `μ_𝔟` is a positive record whenever its piece is one; for the components `κ_s` of a
sharp decomposition this needs the `κ_s` to be positive records (see the report).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Comparison Sarkozy.TheoremC ReflectionCut

section General

variable {V : Type*} [Fintype V] [DecidableEq V] {X : Type*} [Fintype X] [DecidableEq X]

/-- `∑_x m₊(x) G(x) = ∫ G(z₊) dK` for the plus-half marginal `m₊` of `K`. -/
theorem sum_halfMarginalPlus_mul (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (G : (c.Half → X) → ℝ) :
    ∑ x, halfMarginalPlus c K x * G x = K (fun z => G (fun v : c.Half => z v.1)) := by
  have he : (fun z : V → X => G (fun v : c.Half => z v.1)) =
      ∑ x, G x • (fun z : V → X => if (fun v : c.Half => z v.1) = x then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [he, map_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [map_smul, smul_eq_mul, mul_comm]; rfl

/-- `∑_y m₋(y) G(y) = ∫ G(z₋) dK` for the minus-half marginal `m₋` of `K`. -/
theorem sum_halfMarginalMinus_mul (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (G : (c.Half → X) → ℝ) :
    ∑ y, halfMarginalMinus c K y * G y = K (fun z => G (fun v : c.Half => z (c.flip v.1))) := by
  have he : (fun z : V → X => G (fun v : c.Half => z (c.flip v.1))) =
      ∑ y, G y • (fun z : V → X =>
        if (fun v : c.Half => z (c.flip v.1)) = y then (1 : ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [he, map_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [map_smul, smul_eq_mul, mul_comm]; rfl

omit [DecidableEq X] in
theorem diagonalLaw_apply (c : ReflectionCut V) (m : (c.Half → X) → ℝ) (F : (V → X) → ℝ) :
    c.diagonalLaw m F = ∑ x, m x * F (c.join x x) := rfl

/-- The plus folded factor has the mass of `K`. -/
theorem diagonalLaw_halfMarginalPlus_one (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    c.diagonalLaw (halfMarginalPlus c K) (fun _ => 1) = K (fun _ => 1) := by
  rw [diagonalLaw_apply]
  exact sum_halfMarginalPlus_mul c K (fun _ => 1)

/-- The minus folded factor has the mass of `K`. -/
theorem diagonalLaw_halfMarginalMinus_one (c : ReflectionCut V) (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    c.diagonalLaw (halfMarginalMinus c K) (fun _ => 1) = K (fun _ => 1) := by
  rw [diagonalLaw_apply]
  exact sum_halfMarginalMinus_mul c K (fun _ => 1)

/-- The one-slot marginals of the plus folded factor: at a plus slot `v`, that of `K` at `v`; at
a minus slot `v`, that of `K` at `ι v` ("a fold only copies an existing slot"). -/
theorem diagonalLaw_halfMarginalPlus_marginal (c : ReflectionCut V)
    (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (v : V) (g : X → ℝ) :
    c.diagonalLaw (halfMarginalPlus c K) (fun z => g (z v)) =
      if v ∈ c.half then K (fun z => g (z v)) else K (fun z => g (z (c.flip v))) := by
  rw [diagonalLaw_apply]
  split_ifs with hv
  · have := sum_halfMarginalPlus_mul c K (fun x => g (x ⟨v, hv⟩))
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    exact c.join_plus x x ⟨v, hv⟩
  · have hfv : c.flip v ∈ c.half := (c.crosses v).mpr hv
    have := sum_halfMarginalPlus_mul c K (fun x => g (x ⟨c.flip v, hfv⟩))
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    have h := c.join_minus x x ⟨c.flip v, hfv⟩
    simp only [c.flip_flip] at h
    exact h

/-- The one-slot marginals of the minus folded factor. -/
theorem diagonalLaw_halfMarginalMinus_marginal (c : ReflectionCut V)
    (K : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (v : V) (g : X → ℝ) :
    c.diagonalLaw (halfMarginalMinus c K) (fun z => g (z v)) =
      if v ∈ c.half then K (fun z => g (z (c.flip v))) else K (fun z => g (z v)) := by
  rw [diagonalLaw_apply]
  split_ifs with hv
  · have := sum_halfMarginalMinus_mul c K (fun y => g (y ⟨v, hv⟩))
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 2
    exact c.join_plus y y ⟨v, hv⟩
  · have hfv : c.flip v ∈ c.half := (c.crosses v).mpr hv
    have h1 := sum_halfMarginalMinus_mul c K (fun y => g (y ⟨c.flip v, hfv⟩))
    have h2 : ∑ y, halfMarginalMinus c K y * g (c.join y y v) =
        ∑ y, halfMarginalMinus c K y * g (y ⟨c.flip v, hfv⟩) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      congr 2
      have h := c.join_minus y y ⟨c.flip v, hfv⟩
      simp only [c.flip_flip] at h
      exact h
    rw [h2, h1]
    simp only [c.flip_flip]

omit [DecidableEq X] in
/-- The folded factors of a nonnegative law are nonnegative. -/
theorem diagonalLaw_nonneg (c : ReflectionCut V) {m : (c.Half → X) → ℝ} (hm : ∀ x, 0 ≤ m x)
    (F : (V → X) → ℝ) (hF : ∀ z, 0 ≤ F z) : 0 ≤ c.diagonalLaw m F := by
  rw [diagonalLaw_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (hF _)

end General

section Records

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **`lem:record:folded-energy` (b), plus side**: the plus folded factor of a positive record is
a positive record of the same mass. -/
theorem isPositiveRecord_foldPlus (c : ReflectionCut Slot) {K : SlotMeasure X}
    (hK : IsPositiveRecord K) :
    IsPositiveRecord (c.diagonalLaw (halfMarginalPlus c K)) ∧
      mass (c.diagonalLaw (halfMarginalPlus c K)) = mass K := by
  have hmass : mass (c.diagonalLaw (halfMarginalPlus c K)) = mass K :=
    diagonalLaw_halfMarginalPlus_one c K
  refine ⟨⟨fun F hF => diagonalLaw_nonneg c (halfMarginalPlus_nonneg c hK.1) F hF,
    fun v g => ?_⟩, hmass⟩
  rw [diagonalLaw_halfMarginalPlus_marginal, hmass]
  split_ifs
  · exact hK.2 v g
  · exact hK.2 (c.flip v) g

/-- **`lem:record:folded-energy` (b), minus side.** -/
theorem isPositiveRecord_foldMinus (c : ReflectionCut Slot) {K : SlotMeasure X}
    (hK : IsPositiveRecord K) :
    IsPositiveRecord (c.diagonalLaw (halfMarginalMinus c K)) ∧
      mass (c.diagonalLaw (halfMarginalMinus c K)) = mass K := by
  have hmass : mass (c.diagonalLaw (halfMarginalMinus c K)) = mass K :=
    diagonalLaw_halfMarginalMinus_one c K
  refine ⟨⟨fun F hF => diagonalLaw_nonneg c (halfMarginalMinus_nonneg c hK.1) F hF,
    fun v g => ?_⟩, hmass⟩
  rw [diagonalLaw_halfMarginalMinus_marginal, hmass]
  split_ifs
  · exact hK.2 (c.flip v) g
  · exact hK.2 v g

end Records

end Sarkozy.EnvelopeInputs
