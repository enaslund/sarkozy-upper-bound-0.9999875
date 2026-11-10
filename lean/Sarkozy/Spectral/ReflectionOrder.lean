module

public import Sarkozy.Spectral.GlueCut
public import Sarkozy.Reflection.Transport

/-!
# From a spectral lower bound to reflection order

The passage used in `paper/sections/25_upper_reference.tex`, the proof of
`lem:upper-reference-rp`(i), from (V1)/(V3) to an inequality of laws. The comparison
law is the diagonal copy of the **half graph law**, not the actual half marginal.

`ReflectionCut.diagonalHalf` duplicates a half configuration. Its cut form is the
`L²` inner product. `Spectral.cutOp_below` turns a lower bound for the normalized
cut operator into the precise `ReflectionCut.Below` needed by the completion laws.
No count comparison or loss in the spectral constant is required.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.ReflectionCut

variable {U X : Type*} [Fintype U] [DecidableEq U] [Fintype X]

/-- Duplicate the configuration sampled from a law on the plus half. -/
noncomputable def diagonalHalf (c : ReflectionCut U) (μ : FiniteLaw (c.Half → X)) :
    ((U → X) → ℝ) →ₗ[ℝ] ℝ :=
  c.diagonalLaw μ.weight

/-- The reflection form of the diagonal half law is the `L²(μ)` inner product. -/
theorem form_diagonalHalf (c : ReflectionCut U) (μ : FiniteLaw (c.Half → X))
    (f g : (c.Half → X) → ℝ) :
    c.form (c.diagonalHalf μ) f g = μ.expect (fun x => f x * g x) :=
  c.form_diagonalLaw μ.weight f g

/-- A diagonal half law is reflection positive at its defining cut. -/
theorem diagonalHalf_positive (c : ReflectionCut U) (μ : FiniteLaw (c.Half → X)) :
    c.Positive (c.diagonalHalf μ) := c.diagonalLaw_positive μ.nonneg

/-- For a symmetric reflection form, a scalar lower bound relative to `μ` is
exactly reflection order against the diagonal copy of `μ`. -/
theorem below_diagonalHalf_iff (c : ReflectionCut U) (μ : FiniteLaw (c.Half → X))
    (L : ((U → X) → ℝ) →ₗ[ℝ] ℝ)
    (hsymm : ∀ f g, c.form L f g = c.form L g f) (a : ℝ) :
    c.Below (-a • c.diagonalHalf μ) L ↔
      ∀ f, -a * μ.expect (fun x => f x ^ 2) ≤ c.form L f f := by
  constructor
  · intro h f
    have := h.form_le f
    change -a * c.form (c.diagonalHalf μ) f f ≤ c.form L f f at this
    simpa only [form_diagonalHalf, ← pow_two] using this
  · intro h
    constructor
    · intro f g
      change c.form L f g - -a * c.form (c.diagonalHalf μ) f g =
        c.form L g f - -a * c.form (c.diagonalHalf μ) g f
      rw [hsymm f g, (c.diagonalHalf_positive μ).symmetric f g]
    · intro f
      change 0 ≤ c.form L f f - -a * c.form (c.diagonalHalf μ) f f
      rw [form_diagonalHalf]
      simpa only [← pow_two] using sub_nonneg.mpr (h f)

end Sarkozy.ReflectionCut

namespace Sarkozy.Spectral

open Sarkozy.Cuts Sarkozy.Labellings Sarkozy.InfluenceGlue

variable {U F : Type*} [Fintype U] [DecidableEq U]
  [Field F] [Fintype F] [DecidableEq F] (D : SpecData U)

/-- The quadratic form of the graph law is the already normalized cut form. -/
theorem reflectionForm_eq_cutForm (hne : (injLabellings F D.G).Nonempty)
    (f g : (D.cut.Half → F) → ℝ) :
    D.cut.form (signedIntegral (graphLaw D.G hne).weight) f g = D.cutForm hne f g :=
  D.expect_cut_form hne f g

/-- **The exact bridge from spectral bounds to reflection order.** The spectral
criterion's lower bound gives the order relative to the duplicated half graph law. -/
theorem cutOp_below (hne : (injLabellings F D.G).Nonempty) (a : ℝ)
    (h : ∀ v : EuclideanSpace ℝ (D.cut.Half → F),
      -a * ‖v‖ ^ 2 ≤ ⟪v, cutOp D hne v⟫_ℝ) :
    D.cut.Below (-a • D.cut.diagonalHalf (D.halfLaw hne))
      (signedIntegral (graphLaw D.G hne).weight) := by
  apply (D.cut.below_diagonalHalf_iff _ _ (fun f g => ?_) a).mpr
  · intro f
    rw [reflectionForm_eq_cutForm]
    have hf := h (l2Map (D.halfLaw hne) f)
    rwa [norm_l2Map_sq, (cutOp_form D hne f f).1] at hf
  · simp only [reflectionForm_eq_cutForm]
    exact D.cutForm_symm hne f g

end Sarkozy.Spectral
