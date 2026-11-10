module

public import Sarkozy.UpperComparison.Prices
public import Sarkozy.Structured.CenteredTransport

@[expose] public section

/-!
# From the field-level norm bounds to the brackets of `(CP4)(b)`

`paper/sections/26_upper_comparison.tex`, paragraph "The repair": "The emission acts within each
layer, so a test function of an emitted half is a test function of the field half: the emission
preserves the half marginals at `ι` and cannot increase an operator norm between them"; used in
`prop:record:upper`(i) for every changed record.

The analytic propositions (`ForestRecords`, `DenseLaws`, `LEMixture`) bound the symmetric and skew
parts of a change as bilinear forms of the field halves, relative to the actual half marginal
`m₀ = (1 + u₀)ν` (`centredForm`, `mnrm`). The brackets of `(CP4)(b)` are statements about the cut
form at `ι` of the emitted change and its half marginal `m` (`changed_record_bracket`). This file
proves the step between them:
* `form_symPart`, `form_skewPart`: the cut forms of the symmetric and skew parts at a cut are the
  symmetrized and antisymmetrized cut forms;
* `bracket_of_field_bound`, `sym_bracket_of_field_bound`, `skew_bracket_of_field_bound`: if the cut
  form of the change is a field-level form `B` read through the emission `e` of a half
  (`hform`), and the half marginal at the cut is the image of `m₀` (`hnorm`), then a bound on `B`
  (respectively on its symmetric or skew part) relative to `m₀` gives the bracket with that
  coefficient.

The two identities `hform`, `hnorm` express that the emitted record reads each half through the
emission; they are hypotheses here, stated for an arbitrary cut.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.RecordExpansion Sarkozy.Recentering Sarkozy.Structured

variable {W Y : Type*} [Fintype W] [DecidableEq W]

/-- The cut form of the symmetric part at a cut is the symmetrized cut form. -/
theorem form_symPart (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → Y) → ℝ) :
    c.form (symPart c L) F G = (c.form L F G + c.form L G F) / 2 := by
  have h := form_reflect c L F G
  unfold symPart
  unfold ReflectionCut.form at h ⊢
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  rw [h]
  ring

/-- The cut form of the skew part at a cut is the antisymmetrized cut form. -/
theorem form_skewPart (c : ReflectionCut W) (L : ((W → Y) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (c.Half → Y) → ℝ) :
    c.form (skewPart c L) F G = (c.form L F G - c.form L G F) / 2 := by
  have h := form_reflect c L F G
  unfold skewPart
  unfold ReflectionCut.form at h ⊢
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
  rw [h]
  ring

variable [Fintype Y]

/-- **The emission cannot increase an operator norm.** If the cut form of `Δ` is the field-level
form `B` read through the emission `e` of a half (`hform`), the half marginal `m` at the cut is
the image of `m₀ = (1 + u₀)ν` (`hnorm`), and `|B(φ, ψ)| ≤ C ‖φ‖_{m₀} ‖ψ‖_{m₀}`, then
`(C Diag(m)  Δ; Δ*  C Diag(m)) ⪰_c 0`. -/
theorem bracket_of_field_bound (c : ReflectionCut W) {m : (c.Half → Y) → ℝ} (hm : ∀ x, 0 ≤ m x)
    {X : Type*} [Fintype X] (ν : FiniteLaw X) (u0 : X → ℝ) (e : X → (c.Half → Y))
    (Δ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (B : (X → ℝ) → (X → ℝ) → ℝ)
    (hform : ∀ F G, c.form Δ F G = B (F ∘ e) (G ∘ e))
    (hnorm : ∀ F : (c.Half → Y) → ℝ, Real.sqrt (∑ x, m x * (F x * F x)) = mnrm ν u0 (F ∘ e))
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ φ ψ, |B φ ψ| ≤ C * mnrm ν u0 φ * mnrm ν u0 ψ) :
    c.Bracket (C • c.diagonalLaw m) Δ (C • c.diagonalLaw m) := by
  apply bracket_of_norm_bound c hm hC
  intro F G
  rw [hform, hnorm, hnorm]
  exact hB _ _

/-- **The symmetric part**: a bound `C` on the symmetric part `(B(φ,ψ) + B(ψ,φ))/2` relative to
`m₀` (for instance `ρ_old + s_new` of `forest_records_a`, `d_s` of `dense_comparison_b`, the `d_s`
of `le_mixture_change`, applied to `B = 𝒞_{K'} - 𝒞_O`) gives the bracket of the symmetric part
`ζ^s = Sym_c Δ` with coefficient `C`. -/
theorem sym_bracket_of_field_bound (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm : ∀ x, 0 ≤ m x) {X : Type*} [Fintype X] (ν : FiniteLaw X) (u0 : X → ℝ)
    (e : X → (c.Half → Y)) (Δ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (B : (X → ℝ) → (X → ℝ) → ℝ)
    (hform : ∀ F G, c.form Δ F G = B (F ∘ e) (G ∘ e))
    (hnorm : ∀ F : (c.Half → Y) → ℝ, Real.sqrt (∑ x, m x * (F x * F x)) = mnrm ν u0 (F ∘ e))
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ φ ψ, |(B φ ψ + B ψ φ) / 2| ≤ C * mnrm ν u0 φ * mnrm ν u0 ψ) :
    c.Bracket (C • c.diagonalLaw m) (symPart c Δ) (C • c.diagonalLaw m) := by
  apply bracket_of_norm_bound c hm hC
  intro F G
  rw [form_symPart, hform, hform, hnorm, hnorm]
  exact hB _ _

/-- **The skew part**: a bound `C` on `(B(φ,ψ) - B(ψ,φ))/2` relative to `m₀` (`a_new`, `d_a`)
gives the bracket of the skew part `ζ^a = Skew_c Δ` with coefficient `C`. -/
theorem skew_bracket_of_field_bound (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm : ∀ x, 0 ≤ m x) {X : Type*} [Fintype X] (ν : FiniteLaw X) (u0 : X → ℝ)
    (e : X → (c.Half → Y)) (Δ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ) (B : (X → ℝ) → (X → ℝ) → ℝ)
    (hform : ∀ F G, c.form Δ F G = B (F ∘ e) (G ∘ e))
    (hnorm : ∀ F : (c.Half → Y) → ℝ, Real.sqrt (∑ x, m x * (F x * F x)) = mnrm ν u0 (F ∘ e))
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ φ ψ, |(B φ ψ - B ψ φ) / 2| ≤ C * mnrm ν u0 φ * mnrm ν u0 ψ) :
    c.Bracket (C • c.diagonalLaw m) (skewPart c Δ) (C • c.diagonalLaw m) := by
  apply bracket_of_norm_bound c hm hC
  intro F G
  rw [form_skewPart, hform, hform, hnorm, hnorm]
  exact hB _ _

end Sarkozy.UpperComparison
