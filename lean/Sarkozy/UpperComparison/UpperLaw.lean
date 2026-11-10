module

public import Sarkozy.UpperComparison.Acceptance
public import Sarkozy.UpperComparison.Construction

@[expose] public section

/-!
# The components of the upper comparison law: acceptance and uniform marginals

`paper/sections/26_upper_comparison.tex`, `prop:record:upper`(i): "every retained record accepts
`𝓔₆` …; under the normalized accepted part every query pair is a strict-square pair at every
prime of `𝔅`, which is (R5)", and "its one-slot marginals are uniform". These are the fields
`accept` and `unif` of `(CP4)(a)` (`TheoremCParam.ComparisonLaw`) for the components of an upper
block, which are the retained records of `ν̃_𝔅` (`Construction.upperNuTilde`) on V1's block
field laws.

* `upperNu_component_accepts`: every component with nonzero weight (a kept or changed record)
  accepts every query of `𝓔₆` at every prime of the block. Kept records: `Acceptance`; changed
  records: the acceptance of the replacing laws, a hypothesis ((F7), `prop:dense-comparison`(a),
  `prop:le-mixture`).
* `upperNu_component_uniform`: every component has uniform one-slot marginals. Kept records: V1's
  `emit_uniform` with the vertex uniformity of the block graph laws; changed records: a
  hypothesis (the replacing laws are invariant under the square-affine maps).
* `upperNu_component_affine`: every component is invariant under the square-affine maps (R3).
* `upper_change_normalized`: `ν_𝔅 - μ_𝔅 = ∑_ρ P_μ(r)⁻¹ Δ_ρ`, the field `change` of `(CP4)(b)`.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.Labellings Sarkozy.PartV

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- A kept record accepts: two-layer records by `TwoLayerEdgeAccepts`, folded records by
`FoldedEdgeAccepts`. -/
theorem kept_record_accepts (hne : UpperNonempty pr) (ρ : UpIdx) (hρ : upperFate ρ = .kept)
    {z : Slot → BlockLabel pr} (hz : (upComponent (upperBlockFieldLaws pr hne) ρ).weight z ≠ 0)
    (j : Chamber) (i : ι) :
    quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · have hacc : FoldedEdgeAccepts t φ := by
      by_contra h
      simp only [upperFate, h, ↓reduceIte] at hρ
      exact absurd hρ (by decide)
    exact kept_folded_accepts pr hne t φ hacc hz j i
  · have hacc : TwoLayerEdgeAccepts t φ := by
      by_contra h
      simp only [upperFate, h, ↓reduceIte] at hρ
      split_ifs at hρ
    exact kept_two_layer_accepts pr hne t φ hacc hz j i

/-- **(CP4)(a), acceptance, for an upper block** (`prop:record:upper`(i)): every retained record of
`ν̃_𝔅` (nonzero weight) charges only labellings whose query differences are nonzero squares at
every prime of the block. The acceptance of the replacing laws of the changed records is a
hypothesis. -/
theorem upperNu_component_accepts (hne : UpperNonempty pr) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → BlockLabel pr)) (r : ℝ)
    (hnew : ∀ ρ, upperFate ρ = .changed → ∀ z, (new ρ).weight z ≠ 0 → ∀ (j : Chamber) (i : ι),
      quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1)
    (ρ : UpIdx) (hρ : retainedCoeff W r ρ ≠ 0) {z : Slot → BlockLabel pr}
    (hz : (compLaw (upperBlockFieldLaws pr hne) new ρ).weight z ≠ 0) (j : Chamber) (i : ι) :
    quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  unfold compLaw at hz
  unfold retainedCoeff at hρ
  cases h : upperFate ρ
  · rw [h] at hz
    simp only [reduceCtorEq, ↓reduceIte] at hz
    exact kept_record_accepts pr hne ρ h hz j i
  · rw [h] at hz
    simp only [↓reduceIte] at hz
    exact hnew ρ h z hz j i
  · rw [h] at hρ
    simp at hρ

/-- **(CP4)(a), uniform one-slot marginals, for an upper block**: every component of `ν̃_𝔅` has
uniform one-slot marginals; for the replacing laws this is a hypothesis. -/
theorem upperNu_component_uniform (hne : UpperNonempty pr)
    (new : UpIdx → FiniteLaw (Slot → BlockLabel pr))
    (hnew : ∀ ρ, upperFate ρ = .changed → HasUniformMarginals (new ρ)) (ρ : UpIdx) :
    HasUniformMarginals (compLaw (upperBlockFieldLaws pr hne) new ρ) := by
  unfold compLaw
  split_ifs with h
  · exact hnew ρ h
  · rcases ρ with ⟨b, t, φ⟩
    cases b
    · exact emit_uniform _ _ (blockGraphLaw_vertex_uniform pr _ (hne.one _ _))
    · exact emit_uniform _ _ (blockGraphLaw_vertex_uniform pr _ (hne.two _ _))

/-- **(R3) for the components of an upper block** (`prop:record:upper`(i): `ν_𝔅` is invariant
under the maps of (R3)): every component of `ν̃_𝔅` is invariant under the square-affine maps
`z_{v,p} ↦ α_p z_{v,p} + β_p` with `χ_p(α_p) = 1`, prime by prime. Kept records: V1's
`blockGraphLaw_expect_affine`; changed records: the invariance of the replacing laws, a
hypothesis ((F7) "invariant under the square-affine maps", `prop:dense-comparison`(a)). -/
theorem upperNu_component_affine (hne : UpperNonempty pr)
    (new : UpIdx → FiniteLaw (Slot → BlockLabel pr)) (α β : BlockLabel pr)
    (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (hnew : ∀ ρ, upperFate ρ = .changed → ∀ H : (Slot → BlockLabel pr) → ℝ,
      (new ρ).expect (fun z => H (fun v i => α i * z v i + β i)) = (new ρ).expect H)
    (ρ : UpIdx) (H : (Slot → BlockLabel pr) → ℝ) :
    (compLaw (upperBlockFieldLaws pr hne) new ρ).expect
        (fun z => H (fun v i => α i * z v i + β i)) =
      (compLaw (upperBlockFieldLaws pr hne) new ρ).expect H := by
  unfold compLaw
  split_ifs with h
  · exact hnew ρ h H
  · rcases ρ with ⟨b, t, φ⟩
    cases b
    · simp only [upComponent, expect_emit]
      exact blockGraphLaw_expect_affine pr _ (hne.one _ _) α β hα (fun y => H (y ∘ _))
    · simp only [upComponent, expect_emit]
      exact blockGraphLaw_expect_affine pr _ (hne.two _ _) α β hα (fun y => H (y ∘ _))

/-- **The change of `(CP4)(b)` for an upper block** (`prop:record:upper`(i)): with the components
`compLaw ρ` of weight `retainedCoeff ρ / P_μ(r)` and the reference `μ_𝔅` (V1's `upperReference`),
`ν_𝔅 - μ_𝔅 = ∑_ρ P_μ(r)⁻¹ Δ_ρ`: the field `change` of `TheoremCParam.ComparisonLaw` with the
record changes `Δ_ρ` of `Construction.recordChange`, divided by the common normalizer `P_μ(r)`
(the normalizer of `ν_𝔅` is that of `μ_𝔅`, not its own mass). -/
theorem upper_change_normalized {X : Type*} [Fintype X] [DecidableEq X] (F : UpperFieldLaws X)
    (W : UpperWeights) (new : UpIdx → FiniteLaw (Slot → X)) {r : ℝ} (hr : 0 ≤ r) :
    (∑ ρ, (retainedCoeff W r ρ / upPoly W r) • signedIntegral (compLaw F new ρ).weight) -
        signedIntegral (upperReference F W hr).weight =
      ∑ ρ, (upPoly W r)⁻¹ • recordChange F W new r ρ := by
  have href : signedIntegral (upperReference F W hr).weight =
      (upPoly W r)⁻¹ • upperTilde F W r := by
    unfold upperReference upperTilde
    rw [signedIntegral_weightedCompletion, sum_upCoeff]
  have hnu : (∑ ρ, (retainedCoeff W r ρ / upPoly W r) • signedIntegral (compLaw F new ρ).weight) =
      (upPoly W r)⁻¹ • upperNuTilde F W new r := by
    unfold upperNuTilde tildeMeasure
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [smul_smul, div_eq_inv_mul]
  rw [href, hnu, ← smul_sub (upPoly W r)⁻¹ (upperNuTilde F W new r) (upperTilde F W r),
    upperNuTilde_sub, Finset.smul_sum]

end Sarkozy.UpperComparison
