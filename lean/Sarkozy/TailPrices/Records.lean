module

public import Sarkozy.TailPrices.Accepted
public import Sarkozy.ComparisonLawPaper.Upper
public import Sarkozy.Labellings.GraphAutomorphism

@[expose] public section

/-!
# The records of the tail law at one prime (`lem:tail-prices`(i),(ii))

`paper/sections/27_tail_index.tex`, `lem:tail-prices`, proof of (i),(ii): "From here the proof of
`prop:record:upper`(i), its admissibility paragraph included, applies to the atom `{p}`". W8
(`Sarkozy.UpperComparison`) proves the record facts of `prop:record:upper`(i) on V1's block field
laws `upperBlockFieldLaws pr hne`; the tail law at `p` is V1's upper reference on the field laws
`tailFieldLaws p hne` at the single prime `p` (`PartV.tailLaw`). This file proves the same facts for
the tail field laws (labels in `ZMod p`, either class modulo `4`):

* `tail_upComponent_symmetric`: every record is symmetric at the reserved cut `ι` (two-layer
  records by the layer interchange, folded records by V3's `isSymmetricAt_emit`);
* `tail_kept_accepts`: a kept record (`upperFate ρ = kept`, edge acceptance of `𝓔₆`) accepts every
  query of `𝓔₆` at `p`;
* `tail_component_expect_affine`, `tail_component_invariant`: every record is square-affine
  invariant, and `tail_component_uniform`: has uniform one-slot marginals;
* `affineInvariant_of_expect`: invariance in expectation form gives the pointwise form;
* `tail_envelope`: `Diag_ι(m_+(Π_ρ))` is a probability law, diagonal at `ι`, with uniform one-slot
  marginals;
* `tail_skew_recordChange_deleted`, `tail_deleted_bracket`: a deleted record is charged its mass
  in the symmetric total only.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)

/-- **A two-layer record of the tail law is symmetric at `ι`**. -/
theorem tail_twoLayer_symmetric (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    IsSymmetricAt reservedCut
      (signedIntegral (upComponent (tailFieldLaws p hne) (true, ⟨t, φ⟩)).weight) := by
  apply LinearMap.ext
  intro f
  rw [reflect_apply, ← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral]
  change (emit (graphLaw (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))
      (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).expect (fun z => f (z ∘ reservedCut.flip)) =
    (emit (graphLaw (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))
      (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).expect f
  rw [expect_emit, expect_emit]
  have hcomp : ∀ y : t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p,
      (y ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2)) ∘ reservedCut.flip =
        (y ∘ upLayerSwap _ _) ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2) := by
    intro y
    funext v
    simp only [Function.comp_apply, upEmission_reserved]
  simp only [hcomp]
  exact graphLaw_expect_comp _ (hne.two _ _) (upLayerSwap _ _)
    (upLayerSwap_automorphism _ _) (fun y => f (y ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2)))

/-- **Every record of the tail law is symmetric at `ι`**. -/
theorem tail_upComponent_symmetric (ρ : UpIdx) :
    IsSymmetricAt reservedCut (signedIntegral (upComponent (tailFieldLaws p hne) ρ).weight) := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact folded_symmetric _ t φ
  · exact tail_twoLayer_symmetric p hne t φ

/-- **(R5) for a kept two-layer record of the tail law**. -/
theorem tail_kept_two_layer_accepts (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (hacc : TwoLayerEdgeAccepts t φ) {z : Slot → ZMod p}
    (hz : (upComponent (tailFieldLaws p hne) (true, ⟨t, φ⟩)).weight z ≠ 0) (j : Chamber) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  change (emit (graphLaw (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))
    (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 at hz
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  obtain ⟨-, hedge⟩ := graphLaw_support _ _ hy
  simp only [fieldGraph, mem_twoLayerGraph, mem_univ, forall_const] at hedge
  have h := hedge ((t.1.pat φ.1 0, t.2.pat φ.2 j, 0), (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 1))
    (hacc j)
  have h1 : upEmission (t.1.pat φ.1) (t.2.pat φ.2) (queryTarget j) =
      (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 1) := by
    change (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), layerFin 1) = _
    rw [layerFin_one, rot_eq_chamberRotation]
  have h2 : upEmission (t.1.pat φ.1) (t.2.pat φ.2) (querySource j) =
      (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) := by
    change (t.1.pat φ.1 0, t.2.pat φ.2 j, layerFin 0) = _
    rw [layerFin_zero]
  rw [Function.comp_apply, Function.comp_apply, h1, h2]
  exact h

/-- **(R5) for a kept folded record of the tail law**. -/
theorem tail_kept_folded_accepts (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (hacc : FoldedEdgeAccepts t φ) {z : Slot → ZMod p}
    (hz : (upComponent (tailFieldLaws p hne) (false, ⟨t, φ⟩)).weight z ≠ 0) (j : Chamber) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  change (emit (graphLaw (fieldGraph t.1.field t.2.field (Fin 1)) (hne.one _ _))
    (upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 at hz
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  obtain ⟨-, hedge⟩ := graphLaw_support _ _ hy
  simp only [fieldGraph, mem_twoLayerGraph, mem_univ, forall_const] at hedge
  have h := hedge ((t.1.pat φ.1 0, t.2.pat φ.2 j, 0), (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 0))
    (hacc j)
  have h1 : upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2) (queryTarget j) =
      (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 0) := by
    change (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), 0) = _
    rw [rot_eq_chamberRotation]
  have h2 : upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2) (querySource j) =
      (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) := rfl
  rw [Function.comp_apply, Function.comp_apply, h1, h2]
  exact h

/-- **A kept record of the tail law accepts `𝓔₆`** (`lem:tail-prices`(i): every retained record
accepts `𝓔₆`). -/
theorem tail_kept_accepts (ρ : UpIdx) (hρ : upperFate ρ = .kept) {z : Slot → ZMod p}
    (hz : (upComponent (tailFieldLaws p hne) ρ).weight z ≠ 0) (j : Chamber) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · have hacc : FoldedEdgeAccepts t φ := by
      by_contra h
      simp only [upperFate, h, ↓reduceIte] at hρ
      exact absurd hρ (by decide)
    exact tail_kept_folded_accepts p hne t φ hacc hz j
  · have hacc : TwoLayerEdgeAccepts t φ := by
      by_contra h
      simp only [upperFate, h, ↓reduceIte] at hρ
      split_ifs at hρ
    exact tail_kept_two_layer_accepts p hne t φ hacc hz j

/-- **Every record of the tail law is square-affine invariant** (expectation form). -/
theorem tail_component_expect_affine (ρ : UpIdx) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) (H : (Slot → ZMod p) → ℝ) :
    (upComponent (tailFieldLaws p hne) ρ).expect (fun z => H (fun v => α * z v + β)) =
      (upComponent (tailFieldLaws p hne) ρ).expect H := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · simp only [upComponent, expect_emit]
    exact graphLaw_expect_affine _ (hne.one _ _) hα β (fun y => H (y ∘ _))
  · simp only [upComponent, expect_emit]
    exact graphLaw_expect_affine _ (hne.two _ _) hα β (fun y => H (y ∘ _))

variable {p} in
/-- **Pointwise invariance from invariance in expectation**. -/
theorem affineInvariant_of_expect (ν : FiniteLaw (Slot → ZMod p))
    (h : ∀ α : ZMod p, quadraticChar (ZMod p) α = 1 → ∀ (β : ZMod p) (H : (Slot → ZMod p) → ℝ),
      ν.expect (fun z => H (fun v => α * z v + β)) = ν.expect H) :
    AffineInvariant p ν.weight := by
  intro α β hα z
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  set y : Slot → ZMod p := fun w => α * z w + β with hy
  have hH := h α hα β (fun z' => if z' = y then 1 else 0)
  have hiff : ∀ z' : Slot → ZMod p, ((fun v => α * z' v + β) = y) ↔ z' = z := by
    intro z'
    constructor
    · intro hz
      funext v
      have hv := congrFun hz v
      simp only [hy] at hv
      exact mul_left_cancel₀ hα0 (add_right_cancel hv)
    · rintro rfl
      rfl
  have hl : ν.expect (fun z' => if (fun v => α * z' v + β) = y then (1 : ℝ) else 0) =
      ν.weight z := by
    unfold FiniteLaw.expect
    simp only [hiff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
  have hr : ν.expect (fun z' => if z' = y then (1 : ℝ) else 0) = ν.weight y := by
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hl, hr] at hH
  exact hH.symm

/-- **Every record of the tail law is square-affine invariant** (pointwise). -/
theorem tail_component_invariant (ρ : UpIdx) :
    AffineInvariant p (upComponent (tailFieldLaws p hne) ρ).weight :=
  affineInvariant_of_expect _ fun _ hα β H => tail_component_expect_affine p hne ρ hα β H

/-- **Every record of the tail law has uniform one-slot marginals**. -/
theorem tail_component_uniform (ρ : UpIdx) :
    HasUniformMarginals (upComponent (tailFieldLaws p hne) ρ) :=
  uniform_of_translation _ fun β z => by
    have := tail_component_invariant p hne ρ 1 β (map_one _) z
    simp only [one_mul] at this
    exact this

/-- The envelope `Diag_ι(m_+(Π_ρ))` of the record `ρ` of the tail law. -/
noncomputable abbrev tailEnv (ρ : UpIdx) : SlotMeasure (ZMod p) :=
  reservedCut.diagonalLaw (plusMarginal reservedCut (upComponent (tailFieldLaws p hne) ρ).weight)

/-- **The envelopes of the tail records** (W8's `upper_envelope` at the tail). -/
theorem tail_envelope (ρ : UpIdx) :
    IsProbability (tailEnv p hne ρ) ∧ TheoremC.IsDiagonalAt reservedCut (tailEnv p hne ρ) ∧
      HasUniformSlotMarginals (tailEnv p hne ρ) :=
  envelope_of_law reservedCut _ (tail_component_uniform p hne ρ)

/-- **The change of a deleted record of the tail law is symmetric at `ι`**. -/
theorem tail_skew_recordChange_deleted (W : UpperWeights) (new : UpIdx → FiniteLaw (Slot → ZMod p))
    (r : ℝ) {ρ : UpIdx} (hρ : upperFate ρ = .deleted) :
    skewPart reservedCut (recordChange (tailFieldLaws p hne) W new r ρ) = 0 := by
  have hsym := tail_upComponent_symmetric p hne ρ
  unfold recordChange
  rw [hρ]
  unfold skewPart
  rw [reflect_neg, reflect_smul, hsym]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, smul_eq_mul,
    LinearMap.zero_apply]
  ring

/-- **A deleted record of the tail law** (charging rule (i) of `prop:record:upper`(i)): the change
`-ω Π_ρ` has the bracket against `ω Diag_ι(m_+)`. -/
theorem tail_deleted_bracket (ρ : UpIdx) {ω : ℝ} (hω : 0 ≤ ω) :
    reservedCut.Bracket (ω • tailEnv p hne ρ)
      (-(ω • signedIntegral (upComponent (tailFieldLaws p hne) ρ).weight)) (ω • tailEnv p hne ρ) :=
  deleted_record_bracket reservedCut (upComponent (tailFieldLaws p hne) ρ).nonneg
    (tail_upComponent_symmetric p hne ρ) hω

end Sarkozy.TailPrices
