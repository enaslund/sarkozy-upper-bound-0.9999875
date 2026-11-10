module

public import Sarkozy.UpperComparison.Construction
public import Sarkozy.UpperComparison.Prices
public import Sarkozy.PartVRecords.Frame

@[expose] public section

/-!
# The records of the upper reference are symmetric at `ι` (`prop:record:upper`(i))

`paper/sections/26_upper_comparison.tex`, proof of `prop:record:upper`(i):
* "Records deleted": a deleted two-layer record is a coupling of its actual half marginal with
  itself, symmetric under the layer interchange, and a deleted folded record is a
  reserved-diagonal law. Either way the change `-w r^d · (record)` is symmetric and is charged its
  mass in the symmetric total only (`rem:cp:charging`(i)).
* "Records repaired": the old record is symmetric at `ι`, so the skew part of the change is that
  of the new law (`rem:cp:charging`(iii)).

Both use the symmetry at the reserved cut `ι` of every record of the upper reference. It is
proved here for V1's block field laws:
* `upLayerSwap` is the layer interchange of the two-layer field graph, and
  `upLayerSwap_automorphism` shows that it is an automorphism: the edge relation
  `twoLayerEdge` does not read the layer;
* `upEmission_reserved` gives the action of the reserved cut on the two-layer emission;
* `twoLayer_symmetric` and `folded_symmetric` (the latter from V3's `isSymmetricAt_emit`) combine
  into `upComponent_symmetric`: every record `Π_ρ` of an upper block is symmetric at `ι`;
* `deleted_record_bracket_paper`: the bracket of a deleted record of the paper;
* `skew_recordChange`: the skew part of the change of a changed record is the skew part of its
  replacing law, weighted; `skew_recordChange_deleted`: a deleted record's change has no skew part;
* `changed_sym_coef_eq`, `changed_skew_coef_eq`, `deleted_coef_eq`: the coefficients that the two
  charging brackets produce, with the weight `c_ρ/P_μ(r)`, are exactly the unpriced ledger
  coefficients divided by `P_μ(r)`, so the hypotheses of `Ledger.paper_block_prices` hold with
  equality.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.RecordExpansion

/-- The layer interchange `(o₀, o₁, ℓ) ↦ (o₀, o₁, 1 - ℓ)` of the vertices of a two-layer field
graph. -/
def upLayerSwap (O₀ O₁ : Type*) : O₀ × O₁ × Fin 2 ≃ O₀ × O₁ × Fin 2 :=
  Equiv.prodCongr (Equiv.refl O₀) (Equiv.prodCongr (Equiv.refl O₁) (Equiv.swap 0 1))

/-- **The layer interchange is an automorphism of the two-layer field graph**: the edge relation
does not read the layer. -/
theorem upLayerSwap_automorphism (f₀ f₁ : FType) :
    IsAutomorphism (fieldGraph f₀ f₁ (Fin 2)) (upLayerSwap f₀.Obj f₁.Obj) := by
  intro u v
  simp only [fieldGraph, mem_twoLayerGraph, twoLayerEdge, upLayerSwap, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id_eq]

/-- The reserved cut acts on the two-layer emission as the layer interchange. -/
theorem upEmission_reserved {O₀ O₁ : Type*} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (v : Slot) :
    upEmission φ₀ φ₁ (reservedCut.flip v) = upLayerSwap O₀ O₁ (upEmission φ₀ φ₁ v) := by
  change (φ₀ v.1, φ₁ v.2.1, layerFin (1 - v.2.2)) = _
  rw [layerFin_swap]
  rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **A two-layer record of an upper block is symmetric at `ι`.** -/
theorem twoLayer_symmetric (hne : UpperNonempty pr) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) :
    IsSymmetricAt reservedCut
      (signedIntegral (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight) := by
  apply LinearMap.ext
  intro f
  rw [reflect_apply, ← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral]
  change (emit (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))
      (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).expect (fun z => f (z ∘ reservedCut.flip)) =
    (emit (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))
      (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).expect f
  rw [expect_emit, expect_emit]
  have hcomp : ∀ y : t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr,
      (y ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2)) ∘ reservedCut.flip =
        (y ∘ upLayerSwap _ _) ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2) := by
    intro y
    funext v
    simp only [Function.comp_apply, upEmission_reserved]
  simp only [hcomp]
  exact blockGraphLaw_expect_auto pr _ (hne.two _ _) (upLayerSwap _ _)
    (upLayerSwap_automorphism _ _) (fun y => f (y ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2)))

/-- **A folded record is symmetric at `ι`**: its emission is fixed by the reserved cut (V3's
`isSymmetricAt_emit`). -/
theorem folded_symmetric {X : Type} [Fintype X] [DecidableEq X] (F : UpperFieldLaws X)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    IsSymmetricAt reservedCut (signedIntegral (upComponent F (false, ⟨t, φ⟩)).weight) :=
  PartVRecords.isSymmetricAt_emit _ _ reservedCut (upDiagEmission_reserved _ _)

/-- **Every record of an upper block is symmetric at `ι`.** -/
theorem upComponent_symmetric (hne : UpperNonempty pr) (ρ : UpIdx) :
    IsSymmetricAt reservedCut
      (signedIntegral (upComponent (upperBlockFieldLaws pr hne) ρ).weight) := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact folded_symmetric _ t φ
  · exact twoLayer_symmetric pr hne t φ

/-- **`prop:record:upper`(i), a deleted record of the paper** (charging rule (i)): for every
record `Π_ρ` of an upper block and every weight `ω ≥ 0` (in the proof `ω = c_ρ/P_μ(r)`), the change
`-ω Π_ρ` has the bracket `(ω Diag(m_+)  -ωΠ_ρ; -ωΠ_ρ  ω Diag(m_+)) ⪰_ι 0`, `m_+` the actual half
marginal of the record. -/
theorem deleted_record_bracket_paper (hne : UpperNonempty pr) (ρ : UpIdx) {ω : ℝ} (hω : 0 ≤ ω) :
    reservedCut.Bracket
      (ω • reservedCut.diagonalLaw
        (plusMarginal reservedCut (upComponent (upperBlockFieldLaws pr hne) ρ).weight))
      (-(ω • signedIntegral (upComponent (upperBlockFieldLaws pr hne) ρ).weight))
      (ω • reservedCut.diagonalLaw
        (plusMarginal reservedCut (upComponent (upperBlockFieldLaws pr hne) ρ).weight)) :=
  deleted_record_bracket reservedCut (upComponent (upperBlockFieldLaws pr hne) ρ).nonneg
    (upComponent_symmetric pr hne ρ) hω

/-- **The skew part of a changed record's change** (`rem:cp:charging`(iii)): the old record is
symmetric at `ι`, so the skew part of `c_ρ (new ρ - Π_ρ)` is `c_ρ` times the skew part of the
replacing law. -/
theorem skew_recordChange (hne : UpperNonempty pr) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → BlockLabel pr)) (r : ℝ) {ρ : UpIdx}
    (hρ : upperFate ρ = .changed) :
    skewPart reservedCut (recordChange (upperBlockFieldLaws pr hne) W new r ρ) =
      upCoeff W r ρ • skewPart reservedCut (signedIntegral (new ρ).weight) := by
  have hsym := upComponent_symmetric pr hne ρ
  unfold recordChange
  rw [hρ]
  unfold skewPart
  rw [reflect_smul, reflect_sub, hsym]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
  ring

/-- **The change of a deleted record is symmetric** at `ι`: its skew part vanishes, so it enters
the symmetric total only. -/
theorem skew_recordChange_deleted (hne : UpperNonempty pr) (W : UpperWeights)
    (new : UpIdx → FiniteLaw (Slot → BlockLabel pr)) (r : ℝ) {ρ : UpIdx}
    (hρ : upperFate ρ = .deleted) :
    skewPart reservedCut (recordChange (upperBlockFieldLaws pr hne) W new r ρ) = 0 := by
  have hsym := upComponent_symmetric pr hne ρ
  unfold recordChange
  rw [hρ]
  unfold skewPart
  rw [reflect_neg, reflect_smul, hsym]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, smul_eq_mul,
    LinearMap.zero_apply]
  ring

/-! ## The bracket coefficients are the ledger's -/

section Coefficients

variable (W : UpperWeights) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i)

/-- **The coefficient of a changed record's symmetric bracket**: with weight `ω = c_ρ/P_μ(r)` and
norm bound `C^s_ρ r`, `changed_record_bracket` charges `ω C^s_ρ r`, which is the unpriced ledger
coefficient `w C^s r^{deg+1}` divided by `P_μ(r)`: the hypothesis `hπs` of `paper_block_prices`
holds with equality. -/
theorem changed_sym_coef_eq (r : ℝ) {ρ : UpIdx} (hρ : upperFate ρ = .changed) :
    upCoeff W r ρ / upPoly W r * (Cs ρ * r) =
      (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r := by
  have hf : (upperLedger W Cs Ca hCs hCa).fate ρ = .changed := hρ
  unfold RecordLedger.symCoef
  rw [hf, ← upperLedger_mass W Cs Ca hCs hCa r ρ]
  simp only [upperLedger, pow_succ]
  ring

/-- The same for the skew bracket. -/
theorem changed_skew_coef_eq (r : ℝ) {ρ : UpIdx} (hρ : upperFate ρ = .changed) :
    upCoeff W r ρ / upPoly W r * (Ca ρ * r) =
      (upperLedger W Cs Ca hCs hCa).skewCoef r ρ / upPoly W r := by
  have hf : (upperLedger W Cs Ca hCs hCa).fate ρ = .changed := hρ
  unfold RecordLedger.skewCoef
  rw [hf, ← upperLedger_mass W Cs Ca hCs hCa r ρ]
  simp only [upperLedger, pow_succ]
  ring

/-- **The coefficient of a deleted record's bracket** (`deleted_record_bracket_paper` with
`ω = c_ρ/P_μ(r)`) is its unpriced ledger coefficient `w r^{deg}` divided by `P_μ(r)`; its skew
coefficient is zero. -/
theorem deleted_coef_eq (r : ℝ) {ρ : UpIdx} (hρ : upperFate ρ = .deleted) :
    upCoeff W r ρ / upPoly W r = (upperLedger W Cs Ca hCs hCa).symCoef r ρ / upPoly W r ∧
      (upperLedger W Cs Ca hCs hCa).skewCoef r ρ = 0 := by
  have hf : (upperLedger W Cs Ca hCs hCa).fate ρ = .deleted := hρ
  refine ⟨?_, ?_⟩
  · unfold RecordLedger.symCoef
    rw [hf, ← upperLedger_mass W Cs Ca hCs hCa r ρ]
  · unfold RecordLedger.skewCoef
    rw [hf]

end Coefficients

end Sarkozy.UpperComparison
