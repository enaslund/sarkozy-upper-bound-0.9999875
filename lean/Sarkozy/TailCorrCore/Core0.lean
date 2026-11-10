module

public import Sarkozy.TailCorrCore.Swap

@[expose] public section

/-!
# `TailSpectralCore` from the coordinate-`0` inputs

`paper/sections/27_tail_index.tex`, `lem:tail-law`(i); `paper/sections/25_upper_reference.tex`,
`subsec:upper-reference-rp` ((V1), (V2), (V3)), `it:record:upper-F4`, `it:record:upper-F6`.

By `Swap`, the row datum of the coordinate `1` at `𝔣'` is the row datum of the coordinate `0` at
`𝔣'` (`rowD1_eq_rowD0_one`, `rowD1_eq_rowD0_two`). So the six coordinate-`1` field families of
HC's `TailSpectralCore` (`root21`, `root11`, `fold21`, `fold11`, `match21`, `match11`) are its
coordinate-`0` families, and:

* **`TailSpectralCore0`**: the coordinate-`0` fields (`root20`, `root10`, `fold20`, `fold10`,
  `match20`, `match10`) and the layer caps (`caps`), unchanged from `TailSpectralCore`;
* `tailSpectralCore_of_core0`: `TailSpectralCore0 → TailSpectralCore`;
* **`tailInputsCorr_of_core0`**: the obligation `hC : TailInputsCorr P₄` from
  `TailSpectralCore0` at every prime `q ≥ P₄`; `tailInputsValid_of_core0`.

New material for this paper.
-/

namespace Sarkozy.TailCorrCore

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.TailCorr

variable {p : ℕ} [Fact p.Prime]

/-- **One layer: the row datum of the coordinate `1` is that of the coordinate `0`.** -/
theorem rowD1_eq_rowD0_one (hne : TailNonempty p) (f' : FieldTy)
    (h1 : RowHyp1 (lam1 (tailFieldLaws p hne)) f') (h0 : RowHyp0 (lam1 (tailFieldLaws p hne)) f') :
    rowD1 (lam1 (tailFieldLaws p hne)) f' h1 = rowD0 (lam1 (tailFieldLaws p hne)) f' h0 := by
  unfold rowD0 rowD1
  congr 1
  · exact (rows_swap_one hne .E f').symm
  · exact (rows_swap_one hne .F f').symm
  · exact (rows_swap_one hne .L f').symm

/-- **Two layers: the row datum of the coordinate `1` is that of the coordinate `0`.** -/
theorem rowD1_eq_rowD0_two (hne : TailNonempty p) (f' : FieldTy)
    (h1 : RowHyp1 (lam2 (tailFieldLaws p hne)) f') (h0 : RowHyp0 (lam2 (tailFieldLaws p hne)) f') :
    rowD1 (lam2 (tailFieldLaws p hne)) f' h1 = rowD0 (lam2 (tailFieldLaws p hne)) f' h0 := by
  unfold rowD0 rowD1
  congr 1
  · exact (rows_swap_two hne .E f').symm
  · exact (rows_swap_two hne .F f').symm
  · exact (rows_swap_two hne .L f').symm

/-- **The remaining spectral inputs of the tail datum, coordinate `0` only** (`lem:tail-law`(i),
its spectral part). Hypothesis bundle, not proved here: the fields `root20`, `root10`, `fold20`,
`fold10`, `match20`, `match10`, `caps` of HC's `TailSpectralCore`, with the same statements
((V1) `it:upper-valid-root`, `lem:upper-completed-root`, `it:record:upper-F6`; (F4)
`it:record:upper-F4`, `eq:row-anova-actual`, `eq:row-anova-stars`; (V3) `it:upper-valid-layer`).
The coordinate-`1` fields follow (`tailSpectralCore_of_core0`). -/
structure TailSpectralCore0 (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q) : Prop where
  root20 : ∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailOrd f').d (tailR q)
  root10 : ∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailRes f').d (tailR q)
  fold20 : ∀ f', FoldCorr (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailCF (tailOrd f') * tailR q)
  fold10 : ∀ f', FoldCorr (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailCF (tailRes f') * tailR q)
  match20 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) ((tailOrd f').h * tailR q)
  match10 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) ((tailRes f').h * tailR q)
  caps : ∀ f0 f1 : FieldTy, ¬ (f0 = .E ∧ f1 = .E) →
    (Reserved.fieldCut f0.Obj f1.Obj).Below
      (-(tailKappa f0 f1 * tailR q) •
        pushFunctional (lawL (lam1 (tailFieldLaws q hne) f0 f1)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws q hne) f0 f1))

/-- **`TailSpectralCore` from the coordinate-`0` inputs** (the coordinate-`1` row data are the
coordinate-`0` ones). -/
theorem tailSpectralCore_of_core0 (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q) (h : TailSpectralCore0 q hne hW hp) :
    TailSpectralCore q hne hW hp := by
  have e2 : ∀ f', rowD1 (lam2 (tailFieldLaws q hne)) f' ((tail_upperDatumHyp q hW hp hne).two1 f') =
      rowD0 (lam2 (tailFieldLaws q hne)) f' ((tail_upperDatumHyp q hW hp hne).two0 f') :=
    fun f' => rowD1_eq_rowD0_two hne f' _ _
  have e1 : ∀ f', rowD1 (lam1 (tailFieldLaws q hne)) f' ((tail_upperDatumHyp q hW hp hne).one1 f') =
      rowD0 (lam1 (tailFieldLaws q hne)) f' ((tail_upperDatumHyp q hW hp hne).one0 f') :=
    fun f' => rowD1_eq_rowD0_one hne f' _ _
  refine ⟨h.root20, fun f' => ?_, h.root10, fun f' => ?_, h.fold20, fun f' => ?_, h.fold10,
    fun f' => ?_, h.match20, fun f' hf => ?_, h.match10, fun f' hf => ?_, h.caps⟩
  · rw [e2]; exact h.root20 f'
  · rw [e1]; exact h.root10 f'
  · rw [e2]; exact h.fold20 f'
  · rw [e1]; exact h.fold10 f'
  · rw [e2]; exact h.match20 f' hf
  · rw [e1]; exact h.match10 f' hf

/-- **`TailInputsCorr P` from the coordinate-`0` inputs** (`lem:tail-law`(i) reduced to
`TailSpectralCore0`): with `P = P₄` this is the obligation `hC` of the main statement. -/
theorem tailInputsCorr_of_core0 {P : ℕ} (hP : P4 ≤ P)
    (hS : ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
      (hp : (2 : ℝ) ^ 20 ≤ q), TailSpectralCore0 q hne hW hp) :
    TailInputsCorr P :=
  tailInputsCorr_of_core hP fun q _ hq hne hW hp =>
    tailSpectralCore_of_core0 q hne hW hp (hS q hq hne hW hp)

/-- **`TailInputsValid P₄` from the coordinate-`0` inputs.** -/
theorem tailInputsValid_of_core0
    (hS : ∀ (q : ℕ) [Fact q.Prime], P4 ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
      (hp : (2 : ℝ) ^ 20 ≤ q), TailSpectralCore0 q hne hW hp) :
    TailInputsValid P4 :=
  tailInputsValid_of_corr le_rfl (tailInputsCorr_of_core0 le_rfl hS)

end Sarkozy.TailCorrCore
