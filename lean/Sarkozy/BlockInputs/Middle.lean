module

public import Sarkozy.BlockInputs.FoldCaps

@[expose] public section

/-!
# The middle block inputs split: rows, F21 certificates, positive-root caps

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(i),(ii);
`21_middle_records.tex`, `lem:old-f-law`(e); `20b_positive_roots.tex`, `prop:root-chamber`,
`prop:root-layer`, `cert:positive-root-caps`.

B6's `MiddleUniformBlockInputs i` (31 uniform pieces) is rows `j = 2, 1` and the F21 caps;
`MiddleIndividualBlockInputs i u` (pieces `2³⁶`, `2⁴⁰`) is rows, the L20 envelope and L21 cap of the
individual-square root, and the F21 caps. Here:

* `rowBounds_individual`: the rows of the individual datum **are** the rows of the uniform datum
  (a five-type datum's `ν`, `ν^b`, `T_F`, `T_E` are read from the `E` and `F` laws only, which do
  not depend on the root), so one rows input serves all 33 pieces;
* `MiddleBlockRows i`: `lem:front12:reference`(i) at piece `i` (block level);
* `MiddleIndividualRoot i u`: the L20 envelope and the L21 cap of the positive root (block level);
* **`middleUniformBlockInputs_of`**, **`middleIndividualBlockInputs_of`**: B6's two fields from
  the rows, the F21 certificate `MiddleFoldCert i` (`FoldCaps.lean`) and, on the individual
  pieces, `MiddleIndividualRoot`;
* `middleBlockRows_of_uniform`, `middleBlockRows_of_individual`, `middleIndividualRoot_of`: the
  converses for the block-level parts (non-vacuity of the split).
-/

open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.BlockAdapter

/-- **The rows of the individual-root datum are the rows of the uniform-root datum**: `RowBounds`
reads only `ν`, `ν^b`, `T_F`, `T_E`, which are built from the `E` and `F` laws. -/
theorem rowBounds_individual_iff {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ j, Fact (pr j).Prime] (hne : MiddleNonempty pr) (u : ℚ) (f h r : ℝ) :
    RowBounds (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) f h r ↔
      RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) f h r := by
  set πE := objLaw (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
  set πF := objLaw (blockGraphLaw pr (foldGraph (Fin 2)) hne.F2)
  have e1 : (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)).nu = nuOf πE := rfl
  have e1' : (fieldDatum (middleBlock_datumHyp₂ pr hne)).nu = nuOf πE := rfl
  have e2 : (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)).nub = nubOf πE := rfl
  have e2' : (fieldDatum (middleBlock_datumHyp₂ pr hne)).nub = nubOf πE := rfl
  have e3 : (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)).TF = kernelOf πE πF := rfl
  have e3' : (fieldDatum (middleBlock_datumHyp₂ pr hne)).TF = kernelOf πE πF := rfl
  have e4 : (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)).TE = kernelOf πE πE := rfl
  have e4' : (fieldDatum (middleBlock_datumHyp₂ pr hne)).TE = kernelOf πE πE := rfl
  unfold RowBounds
  rw [e1, e2, e3, e4, e1', e2', e3', e4']

theorem rowBounds_individual {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ j, Fact (pr j).Prime] (hne : MiddleNonempty pr) (u : ℚ) {f h r : ℝ}
    (H : RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) f h r) :
    RowBounds (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) f h r :=
  (rowBounds_individual_iff pr hne u f h r).mpr H

/-- **`lem:front12:reference`(i) on piece `i`**: the rows at `j = 2, 1` with the recorded row
constants, on every block of the piece. *Hypothesis* (block level, spectral). -/
def MiddleBlockRows (i : Fin 33) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) (allpInputs i).f₂ (allpInputs i).h₂
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **The positive-root caps of an individual piece**: the L20 envelope (`prop:root-chamber` with
`lem:spec:tensorcomp`(b)) and the L21 cap (`prop:root-layer`) of the individual-square root at the
block caps of the piece, on every block. *Hypothesis* (block level, spectral). -/
def MiddleIndividualRoot (i : Fin 33) (u : ℚ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RootEnvelope (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (capVal i 0)
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      IndividualRootLayerCap pr u hne (capK i .L) ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **B6's `MiddleUniformBlockInputs i`** from the rows and the F21 certificate. -/
theorem middleUniformBlockInputs_of {i : Fin 33} (hR : MiddleBlockRows i)
    (hF : MiddleFoldCert i) : MiddleUniformBlockInputs i := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1⟩ := hR ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨r2, r1, foldLayerCaps_of_cert hF pr b h3 hpc hbud hb hb' hne⟩

/-- **B6's `MiddleIndividualBlockInputs i u`** from the rows, the F21 certificate and the
positive-root caps. -/
theorem middleIndividualBlockInputs_of {i : Fin 33} {u : ℚ} (hR : MiddleBlockRows i)
    (hF : MiddleFoldCert i) (hP : MiddleIndividualRoot i u) :
    MiddleIndividualBlockInputs i u := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1⟩ := hR ι pr b hinj h3 hpc hbud hb hb' hne
  obtain ⟨e2, hL⟩ := hP ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨rowBounds_individual pr hne u r2, r1, e2, hL,
    foldLayerCaps_of_cert hF pr b h3 hpc hbud hb hb' hne⟩

/-- The rows from B6's uniform field (non-vacuity). -/
theorem middleBlockRows_of_uniform {i : Fin 33} (h : MiddleUniformBlockInputs i) :
    MiddleBlockRows i := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1, -⟩ := h ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨r2, r1⟩

/-- The rows from B6's individual field (non-vacuity; the rows of the two data agree). -/
theorem middleBlockRows_of_individual {i : Fin 33} {u : ℚ} (h : MiddleIndividualBlockInputs i u) :
    MiddleBlockRows i := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨r2, r1, -⟩ := h ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨(rowBounds_individual_iff pr hne u _ _ _).mp r2, r1⟩

/-- The positive-root caps from B6's individual field (non-vacuity). -/
theorem middleIndividualRoot_of {i : Fin 33} {u : ℚ} (h : MiddleIndividualBlockInputs i u) :
    MiddleIndividualRoot i u := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  obtain ⟨-, -, e2, hL, -⟩ := h ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨e2, hL⟩

end Sarkozy.BlockInputs
