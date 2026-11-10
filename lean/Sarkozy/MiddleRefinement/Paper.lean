module

public import Sarkozy.MiddleRefinement.Spec
public import Sarkozy.MainFinalF1d.Main

@[expose] public section

/-!
# `Env.MR` of the F1 main statement from the paper's construction (MRG)

`paper/sections/24_matching_mean.tex`, `prop:record:matching`(i), `prop:signed-sides`.

The field `Dv.MR` of `MainFinalF1d.MainFinalObligations3f` is a `MidRefinement` over the
irreducible `gramBracketTarget` (A2), `firstStageTarget` (A1) and `comparisonLawTarget` (B2) of the
F1 data. Here it is **built** from `Spec.lean`'s block refinements:

* **`atomRefinementOf`**: a `BlockRefinement` of the block `b` (in A1/A2/B7's terms) is an
  `AtomRefinement` of the F1 data at the atom `.inr b` (the identification: the records of
  `comparisonLawTarget` at a middle block are B7's `Chg ⊕ Del`, its changes `R.delta`; A2's `Ñ`
  and A1's `λ` are V3's; the irreducible definitions are unfolded once, the identities are `rfl`);
* **`SideInputs`**: the inputs of the paper's refinement on the middle blocks: per middle block
  the chosen sides `d_L, d_R`, the block Grams of `prop:signed-sides`(i),(ii) (`SpecSides`) and
  the side gates (`SpecGate`);
* **`midRefinementOf`**: the `MidRefinement` with `repl = replSet` (B7's folds and matchings) on
  every middle block, the signed sides on the folds, the (CP4) envelopes on the matchings, and the
  per-atom bounds `KL = KR` = the exact side price (independent of the scale);
* **`others_eq`**: the (CP4) prices of the F1 data outside `MR.repl` at `.inr b` are B7's
  `π̃_t q^{2a}` outside the block refinement's `repl` (`= replSet` on every root);
* **`KL_eq`**, **`KR_eq`**: `KL (.inr b)`, `KR (.inr b)` are the block refinement's side prices
  `(P⁻¹ r² (k_L + k_R) + ∑_s π̃_{E_s}) q^{2a}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRefinement

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.GramBracketPaper
open Sarkozy.CancellationSteps Sarkozy.BlockSpecPaper Sarkozy.MainTarget
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.MainFinal (hCF)
open Sarkozy.MainFinal2 (MidRefinement AtomRefinement)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk midAtom)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- The Gram bracket of the F1 data (A2's `gramBracketTarget`). -/
noncomputable abbrev gbF (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) :=
  gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour) (paperIn f1Cell) (paperGi hW A)

/-- (R2) of the reference at `ι` at a class-three block (A2's `hμ` of `paperGram`). -/
theorem hμF (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (b : Blk) :
    reservedCut.Positive (signedIntegral ((specF hW A b).toAtom hW).law.weight) :=
  (v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).rp₀ (.inr b) reservedCut
    reservedCut_family

/-- The block refinement of a class-three block of the F1 data. -/
abbrev BlockRefF (C : ComparisonParts hW hMR hFour A) (b : Blk) : Type 1 :=
  BlockRefinement hW (paperIn f1Cell) (specF hW A b) (C.blk b) ((paperGi hW A).protects b)
    (hμF hW hMR hFour A b)

/-- **The identification** (`prop:record:matching`(i) on the paper's objects): a block refinement
of `b` (in the terms of A1's `specStage`, A2's `specGram` and B7's `atomOf`) is a refinement of the
F1 data at the atom `.inr b` and every scale. The records of `comparisonLawTarget` at `.inr b` are
those of `atomOf`, its changes `atomOf`'s, and A2's `Ñ`, A1's `λ` at `.inr b` are `specGram`'s
and `specStage`'s (all by unfolding the irreducible definitions). -/
noncomputable def atomRefinementOf (C : ComparisonParts hW hMR hFour A) {b : Blk}
    (BR : BlockRefF C b) (L : ℕ) : AtomRefinement (gbF hW hMR hFour A) C.CL L (.inr b) where
  repl := by
    unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
    exact BR.repl
  IK := BR.IK
  kL := BR.kL
  kR := BR.kR
  kL_nonneg := BR.kL_nonneg
  kR_nonneg := BR.kR_nonneg
  κK := BR.κK
  κK_pos := BR.κK_pos
  κK_diag := BR.κK_diag
  bracket := by
    unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget gbF
      GramBracketPaper.gramBracketTarget FirstStagePaper.firstStageTarget
    exact BR.bracket

/-- (R2) at `ι` and the protection give A2's data; a middle atom of the F1 data is a block with
`specUpper = false`. -/
theorem specUpper_of_mid {b : Blk} (h : midAtom hW A (.inr b) = true) :
    specUpper (specF hW A b) = false := by
  simpa [midAtom] using h

/-- `f₁ + h₁ ≥ 0` on every middle block of the F1 data (B1's `allpInputs_nonneg`, through
`paperSpec_facts`). -/
theorem specSign_of_mid (b : Blk) (hu : specUpper (specF hW A b) = false) :
    SpecSign (specF hW A b) := by
  rcases hs : blockSite b with i | k
  · have h := (MainFinalF1.paperSpec_facts hW A b i hs ⟨0, 0, 0, 0, 0⟩ 0 0).2.1
    revert h
    generalize specF hW A b = S
    intro h
    cases S with
    | upper _ => trivial
    | middleUniform _ => exact h.2
    | middleIndividual _ => exact h.2
    | middleCoherent _ => exact h.2
  · have := MainFinalF1.paperSpec_upper hW A b k hs
    rw [hu] at this
    exact absurd this (by decide)

/-- **The inputs of the paper's refinement on the middle blocks** (`prop:signed-sides`): per
block the chosen sides `d_L, d_R` (data; the paper's `d_s(X_i)` of the block's piece), the block
Grams of the signed fold records with these sides (`SpecSides`, *hypothesis*: `prop:signed-sides`
(i),(ii)) and the side gates `w_D d_s - v_D ≥ 0` (`SpecGate`, *hypothesis*: finite checks of the
recorded weights, `cert:record:matching`). -/
structure SideInputs (C : ComparisonParts hW hMR hFour A) where
  dL : Blk → ℝ
  dR : Blk → ℝ
  gram : ∀ b, specUpper (specF hW A b) = false →
    SpecSides hW (paperIn f1Cell) (dL b) (dR b) (specF hW A b) (C.blk b)
  gateL : ∀ b, specUpper (specF hW A b) = false → SpecGate (dL b) (specF hW A b)
  gateR : ∀ b, specUpper (specF hW A b) = false → SpecGate (dR b) (specF hW A b)

/-- The block refinement of a middle block of the F1 data (`blockRefinementOf`). -/
noncomputable def blockRefF (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (b : Blk)
    (hu : specUpper (specF hW A b) = false) : BlockRefF C b :=
  blockRefinementOf hW (paperIn f1Cell) (SI.dL b) (SI.dR b) (specF hW A b) (C.blk b)
    ((paperGi hW A).protects b) (hμF hW hMR hFour A b) hu (specSign_of_mid b hu) (SI.gateL b hu)
    (SI.gateR b hu) (SI.gram b hu)

/-- The left side price of a block (`0` on an upper block). -/
noncomputable def sideKL (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (b : Blk) : ℝ :=
  if hu : specUpper (specF hW A b) = false then
    ∑ i, (blockRefF C SI b hu).kL i * mass ((blockRefF C SI b hu).κK i) *
      paperSelAt (paperAtomMap bOf) targetDecay (.inr b)
  else 0

/-- The right side price of a block (`0` on an upper block). -/
noncomputable def sideKR (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (b : Blk) : ℝ :=
  if hu : specUpper (specF hW A b) = false then
    ∑ i, (blockRefF C SI b hu).kR i * mass ((blockRefF C SI b hu).κK i) *
      paperSelAt (paperAtomMap bOf) targetDecay (.inr b)
  else 0

/-- **`Env.MR` of the F1 statement from the paper's construction** (`prop:record:matching`(i),
`prop:signed-sides`): on every middle block the refinement `blockRefinementOf` (the folds and
matchings of B7's atom replaced, the paper's signed sides on the folds, the (CP4) envelopes on the
matchings), transported to the F1 data by `atomRefinementOf`; the per-atom bounds are the exact
side prices `sideKL`, `sideKR` (scale-free). -/
noncomputable def midRefinementOf (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) :
    MidRefinement (gbF hW hMR hFour A) C.CL (fun β => midAtom hW A β = true) where
  R L β h := match β, h with
    | .inl _, h => absurd h (by simp [midAtom])
    | .inr b, h => atomRefinementOf C (blockRefF C SI b (specUpper_of_mid h)) L
  KL β := match β with
    | .inl _ => 0
    | .inr b => sideKL C SI b
  KR β := match β with
    | .inl _ => 0
    | .inr b => sideKR C SI b
  KL_bound L β h := match β, h with
    | .inl _, h => absurd h (by simp [midAtom])
    | .inr b, h => by
        show _ ≤ sideKL C SI b
        unfold sideKL
        simp only [specUpper_of_mid h, ↓reduceDIte]
        rfl
  KR_bound L β h := match β, h with
    | .inl _, h => absurd h (by simp [midAtom])
    | .inr b, h => by
        show _ ≤ sideKR C SI b
        unfold sideKR
        simp only [specUpper_of_mid h, ↓reduceDIte]
        rfl

theorem midAtom_of_specUpper {b : Blk} (hu : specUpper (specF hW A b) = false) :
    midAtom hW A (.inr b) = true := by
  simp [midAtom, hu]

/-- **The records not replaced at a middle block, in B7's terms**: the (CP4) prices of the F1 data
outside `MR.repl` at `.inr b` are B7's `π̃_t q^{2a}` outside the block refinement's `repl`. -/
theorem others_eq (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (L : ℕ) (b : Blk)
    (hu : specUpper (specF hW A b) = false) :
    ∑ t ∈ univ \ (midRefinementOf C SI).toPrefix.repl L (.inl (.inr b)),
        (C.CL.π L (.inl (.inr b)) t .sym + C.CL.π L (.inl (.inr b)) t .skew) =
      ∑ t ∈ univ \ (blockRefF C SI b hu).repl,
        ((atomOf hW (paperIn f1Cell) (specF hW A b) (C.blk b)).πt t .sym +
          (atomOf hW (paperIn f1Cell) (specF hW A b) (C.blk b)).πt t .skew) *
          paperSelAt (paperAtomMap bOf) targetDecay (.inr b) := by
  have hm := midAtom_of_specUpper (hW := hW) (A := A) hu
  have e : (midRefinementOf C SI).atom L (.inr b) = (midRefinementOf C SI).R L (.inr b) hm := by
    unfold MidRefinement.atom
    simp only [hm, ↓reduceDIte]
  show ∑ t ∈ univ \ ((midRefinementOf C SI).atom L (.inr b)).repl, _ = _
  rw [e]
  show ∑ t ∈ univ \ (atomRefinementOf C (blockRefF C SI b (specUpper_of_mid hm)) L).repl, _ = _
  unfold atomRefinementOf ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  simp only [add_mul]
  rfl

/-- **The left and right per-atom bounds of `midRefinementOf`** at a middle block are the block
refinement's side prices. -/
theorem KL_eq (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (b : Blk)
    (hu : specUpper (specF hW A b) = false) :
    (midRefinementOf C SI).toPrefix.KL (.inr b) =
      ∑ i, (blockRefF C SI b hu).kL i * mass ((blockRefF C SI b hu).κK i) *
        paperSelAt (paperAtomMap bOf) targetDecay (.inr b) := by
  have hm := midAtom_of_specUpper (hW := hW) (A := A) hu
  show (if midAtom hW A (.inr b) = true then sideKL C SI b else 0) = _
  simp only [hm, ↓reduceIte]
  unfold sideKL
  simp only [hu, ↓reduceDIte]

theorem KR_eq (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (b : Blk)
    (hu : specUpper (specF hW A b) = false) :
    (midRefinementOf C SI).toPrefix.KR (.inr b) =
      ∑ i, (blockRefF C SI b hu).kR i * mass ((blockRefF C SI b hu).κK i) *
        paperSelAt (paperAtomMap bOf) targetDecay (.inr b) := by
  have hm := midAtom_of_specUpper (hW := hW) (A := A) hu
  show (if midAtom hW A (.inr b) = true then sideKR C SI b else 0) = _
  simp only [hm, ↓reduceIte]
  unfold sideKR
  simp only [hu, ↓reduceDIte]

end Sarkozy.MiddleRefinement
