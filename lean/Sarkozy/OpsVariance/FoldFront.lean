module

public import Sarkozy.OpsVariance.FoldCen

@[expose] public section

/-!
# The fold record laws at the paper's comparison law

`paper/sections/22_variance.tex`, `lem:var-gain` (Cen), `cor:var-classes`(i) (fold classes);
`paper/sections/21_middle_records.tex`, `lem:record:old-f-marginal`(d).

The fold analogue of `MatchFront`. The (Cen) input of a block is the per-block hypothesis
`FoldCenAt κ S` (the prime centred norms of the reference fold coupling are `≤ κ`), which PG's
collision bounds supply (`foldCenAt_of_collision`).

* `foldIdx`, `foldLawOf`, `foldLawIdx`, **`foldRecord_atom`**: at B7's atom of a class-three block
  with fold-component inputs, `Π_{F_j}` is a record law for `F_j` (`j = 1, 2`) with `κ`;
  `foldRecord_atomM`, the twin at the data priced at the bounds (`FoldSpec.toSpecDataM`, RP),
  which the front uses;
* `CollisionAt`, **`foldCenAt_of_collision`**: `FoldCenAt κ S` from `CollisionBound` at every
  prime, `p ≥ 19` and `κ ≥ (Γ_p + e_{o,p} r_p) r_p`;
* `foldCL`, `foldLawCL`, **`foldRecord_CL`**, `foldCL_subset_replCL`: the same at B2's comparison
  law of the obligations' data; the fold records are replaced records (zero marginals).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.Variance
open Sarkozy.Labellings (foldGraph)
open Sarkozy.CancellationSteps (PaperJ0 PaperJt paperM0 paperTail)
open Sarkozy.BlockSpecPaper (PaperAnalyticInputs paperIn)
open Sarkozy.SignedGram (CentredNorm mP oldP)
open Sarkozy.PrimeGram (rP gammaP eoP CollisionBound)

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The fold record laws of a middle block**: `Π_{F_j}` at the fold record `F_j`, `0` at the
other records. -/
noncomputable def foldLawOf (hne : MiddleNonempty pr) : Chg ⊕ Del → (Slot → BlockLabel pr) → ℝ
  | .inl (.inl j) => (blockFold pr hne (PType.pat .D (foldPat j))).weight
  | _ => fun _ => 0

/-- The (Cen) hypothesis of a middle block: prime centred norms `δ_p ≤ κ`. -/
def FoldCenPr (hne : MiddleNonempty pr) (κ : ℝ) : Prop :=
  ∃ δ : ι → ℝ, (∀ i, 0 ≤ δ i) ∧ (∀ i, CentredNorm (mP hne i) (oldP hne i) (δ i)) ∧
    ∀ i, δ i ≤ κ

/-- The collision hypothesis of a middle block (PG's route to `FoldCenPr`). -/
def CollisionPr (hne : MiddleNonempty pr) (κ : ℝ) : Prop :=
  (∀ i, 19 ≤ pr i) ∧ ∃ ccol : ι → ℝ, (∀ i, 0 ≤ ccol i) ∧
    (∀ i, CollisionBound (hne.F2 i) (ccol i)) ∧
    ∀ i, (gammaP pr i + eoP pr ccol i * rP pr i) * rP pr i ≤ κ

omit [Fintype ι] [DecidableEq ι] in
theorem foldCenPr_of_collision (h3 : ∀ i, pr i % 4 = 3) (hne : MiddleNonempty pr) {κ : ℝ}
    (h : CollisionPr pr hne κ) : FoldCenPr pr hne κ := by
  obtain ⟨h19, ccol, hc0, hcol, hκ⟩ := h
  refine ⟨_, fun i => ?_, centredNorm_old pr hne h3 h19 hcol, hκ⟩
  have hrP : 0 ≤ rP pr i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have := PrimeGram.eoP_nonneg h19 hc0 i
  have := PrimeGram.gammaP_nonneg h19 i
  positivity

end Frame

section Spec

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
variable (hW : Target.Weil) (In : FirstStageInputs blockOf)

/-- **The fold records `F₁, F₂` of the atom of a class-three block** (none on an upper block). -/
noncomputable def foldIdx {b : B} :
    (S : PaperBlockSpec blockOf b) → (SD : SpecData hW In S) →
      Finset (MiddleRefinement.atomOf hW In S SD).T
  | .upper _, _ => ∅
  | .middleUniform _, _ => univ.image fun j : Fin 2 => (.inl (.inl j) : Chg ⊕ Del)
  | .middleIndividual _, _ => univ.image fun j : Fin 2 => (.inl (.inl j) : Chg ⊕ Del)
  | .middleCoherent _, _ => univ.image fun j : Fin 2 => (.inl (.inl j) : Chg ⊕ Del)

/-- **The fold record laws of the atom of a class-three block**. -/
noncomputable def foldLawIdx {b : B} :
    (S : PaperBlockSpec blockOf b) → (SD : SpecData hW In S) →
      (MiddleRefinement.atomOf hW In S SD).T → (Slot → BlockLabel (blockPrimes blockOf b)) → ℝ
  | .upper _, _ => fun _ _ => 0
  | .middleUniform M, _ => foldLawOf _ M.hne
  | .middleIndividual M, _ => foldLawOf _ M.hne
  | .middleCoherent M, _ => foldLawOf _ M.hne

/-- **The (Cen) hypothesis of a class-three block** (`True` on an upper block). -/
def FoldCenAt (κ : ℝ) {b : B} : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => FoldCenPr _ M.hne κ
  | .middleIndividual M => FoldCenPr _ M.hne κ
  | .middleCoherent M => FoldCenPr _ M.hne κ

/-- **The collision hypothesis of a class-three block** (`True` on an upper block). -/
def CollisionAt (κ : ℝ) {b : B} : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => CollisionPr _ M.hne κ
  | .middleIndividual M => CollisionPr _ M.hne κ
  | .middleCoherent M => CollisionPr _ M.hne κ

omit [Fintype B] in
theorem foldCenAt_of_collision {κ : ℝ} {b : B} (S : PaperBlockSpec blockOf b)
    (h : CollisionAt κ S) : FoldCenAt κ S := by
  cases S with
  | upper U => trivial
  | middleUniform M => exact foldCenPr_of_collision _ (classThree_blockPrimes b).mod4 M.hne h
  | middleIndividual M => exact foldCenPr_of_collision _ (classThree_blockPrimes b).mod4 M.hne h
  | middleCoherent M => exact foldCenPr_of_collision _ (classThree_blockPrimes b).mod4 M.hne h

omit [Fintype B] in
/-- The fold records are among the replaced records. -/
theorem foldIdx_subset_replIdx {b : B} (S : PaperBlockSpec blockOf b) (SD : SpecData hW In S) :
    foldIdx hW In S SD ⊆ replIdx hW In S SD := by
  cases S with
  | upper U => exact empty_subset _
  | middleUniform M => exact subset_union_left
  | middleIndividual M => exact subset_union_left
  | middleCoherent M => exact subset_union_left

omit [Fintype B] in
/-- **The fold record laws at B7's atom** of a class-three block with fold-component inputs. -/
theorem foldRecord_atom {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcen : FoldCenAt κ S)
    (t' : (MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).T)
    (ht' : t' ∈ foldIdx hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)) :
    RecordLawIs (foldLawIdx hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC) t')
      ((MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).D t') κ := by
  cases S with
  | upper U => exact absurd ht' (notMem_empty _)
  | middleUniform M =>
    obtain ⟨j, -, rfl⟩ := mem_image.mp ht'
    obtain ⟨δ, hδ0, hcn, hκ⟩ := hcen
    exact recordLawIs_fold_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsU In M) j δ hδ0 hcn hκ0 hκ1 hκ
  | middleIndividual M =>
    obtain ⟨j, -, rfl⟩ := mem_image.mp ht'
    obtain ⟨δ, hδ0, hcn, hκ⟩ := hcen
    exact recordLawIs_fold_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsI In M) j δ hδ0 hcn hκ0 hκ1 hκ
  | middleCoherent M =>
    obtain ⟨j, -, rfl⟩ := mem_image.mp ht'
    obtain ⟨δ, hδ0, hcn, hκ⟩ := hcen
    exact recordLawIs_fold_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsC In M) j δ hδ0 hcn hκ0 hκ1 hκ

omit [Fintype B] in
/-- **`foldRecord_atom` at the data priced at the bounds** (`FoldSpec.toSpecDataM`, RP): the record
laws are those of `ofFold` (`ofFoldM_D`). -/
theorem foldRecord_atomM {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (bl sF aF ℓ sE aE : ℝ)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hcen : FoldCenAt κ S)
    (t' : (MiddleRefinement.atomOf hW In S
      (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).T)
    (ht' : t' ∈ foldIdx hW In S (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)) :
    RecordLawIs (foldLawIdx hW In S (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC) t')
      ((MiddleRefinement.atomOf hW In S
        (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).D t') κ := by
  cases S with
  | upper U => exact absurd ht' (notMem_empty _)
  | middleUniform M =>
    obtain ⟨j, -, rfl⟩ := mem_image.mp ht'
    obtain ⟨δ, hδ0, hcn, hκ⟩ := hcen
    exact recordLawIs_fold_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsU In M) j δ hδ0 hcn hκ0 hκ1 hκ
  | middleIndividual M =>
    obtain ⟨j, -, rfl⟩ := mem_image.mp ht'
    obtain ⟨δ, hδ0, hcn, hκ⟩ := hcen
    exact recordLawIs_fold_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsI In M) j δ hδ0 hcn hκ0 hκ1 hκ
  | middleCoherent M =>
    obtain ⟨j, -, rfl⟩ := mem_image.mp ht'
    obtain ⟨δ, hδ0, hcn, hκ⟩ := hcen
    exact recordLawIs_fold_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsC In M) j δ hδ0 hcn hκ0 hκ1 hκ

end Spec

section CL

open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.AnalyticCells (f1Cell)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The fold records of the comparison law at a class-three block `b`**. -/
noncomputable def foldCL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) :
    Finset (C.toK1.CL.T L (.inl (.inr b))) := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  exact foldIdx hW (paperIn f1Cell) (specF hW A b) (C.toK1.blk b)

/-- **The fold record laws of the comparison law at a class-three block `b`**. -/
noncomputable def foldLawCL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) :
    C.toK1.CL.T L (.inl (.inr b)) →
      (Slot → BlockFrame.BlockLabel paperM0 (paperAtomMap bOf) paperTail L (.inl (.inr b))) →
        ℝ := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  exact foldLawIdx hW (paperIn f1Cell) (specF hW A b) (C.toK1.blk b)

/-- **The fold record laws at the paper's comparison law**: at every fold record of a middle
block with the (Cen) hypothesis `FoldCenAt κ`, `Π_{F_j}` (`foldLawCL`) is a record law with `κ`. -/
theorem foldRecord_CL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hcen : FoldCenAt κ (specF hW A b))
    (t : C.toK1.CL.T L (.inl (.inr b))) (ht : t ∈ foldCL C L b) :
    RecordLawIs (foldLawCL C L b t) (C.toK1.CL.D L (.inl (.inr b)) t) κ := by
  unfold foldCL at ht
  unfold foldLawCL
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget at *
  exact foldRecord_atomM hW (paperIn f1Cell) tPaper_nonneg tPaper_le_one _ _ _ _ _ _
    (specF hW A b) _
    hκ0 hκ1 hcen t ht

/-- The fold records are replaced records (so their changes have zero marginals). -/
theorem foldCL_subset_replCL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) :
    foldCL C L b ⊆ replCL C L b := by
  unfold foldCL replCL
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  exact foldIdx_subset_replIdx hW (paperIn f1Cell) (specF hW A b) (C.toK1.blk b)

end CL

end Sarkozy.OpsVariance
