module

public import Sarkozy.OpsVariance.ZeroMarginal
public import Sarkozy.OpsVariance.Selection
public import Sarkozy.MiddleRefinement.Spec
public import Sarkozy.E1Closure.Main

@[expose] public section

/-!
# Zero marginals of the replaced records of the paper's comparison law

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`, proof of
`lem:middle-comparison-prices` ("each replacement has the same actual half marginals on both halves
of `ι` as the record it replaces"); `paper/sections/22_variance.tex`, `eq:record:zero-marginal`,
proof of `lem:var-gain`(b).

**The trace.** At the data `(F.X hB hRR).data` of the companion obligations the comparison law is
`(F.toK.Up.toCmp hMR hFour).toK1.CL` (by `rfl`), B2's `comparisonLawTarget` at the inputs of B7's
`comparisonInputsOfData`. At the atom `.inl (.inr b)` of a middle block `b` its records are B7's
`Chg ⊕ Del` and its changes are those of `Replacements.toAtom` for B8's `ofFold` (through
`SignedSpec.toSpecData = FoldSpec.toSpecData`; since RP the front's data are
`toSpecDataAt = FoldSpec.toSpecDataM`, priced at the bounds, with the same changes, `ofFoldM_Δ`):
`Δ_{F_j} = P⁻¹ w_D r (K_{t,𝔅} − Π_{F_j})` and `Δ_{E_s} = P⁻¹ w_S r (⊗_p K₁ − Π_{E_s})` (B7's
`toAtom_Δ_fold`, `toAtom_Δ_match`). The irreducible `comparisonLawTarget` is unfolded once, as in
MRG's `atomRefinementOf`.

* `zeroMarginals_smul`; **`zeroMarginals_ofFold`**: the changes of B8's `ofFold` atom at the
  replaced records `replSet` (the folds `F₁, F₂` and the matchings `E₀, E₁`) have zero marginals
  (`zeroMarginals_signedFold`, `zeroMarginals_matchRec`);
* `replIdx`, **`zeroMarginals_atom`**: the same for B7's atom of any class-three block whose inputs
  are fold components (`FoldSpec.toSpecData`; empty on an upper block); `zeroMarginals_atomM`, the
  twin at the data priced at the bounds (`FoldSpec.toSpecDataM`, RP), which the front uses;
* `replCL`, **`zeroMarginals_CL`**: at B2's `comparisonLawTarget` of a `ComparisonPartsTC`;
* **`InRepl`**, **`recordsZeroMarginal_front`**: at the obligations' data, a selection whose records
  are all replaced fold or matching records of middle blocks satisfies `RecordsZeroMarginal`, the
  input `hz0`/`hzm` of `varStepsAt_credit` and `varConjunct`. The aligned matching classes
  (records `E_s` at every block) and the fold classes (`F_j`) are of this kind.

The other changed records (merges, constants) and the deleted records are not covered: a deleted
record has the change `−c Π`, whose marginals do not vanish, and no variance credit is taken on
them in the paper.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.CancellationSteps (PaperJ0 PaperJt)
open Sarkozy.BlockSpecPaper (PaperAnalyticInputs paperIn)

/-- Zero marginals are preserved by scalars. -/
theorem zeroMarginals_smul {W Y : Type} [Fintype W] [DecidableEq W] {c : ReflectionCut W}
    {X : ((W → Y) → ℝ) →ₗ[ℝ] ℝ} (a : ℝ) (h : ZeroMarginals c X) : ZeroMarginals c (a • X) :=
  ⟨fun F => by rw [form_smul_law, h.1 F, mul_zero], fun G => by rw [form_smul_law, h.2 G, mul_zero]⟩

section OfFold

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The replaced records of B8's `ofFold` atom have zero marginals**: at `F₁, F₂, E₀, E₁`
(`replSet`), the change of `Replacements.toAtom` annihilates the constants at `ι`. -/
theorem zeroMarginals_ofFold (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : FrameFacts (middleFrame pr hne root W I hr bm h) (blockSquareAccepted pr)
      MainAnchor.paperQueries)
    (t' : Chg ⊕ Del) (ht' : t' ∈ replSet) :
    ZeroMarginals reservedCut
      (((ofFold pr h hne root W I hr bm C t ht0 ht1).toReplacements.toAtom hF).Δ t') := by
  unfold replSet at ht'
  rcases mem_union.mp ht' with hf | hm
  · obtain ⟨j, -, rfl⟩ := mem_image.mp hf
    rw [Replacements.toAtom_Δ_fold, ofFold_newMeas_fold]
    exact zeroMarginals_smul _ (zeroMarginals_signedFold hne root C t j)
  · obtain ⟨s, -, rfl⟩ := mem_image.mp hm
    rw [Replacements.toAtom_Δ_match, ofFold_newMeas_match]
    exact zeroMarginals_smul _ (zeroMarginals_matchRec pr h hne root s)

end OfFold

section Spec

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
variable (hW : Target.Weil) (In : FirstStageInputs blockOf)

/-- **The replaced fold and matching records of the atom of a class-three block**: `replSet` on a
middle block, none on an upper block. -/
noncomputable def replIdx {b : B} :
    (S : PaperBlockSpec blockOf b) → (SD : SpecData hW In S) →
      Finset (MiddleRefinement.atomOf hW In S SD).T
  | .upper _, _ => ∅
  | .middleUniform _, _ => replSet
  | .middleIndividual _, _ => replSet
  | .middleCoherent _, _ => replSet

omit [Fintype B] in
/-- **The replaced records of B7's atom have zero marginals** when the middle inputs are fold
components (`FoldSpec.toSpecData`, i.e. B8's `ofFold` on every middle block). -/
theorem zeroMarginals_atom {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S)
    (t' : (MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).T)
    (ht' : t' ∈ replIdx hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)) :
    ZeroMarginals reservedCut
      ((MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).Δ t') := by
  cases S with
  | upper U => exact absurd ht' (notMem_empty _)
  | middleUniform M =>
    exact zeroMarginals_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsU In M) t' ht'
  | middleIndividual M =>
    exact zeroMarginals_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsI In M) t' ht'
  | middleCoherent M =>
    exact zeroMarginals_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsC In M) t' ht'

omit [Fintype B] in
/-- **`zeroMarginals_atom` at the data priced at the bounds** (`FoldSpec.toSpecDataM`, RP): the
changes are those of `ofFold` (`ofFoldM_Δ`). -/
theorem zeroMarginals_atomM {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (bl sF aF ℓ sE aE : ℝ)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S)
    (t' : (MiddleRefinement.atomOf hW In S
      (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).T)
    (ht' : t' ∈ replIdx hW In S (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)) :
    ZeroMarginals reservedCut
      ((MiddleRefinement.atomOf hW In S
        (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).Δ t') := by
  cases S with
  | upper U => exact absurd ht' (notMem_empty _)
  | middleUniform M =>
    exact zeroMarginals_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsU In M) t' ht'
  | middleIndividual M =>
    exact zeroMarginals_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsI In M) t' ht'
  | middleCoherent M =>
    exact zeroMarginals_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsC In M) t' ht'

end Spec

/-! ## At B2's comparison law of the paper's data -/

section CL

open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.AnalyticCells (f1Cell)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The replaced fold and matching records of the comparison law at a class-three block `b`**
(the atom `.inl (.inr b)`): B7's `replSet` on a middle block, none on an upper block. -/
noncomputable def replCL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) :
    Finset (C.toK1.CL.T L (.inl (.inr b))) := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  exact replIdx hW (paperIn f1Cell) (specF hW A b) (C.toK1.blk b)

/-- **`eq:record:zero-marginal` at the paper's comparison law**: every replaced fold or matching
record of a middle block has a change with zero marginals at `ι`. -/
theorem zeroMarginals_CL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk)
    (t : C.toK1.CL.T L (.inl (.inr b))) (ht : t ∈ replCL C L b) :
    ZeroMarginals reservedCut (C.toK1.CL.Δ L (.inl (.inr b)) t) := by
  unfold replCL at ht
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget at *
  exact zeroMarginals_atomM hW (paperIn f1Cell) tPaper_nonneg tPaper_le_one _ _ _ _ _ _
    (specF hW A b) _ t ht

/-- **The records of the comparison law that carry a variance credit**: the replaced fold and
matching records of the middle blocks (`replCL`); nothing at the other atoms. -/
def InRepl (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) :
    (b : BlockAtom (PaperAtom Blk) (PaperJt) L) → C.toK1.CL.T L b → Prop
  | .inl (.inr b), t => t ∈ replCL C L b
  | _, _ => False

theorem zeroMarginals_of_inRepl (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ)
    (b : BlockAtom (PaperAtom Blk) (PaperJt) L) (t : C.toK1.CL.T L b) (h : InRepl C L b t) :
    ZeroMarginals reservedCut (C.toK1.CL.Δ L b t) := by
  rcases b with (q | b) | j
  · exact absurd h id
  · exact zeroMarginals_CL C L b t h
  · exact absurd h id

end CL

/-! ## At the data of the companion obligations -/

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperCapsPaper.UpperRecordTables}

/-- **The input `hz0`/`hzm` of the variance credit at the obligations' data**: a selection all of
whose records are replaced fold or matching records of middle blocks (`InRepl`) satisfies
`RecordsZeroMarginal`. -/
theorem recordsZeroMarginal_front (F : CompanionND.CompanionFrontND hW hMR hFour UpT)
    (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) (L : ℕ)
    (ω : Choice ((F.X hB hRR).data.CL.T L))
    (hω : ∀ b t e, ω b = some (t, e) → InRepl (F.toK.Up.toCmp hMR hFour) L b t) :
    RecordsZeroMarginal (F.X hB hRR).data L ω :=
  fun b t e h => zeroMarginals_of_inRepl (F.toK.Up.toCmp hMR hFour) L b t (hω b t e h)

end Sarkozy.OpsVariance
