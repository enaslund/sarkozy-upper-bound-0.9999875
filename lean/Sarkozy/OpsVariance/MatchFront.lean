module

public import Sarkozy.OpsVariance.MatchCen
public import Sarkozy.OpsVariance.ZeroMarginalPaper

@[expose] public section

/-!
# The matching record laws at the paper's comparison law (record laws and (Cen))

`paper/sections/22_variance.tex`, `lem:var-gain` (Cen), `lem:record:paired-e-bridge`(b),
`def:record:eligible`; `paper/sections/09_comparison_theorem.tex`, `def:cp4`(b) ("diagonal copies
of actual half marginals of `t`, in the applications").

At a matching record `E_s` of a middle block, B7's norm envelope is `env = Diag_ι(m_+)` with `m_+`
the half marginal of the record `Π_{E_s}` of V1's middle field laws. So the half marginal `envM` of
`Selection.lean` is `m_+` (`halfMarginalPlus_diagonalLaw`), and the record law `Π_{E_s}` supplies
the inputs `hw`, `hp`, `hn`, `ht`, `hcen` of `hres_of_restoration` for the aligned matching
classes:

* `RecordLawIs w Dt κ`: `w` is a record law for the record with norm envelopes `Dt` (the five
  pointwise inputs of `hres_of_restoration`); `RecordLawAt`: one exists;
* **`recordLawIs_ofFold`**: at B8's `ofFold` atom, `Π_{E_s}` (`blockMatch`) is a record law for
  `E_s`, with `κ = 3/(b₀ − 3)` for any `7 ≤ b₀ ≤` the primes of the block (`b₀ = X_i` gives the
  piece value `k_{E,i}` of `eq:variance:pieces`);
* `matchIdx`, `matchLawIdx`, **`matchRecord_atom`**: the same at B7's atom of a class-three block
  with fold-component inputs (`matchLawIdx` is `Π_{E_s}` at `E_s`, `0` elsewhere);
  `matchRecord_atomM`, the twin at the data priced at the bounds (`FoldSpec.toSpecDataM`, RP; the
  record laws are those of `ofFold`), which the front uses;
* `matchCL`, `matchLawCL`, **`matchRecord_CL`**: the same at B2's comparison law of the obligations'
  data (unfolding the irreducible `comparisonLawTarget` once), with `b₀` the least prime of the
  block (`blockLeast`), i.e. `κ_E = 3/(b − 3)`; `matchCL_subset_replCL`: the matching records are
  replaced records, so their changes have zero marginals (`zeroMarginals_CL`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.Variance
open Sarkozy.Labellings (matchGraph matching)
open Sarkozy.CancellationSteps (PaperJ0 PaperJt paperM0 paperTail)
open Sarkozy.BlockSpecPaper (PaperAnalyticInputs paperIn blockLeast)

/-- **`w` is a record law for the record `t` with norm envelopes `Dt`** (the inputs `hw`, `hp`,
`hn`, `ht`, `hcen` of `hres_of_restoration` at one block): `w ≥ 0`, both half marginals are the
half marginal of the norm envelope of `t` (of either type), symmetric at `ι`, centred norm
`≤ κ`. -/
def RecordLawIs {Y : Type} [Fintype Y] [DecidableEq Y] (w : (Slot → Y) → ℝ)
    (Dt : ChangeType → ((Slot → Y) → ℝ) →ₗ[ℝ] ℝ) (κ : ℝ) : Prop :=
  (∀ z, 0 ≤ w z) ∧
    (∀ e, plusMarginal reservedCut w = Comparison.halfMarginalPlus reservedCut (Dt e)) ∧
    minusMarginal reservedCut w = plusMarginal reservedCut w ∧
    (∀ G H : (reservedCut.Half → Y) → ℝ,
      reservedCut.form (signedIntegral w) G H = reservedCut.form (signedIntegral w) H G) ∧
    CentredNormLe reservedCut (signedIntegral w) (plusMarginal reservedCut w) κ

/-- **The record-law inputs at a record `t` of an atom**: some record law exists. -/
structure RecordLawAt {Y : Type} [Fintype Y] [DecidableEq Y]
    (Dt : ChangeType → ((Slot → Y) → ℝ) →ₗ[ℝ] ℝ) (κ : ℝ) : Prop where
  ex : ∃ w : (Slot → Y) → ℝ, RecordLawIs w Dt κ

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The matching record law at B8's `ofFold` atom is `Π_{E_s}`**, the record of V1's middle
field laws (`blockMatch`). -/
theorem recordLawIs_ofFold (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : FrameFacts (middleFrame pr hne root W I hr bm h) (blockSquareAccepted pr)
      MainAnchor.paperQueries)
    (s : Fin 2) (b₀ : ℕ) (hb₀ : 7 ≤ b₀) (hle : ∀ i, b₀ ≤ pr i) :
    RecordLawIs (blockMatch pr hne root s).weight
      (((ofFold pr h hne root W I hr bm C t ht0 ht1).toReplacements.toAtom hF).D
        (.inl (.inr (.inl s)))) (3 / ((b₀ : ℝ) - 3)) := by
  refine ⟨(blockMatch pr hne root s).nonneg, fun e => ?_,
    blockMatch_minus pr hne root s, blockMatch_symm pr hne root s,
    centredNormLe_blockMatch pr hne root s b₀ hb₀ hle⟩
  change _ = Comparison.halfMarginalPlus reservedCut (reservedCut.diagonalLaw
    (plusMarginal reservedCut (midComponent (middleBlockFieldLaws pr hne root)
      (true, ⟨PType.S, s⟩)).weight))
  rw [halfMarginalPlus_diagonalLaw]

/-- **The matching record laws of a middle block**: `Π_{E_s}` at the matching record `E_s`, `0` at
the other records. -/
noncomputable def matchLawOf (hne : MiddleNonempty pr) : Chg ⊕ Del → (Slot → BlockLabel pr) → ℝ
  | .inl (.inr (.inl s)) =>
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2) (midEmission (matching s))).weight
  | _ => fun _ => 0

theorem matchLawOf_match (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (s : Fin 2) :
    matchLawOf pr hne (.inl (.inr (.inl s))) = (blockMatch pr hne root s).weight :=
  rfl

/-- The matching record law at B8's `ofFold` atom exists. -/
theorem recordLaw_ofFold (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : FrameFacts (middleFrame pr hne root W I hr bm h) (blockSquareAccepted pr)
      MainAnchor.paperQueries)
    (s : Fin 2) (b₀ : ℕ) (hb₀ : 7 ≤ b₀) (hle : ∀ i, b₀ ≤ pr i) :
    RecordLawAt (((ofFold pr h hne root W I hr bm C t ht0 ht1).toReplacements.toAtom hF).D
      (.inl (.inr (.inl s)))) (3 / ((b₀ : ℝ) - 3)) :=
  ⟨⟨_, recordLawIs_ofFold pr h hne root W I hr bm C ht0 ht1 hF s b₀ hb₀ hle⟩⟩

end Frame

section Spec

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
variable (hW : Target.Weil) (In : FirstStageInputs blockOf)

/-- **The matching records of the atom of a class-three block**: `E₀, E₁` on a middle block,
none on an upper block. -/
noncomputable def matchIdx {b : B} :
    (S : PaperBlockSpec blockOf b) → (SD : SpecData hW In S) →
      Finset (MiddleRefinement.atomOf hW In S SD).T
  | .upper _, _ => ∅
  | .middleUniform _, _ => univ.image fun s : Fin 2 => (.inl (.inr (.inl s)) : Chg ⊕ Del)
  | .middleIndividual _, _ => univ.image fun s : Fin 2 => (.inl (.inr (.inl s)) : Chg ⊕ Del)
  | .middleCoherent _, _ => univ.image fun s : Fin 2 => (.inl (.inr (.inl s)) : Chg ⊕ Del)

/-- **The matching record laws of the atom of a class-three block** (`matchLawOf` on a middle
block, `0` on an upper block). -/
noncomputable def matchLawIdx {b : B} :
    (S : PaperBlockSpec blockOf b) → (SD : SpecData hW In S) →
      (MiddleRefinement.atomOf hW In S SD).T → (Slot → BlockLabel (blockPrimes blockOf b)) → ℝ
  | .upper _, _ => fun _ _ => 0
  | .middleUniform M, _ => matchLawOf _ M.hne
  | .middleIndividual M, _ => matchLawOf _ M.hne
  | .middleCoherent M, _ => matchLawOf _ M.hne

omit [Fintype B] in
/-- The matching records are among the replaced records. -/
theorem matchIdx_subset_replIdx {b : B} (S : PaperBlockSpec blockOf b) (SD : SpecData hW In S) :
    matchIdx hW In S SD ⊆ replIdx hW In S SD := by
  cases S with
  | upper U => exact empty_subset _
  | middleUniform M => exact subset_union_right
  | middleIndividual M => exact subset_union_right
  | middleCoherent M => exact subset_union_right

omit [Fintype B] in
/-- **The matching record laws at B7's atom** of a class-three block with fold-component inputs. -/
theorem matchRecord_atom {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S) (b₀ : ℕ) (hb₀ : 7 ≤ b₀)
    (hle : ∀ i, b₀ ≤ blockPrimes blockOf b i)
    (t' : (MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).T)
    (ht' : t' ∈ matchIdx hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)) :
    RecordLawIs (matchLawIdx hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC) t')
      ((MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).D t')
      (3 / ((b₀ : ℝ) - 3)) := by
  cases S with
  | upper U => exact absurd ht' (notMem_empty _)
  | middleUniform M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp ht'
    exact recordLawIs_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsU In M) s b₀ hb₀ hle
  | middleIndividual M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp ht'
    exact recordLawIs_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsI In M) s b₀ hb₀ hle
  | middleCoherent M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp ht'
    exact recordLawIs_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsC In M) s b₀ hb₀ hle

omit [Fintype B] in
/-- **`matchRecord_atom` at the data priced at the bounds** (`FoldSpec.toSpecDataM`, RP): the record
laws are those of `ofFold` (`ofFoldM_D`). -/
theorem matchRecord_atomM {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (bl sF aF ℓ sE aE : ℝ)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S) (b₀ : ℕ) (hb₀ : 7 ≤ b₀)
    (hle : ∀ i, b₀ ≤ blockPrimes blockOf b i)
    (t' : (MiddleRefinement.atomOf hW In S
      (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).T)
    (ht' : t' ∈ matchIdx hW In S (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)) :
    RecordLawIs (matchLawIdx hW In S (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC) t')
      ((MiddleRefinement.atomOf hW In S
        (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).D t')
      (3 / ((b₀ : ℝ) - 3)) := by
  cases S with
  | upper U => exact absurd ht' (notMem_empty _)
  | middleUniform M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp ht'
    exact recordLawIs_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsU In M) s b₀ hb₀ hle
  | middleIndividual M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp ht'
    exact recordLawIs_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsI In M) s b₀ hb₀ hle
  | middleCoherent M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp ht'
    exact recordLawIs_ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      FC.down ht0 ht1 (factsC In M) s b₀ hb₀ hle

end Spec

section CL

open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.AnalyticCells (f1Cell)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- The least prime of a block is at least `7`, and at most every prime of the block. -/
theorem blockLeast_facts' (b : Blk) :
    7 ≤ blockLeast b ∧ ∀ i, blockLeast b ≤ blockPrimes bOf b i := by
  refine ⟨?_, fun i => BlockSpecPaper.blockLeast_le b i⟩
  obtain ⟨j, hj⟩ := BlockSpecPaper.blockLeast_mem (cell := f1Cell) b
  rw [← hj]
  exact (classThree_blockPrimes b).ge7 j

/-- **The matching records of the comparison law at a class-three block `b`**. -/
noncomputable def matchCL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) :
    Finset (C.toK1.CL.T L (.inl (.inr b))) := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  exact matchIdx hW (paperIn f1Cell) (specF hW A b) (C.toK1.blk b)

/-- **The matching record laws of the comparison law at a class-three block `b`**: `Π_{E_s}` at
the matching records of a middle block (`matchLawIdx`), `0` elsewhere. -/
noncomputable def matchLawCL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) :
    C.toK1.CL.T L (.inl (.inr b)) →
      (Slot → BlockFrame.BlockLabel paperM0 (paperAtomMap bOf) paperTail L (.inl (.inr b))) →
        ℝ := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  exact matchLawIdx hW (paperIn f1Cell) (specF hW A b) (C.toK1.blk b)

/-- **The matching record laws at the paper's comparison law**: at every matching record of a
middle block, `Π_{E_s}` (`matchLawCL`) is a record law: it supplies `hw`, `hp`, `hn`, `ht` and
(Cen) with `κ_E = 3/(b − 3)`, `b` the least prime of the block. -/
theorem matchRecord_CL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk)
    (t : C.toK1.CL.T L (.inl (.inr b))) (ht : t ∈ matchCL C L b) :
    RecordLawIs (matchLawCL C L b t) (C.toK1.CL.D L (.inl (.inr b)) t)
      (3 / ((blockLeast b : ℝ) - 3)) := by
  unfold matchCL at ht
  unfold matchLawCL
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget at *
  exact matchRecord_atomM hW (paperIn f1Cell) tPaper_nonneg tPaper_le_one _ _ _ _ _ _
    (specF hW A b) _
    (blockLeast b) (blockLeast_facts' b).1 (blockLeast_facts' b).2 t ht

/-- The matching records are replaced records (so they also have zero marginals). -/
theorem matchCL_subset_replCL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk) :
    matchCL C L b ⊆ replCL C L b := by
  unfold matchCL replCL
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  exact matchIdx_subset_replIdx hW (paperIn f1Cell) (specF hW A b) (C.toK1.blk b)

end CL

end Sarkozy.OpsVariance
