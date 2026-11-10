module

public import Sarkozy.MainFinalF1.K2
public import Sarkozy.SignedComponents.Priced
public import Sarkozy.HsumProof.PaperKappa

@[expose] public section





open Finset

namespace Sarkozy.MainFinalF1c

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
open Sarkozy.CancellationSteps Sarkozy.FirstStagePaper Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.MiddleRecords (MergeRepairBounds)
open Sarkozy.SignedComponents (FoldComponents FoldSpec DefectSpec NormBounds boundN boundN_mono
  ofFoldM ofFoldM_N_le ofFoldM_N_eq)
open Sarkozy.MainFinal (MiddleConsts NormSizes SpecNorm SpecUpperRec)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinalF1 (Blk bOf SignedSpec SpecNormBounds)
open Sarkozy.HsumProof (paperKappa)

/-- **The componentwise order of the piece constants** `(s_F, a_F, ℓ_t, s_E, a_E)`. -/
def KappaLe (κ κ' : MiddleConsts) : Prop :=
  κ.sF ≤ κ'.sF ∧ κ.aF ≤ κ'.aF ∧ κ.ℓ ≤ κ'.ℓ ∧ κ.sE ≤ κ'.sE ∧ κ.aE ≤ κ'.aE

theorem KappaLe.refl (κ : MiddleConsts) : KappaLe κ κ :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-! ## One middle block -/

section Frame

open Sarkozy.Labellings Sarkozy.ComparisonLawPaper

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **K1's `NormSizes` for `ofFoldM` from the twelve norm bounds** (the twin of K2's
`normSizes_of_bounds`): with the prices at constants `κ₀ ≤ κ` and the twelve norm bounds at `κ`
(`NB`), the prices are at most the bounds at `κ`. -/
theorem normSizes_ofFoldM (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' : ℝ} {κ₀ κ : MiddleConsts} (hle : KappaLe κ₀ κ)
    (NB : NormBounds pr h hne root W I hr b C t b' κ.sF κ.aF κ.ℓ κ.sE κ.aE) :
    NormSizes (ofFoldM pr h hne root W I hr b C t ht0 ht1 b' κ₀.sF κ₀.aF κ₀.ℓ κ₀.sE κ₀.aE).N
      κ b' r := by
  have hN : ∀ t' e, (ofFoldM pr h hne root W I hr b C t ht0 ht1 b' κ₀.sF κ₀.aF κ₀.ℓ κ₀.sE
      κ₀.aE).N t' e ≤ boundN r b' κ.sF κ.aF κ.ℓ κ.sE κ.aE t' e :=
    ofFoldM_N_le pr h hne root W I hr b C ht0 ht1 NB
      (boundN_mono hle.1 hle.2.1 hle.2.2.1 hle.2.2.2.1 hle.2.2.2.2)
  refine ⟨fun i => hN (.inl i) .sym, fun i => hN (.inl i) .skew,
    fun i => hN (.inr (.inl i)) .sym, fun i => hN (.inr (.inl i)) .skew, ?_,
    fun k => hN (.inr (.inr (.inr k))) .sym, fun k => hN (.inr (.inr (.inr k))) .skew⟩
  exact
    { sym_nonneg := fun _ => (ofFoldM pr h hne root W I hr b C t ht0 ht1 b' κ₀.sF κ₀.aF κ₀.ℓ κ₀.sE
        κ₀.aE).N_nonneg _ _
      skew_nonneg := fun _ => (ofFoldM pr h hne root W I hr b C t ht0 ht1 b' κ₀.sF κ₀.aF κ₀.ℓ
        κ₀.sE κ₀.aE).N_nonneg _ _
      sym_mirror := fun s k hk => by simpa [boundN, hk] using hN (.inr (.inr (.inl (s, k)))) .sym
      skew_mirror := fun s k hk => by
        simpa [boundN, hk] using hN (.inr (.inr (.inl (s, k)))) .skew
      sym_first := fun s => by simpa [boundN] using hN (.inr (.inr (.inl (s, 2)))) .sym
      skew_first := fun s => by simpa [boundN] using hN (.inr (.inr (.inl (s, 2)))) .skew }

end Frame

/-! ## The paper's blocks -/

variable (hW : Target.Weil) (In : FirstStageInputs bOf)

/-- **B7's `SpecData` of a block from the signed estimates, priced at `(κ, bl)`**: on a middle block
`ofFoldM` with the paper's fold components `paperComponents` at `t = 127/500` (the records of K2's
`SignedSpec.toSpecData`), priced at `max(optNorm, bound)` with the piece constants `κ` and the
least prime `bl`; on an upper block B2's inputs, as before. -/
noncomputable def SignedSpec.toSpecDataAt (κ : MiddleConsts) (bl : ℝ) {b : Blk}
    (S : PaperBlockSpec bOf b) (E : SignedSpec hW S) : SpecData hW In S :=
  FoldSpec.toSpecDataM hW In tPaper_nonneg tPaper_le_one bl κ.sF κ.aF κ.ℓ κ.sE κ.aE S
    (DefectSpec.toFoldSpec hW tPaper_nonneg tPaper_le_one S (SignedSpec.toDefect hW S E))

/-- **K1's `SpecNorm` at `κ` from the twelve norm bounds at `κ`, for the prices at `κ₀ ≤ κ`** (the
twin of K2's `specNorm_of_bounds`). -/
theorem specNormAt_of_bounds {b : Blk} (κ₀ κ : MiddleConsts) (bl : ℝ) (hle : KappaLe κ₀ κ) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecNormBounds hW In κ bl S E →
      SpecNorm hW In κ bl S (SignedSpec.toSpecDataAt hW In κ₀ bl S E)
  | .upper _, _, _ => trivial
  | .middleUniform _, _, NB =>
      normSizes_ofFoldM _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one hle NB
  | .middleIndividual _, _, NB =>
      normSizes_ofFoldM _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one hle NB
  | .middleCoherent _, _, NB =>
      normSizes_ofFoldM _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one hle NB

/-- **The prices of a middle block are the bounds**: `N = boundN` at `(κ, bl)` and the frame's
scale. `True` on an upper block. -/
def SpecPrices {b : Blk} (κ : MiddleConsts) (bl : ℝ) :
    (S : PaperBlockSpec bOf b) → SpecData hW In S → Prop
  | .upper _, _ => True
  | .middleUniform M, R => ∀ t' e, R.down.N t' e = boundN M.r bl κ.sF κ.aF κ.ℓ κ.sE κ.aE t' e
  | .middleIndividual M, R => ∀ t' e, R.down.N t' e = boundN M.r bl κ.sF κ.aF κ.ℓ κ.sE κ.aE t' e
  | .middleCoherent M, R => ∀ t' e, R.down.N t' e = boundN M.r bl κ.sF κ.aF κ.ℓ κ.sE κ.aE t' e

/-- **Under the twelve norm bounds at `(κ, bl)`, the prices at `(κ, bl)` are exactly the bounds**
(`ofFoldM_N_eq`). -/
theorem specPrices_at {b : Blk} (κ : MiddleConsts) (bl : ℝ) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecNormBounds hW In κ bl S E →
      SpecPrices hW In κ bl S (SignedSpec.toSpecDataAt hW In κ bl S E)
  | .upper _, _, _ => trivial
  | .middleUniform _, _, NB => ofFoldM_N_eq _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one NB
  | .middleIndividual _, _, NB => ofFoldM_N_eq _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one NB
  | .middleCoherent _, _, NB => ofFoldM_N_eq _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one NB

/-- **The upper blocks are unchanged**: the per-record bounds of an upper block transfer from K2's
`SignedSpec.toSpecData` to `toSpecDataAt` (they are the same inputs). -/
theorem specUpperRec_at {b : Blk} (κ : MiddleConsts) (bl : ℝ)
    {Cs Ca : UpIdx → ℝ} (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) →
      SpecUpperRec hW In Cs Ca hCs hCa S (SignedSpec.toSpecData hW In S E) →
      SpecUpperRec hW In Cs Ca hCs hCa S (SignedSpec.toSpecDataAt hW In κ bl S E)
  | .upper _, _, h => h
  | .middleUniform _, _, _ => trivial
  | .middleIndividual _, _, _ => trivial
  | .middleCoherent _, _, _ => trivial

/-- **The pricing constants of a block**: `paperKappa i` (the rebased `κ′`) on piece `i`; unused on
a band (an upper block), where `paperKappa 0` is a placeholder. -/
noncomputable def blockKappa (b : Blk) : MiddleConsts :=
  match blockSite b with
  | .inl i => paperKappa i
  | .inr _ => paperKappa 0

theorem blockKappa_eq {b : Blk} {i : Fin 33} (hs : blockSite b = .inl i) :
    blockKappa b = paperKappa i := by
  unfold blockKappa
  rw [hs]

end Sarkozy.MainFinalF1c
