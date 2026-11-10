module

public import Sarkozy.SignedDecompCrude.Gate
public import Sarkozy.FoldSymSkew.Constructor
public import Sarkozy.Rebase.Folds
public import Sarkozy.NormBoundsPaper3.Main
public import Sarkozy.NormBoundsPaper4.Main

@[expose] public section

/-!
# The four fold bounds and NB3's front without the signed decomposition (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(a),(b),(c),(e).

FS's `hNr4_of_newDecompF38` gives NB3's `hNr4` (the four fold bounds) from `NewDecomp` at any
`e_sg′ = esgF(p)` with `esgF(p) ≤ E_k` for `p ≥ X_k`, given C38's `FoldSides κ 38 0` and FS's
`SymSkewSides κ E`. With ND's `e_sg′ = esgCrude κRec nT ≤ 21`:

* **`symSkewSides21_check`** (kernel): `e_o(X_k) + 21 ≤ s_F`, `21 ≤ a_F`, `aNU Γ_X ≤ ℓ` on the
  rebased table `paperKappa` (RG's `symSkewSides_check` with `esgX k` replaced by `21`);
* **`hNr4_proved`**: `hNr4` at `paperKappa` for every `C`, with no hypothesis
  (RG's `foldSides38_paperKappa` for `FoldSides`);
* **`FrontN3ND`** (3 fields: `PCu`, `BA`, `UpB`): NB3's `FrontN3` with
  `SD := signedDecompInputs_proved`, `hEs := eOrthPaperInput` (FD) and `hNr4 := hNr4_proved`;
  **`FrontN3ND.toN3`**, **`FrontN3ND.toK`**.
-/

namespace Sarkozy.SignedDecompCrude

open Sarkozy.SignedDecomp
open Sarkozy.FoldSymSkew (SymSkewSides SpecNewDecompF hNr4_of_newDecompF38 aNU)
open Sarkozy.NormBoundsPaper4 (eo73)
open Sarkozy.HsumProof (paperKappa kSF kAF kL)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF analyticInputs)
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.BlockSpecPaper
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.NormBoundsPaper3 (SpecNormBoundsRest4 FrontN3)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.MainFinal (BlockAnalytic)
open Sarkozy.UpperCapsPaper (PrimeCertificatesUC UpperRecordTables UpperRecordBlocks)
open Sarkozy.MainCombined2 (FrontK)

/-- **FS's side conditions at `E = 21`** on the rebased table (kernel, exact rationals). -/
theorem symSkewSides21_check : ∀ k : Fin 33,
    eo73 k + 21 ≤ kSF k ∧ (21 : ℚ) ≤ kAF k ∧ aNU * gamX k ≤ kL k := by
  decide +kernel

theorem paperKappa_symSkewSides21 (k : Fin 33) : SymSkewSides paperKappa (fun _ => 21) k := by
  obtain ⟨h1, h2, h3⟩ := symSkewSides21_check k
  refine ⟨?_, ?_, ?_⟩
  · change (((eo73 k + 21 : ℚ)) : ℝ) ≤ (kSF k : ℝ); exact_mod_cast h1
  · change ((21 : ℚ) : ℝ) ≤ (kAF k : ℝ); exact_mod_cast h2
  · change ((aNU * gamX k : ℚ) : ℝ) ≤ (kL k : ℝ); exact_mod_cast h3

variable (hW : Target.Weil)

theorem specNewDecompF_of_new {esgF : ℕ → ℝ} {b : Blk} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecNew hW esgF S E →
      SpecNewDecompF hW esgF S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, H => H.2
  | .middleIndividual _, _, H => H.2
  | .middleCoherent _, _, H => H.2

variable {hW} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **ND's `CrudeSD` for every `C`** (`e_sg′ = esgCrude κRec nT`, the gates proved). -/
theorem crudeSD_proved (C : ComparisonPartsTC hW hMR hFour A) : CrudeSD (esgCrude κRec nT) C :=
  (estInputs C).toRecordInputs.toKN.toCrudeSD pieceGate_esgCrude

/-- **NB3's `hNr4` (the four fold bounds, `prop:signed-bounds`(a),(b),(e)) at the rebased table
for every `C`**, from ND's `NewDecomp` at `e_sg′ ≤ 21` (FS's `hNr4_of_newDecompF38`). -/
theorem hNr4_proved (C : ComparisonPartsTC hW hMR hFour A) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
        (C.blk b) :=
  hNr4_of_newDecompF38 hW A C.blk paperKappa (esgCrude κRec nT) (fun _ => 21)
    (fun k p hp => by
      obtain ⟨hX24, -, -, -⟩ := table_check k
      have := esgCrude_le (hX24.trans hp)
      push_cast
      exact this)
    Sarkozy.Rebase.foldSides38_paperKappa paperKappa_symSkewSides21
    (fun b i hb => specNewDecompF_of_new hW (specF hW A b) (C.blk b)
      ((crudeSD_proved C).new b i hb))

/-- **NB3's `FrontN3` without `SD`, `hEs`, `hNr4`** (3 fields, as in `FrontN3`). -/
structure FrontN3ND (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (UpT : UpperRecordTables) : Type 1 where
  /-- As in `FrontN3`. *Open*. -/
  PCu : PrimeCertificatesUC
  /-- As in `FrontN3`. *Open*. -/
  BA : BlockAnalytic
  /-- As in `FrontN3`. *Open*. -/
  UpB : UpperRecordBlocks hW (analyticInputs (PCu.toPC2'.toPC hW hMR hFour) BA) UpT

/-- `FrontN3ND` gives NB3's `FrontN3`: `SD := signedDecompInputs_proved`,
`hEs := eOrthPaperInput` (FD), `hNr4 := hNr4_proved`. -/
noncomputable def FrontN3ND.toN3 {UpT : UpperRecordTables} (F : FrontN3ND hW hMR hFour UpT) :
    FrontN3 hW hMR hFour UpT where
  PCu := F.PCu
  BA := F.BA
  UpB := F.UpB
  SD := signedDecompInputs_proved _
  hEs := Sarkozy.NormBoundsPaper4.eOrthPaperInput
  hNr4 := hNr4_proved _

/-- `MainCombined2.FrontK` from `FrontN3ND` (NB3's `FrontN3.toK`). -/
noncomputable def FrontN3ND.toK {UpT : UpperRecordTables} (F : FrontN3ND hW hMR hFour UpT) :
    FrontK hW hMR hFour UpT :=
  F.toN3.toK

end Sarkozy.SignedDecompCrude
