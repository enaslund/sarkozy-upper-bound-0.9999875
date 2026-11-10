module

public import Sarkozy.NormBoundsPaper4.FoldBlock

@[expose] public section

/-!
# NB3's `hNr4` (the fold families) from the one-prime fold inputs (FD)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(a),(b),(e) at the paper's partition
and `paperKappa`.

* `paper_reflected`: the paper's components (`paperComponents`) are reflected
  (`def:record:mixture`(d); SGA's `blockComponents_reflected`);
* **`SpecFoldInputs`**: `FoldInputs` on a middle block (any root), `True` on an upper block;
* `specRest4_of_inputs`: NB3's `SpecNormBoundsRest4` from `SpecFoldInputs` on a block of piece `k`;
* **`hNr4_of_inputs`**: the field `hNr4` of NB3's `FrontN3` at the paper's partition and
  `paperKappa`, from `SpecFoldInputs` at every middle block (`fold_check` discharges the numerical
  side conditions).
-/

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedGram
open Sarkozy.SignedDecomp (XQ gamX rX cpX)
open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes paperAtomMap)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one MiddleEstimates)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.HsumProof (paperKappa kSF kAF paperKappa_nonneg)
open Sarkozy.NormBoundsPaper2 (blockLeast_facts24)
open Sarkozy.NormBoundsPaper3 (SpecNormBoundsRest4)

/-- **The paper's components are reflected** (`def:record:mixture`(d)). -/
theorem paper_reflected {b : Blk} {hne : MiddleNonempty (blockPrimes bOf b)}
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) : Reflected (paperComponents Dc) :=
  blockComponents_reflected _ _ _ _ _ _ _

/-- **The fold inputs of a block specification** (`True` on an upper block), at the piece
constants `κ`. -/
def SpecFoldInputs (hW : Target.Weil) {b : Blk} (κ : MiddleConsts) :
    (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => FoldInputs (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
      κ.sF κ.aF κ.ℓ
  | .middleIndividual M, E => FoldInputs (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
      κ.sF κ.aF κ.ℓ
  | .middleCoherent M, E => FoldInputs (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
      κ.sF κ.aF κ.ℓ

/-- **NB3's `SpecNormBoundsRest4` from the fold inputs** on a block of piece `k`. -/
theorem specRest4_of_inputs (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) (k : Fin 33) (hXb : XQ k ≤ blockLeast b) (hℓ : 0 ≤ κ.ℓ)
    (hsF : (((gamX k + eo73 k * rX k) ^ 2 + 627 / 500 * cpX k ^ 2 : ℚ) : ℝ) ≤ κ.sF)
    (haF : ((627 / 500 * cpX k ^ 2 : ℚ) : ℝ) ≤ κ.aF) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) →
      SpecFoldInputs hW κ S E → SpecNormBoundsRest4 hW In κ (blockLeast b) S E := by
  have hXb' : (XQ k : ℝ) ≤ blockLeast b := by exact_mod_cast hXb
  obtain ⟨-, hbp⟩ := blockLeast_facts24 b
  intro S E R
  match S, E, R with
  | .upper _, _, _ => trivial
  | .middleUniform _, E, R =>
    exact fold_paper _ _ _ _ _ _ _ _ _ (paper_reflected E.down.toDC) k hXb' hbp hℓ hsF haF R
  | .middleIndividual _, E, R =>
    exact fold_paper _ _ _ _ _ _ _ _ _ (paper_reflected E.down.toDC) k hXb' hbp hℓ hsF haF R
  | .middleCoherent _, E, R =>
    exact fold_paper _ _ _ _ _ _ _ _ _ (paper_reflected E.down.toDC) k hXb' hbp hℓ hsF haF R

/-- **The field `hNr4` of NB3's `FrontN3` from the fold inputs**, at the paper's partition and
`paperKappa`: the fold families `Fs`, `Fa` (`prop:signed-bounds`(a),(b),(e)) are discharged from
`prop:signed-bounds`(c) at one prime and the component norms. -/
theorem hNr4_of_inputs (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b))
    (R : ∀ b i, blockSite b = .inl i →
      SpecFoldInputs hW (paperKappa i) (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
        (blk b) := by
  intro b i hs
  have hXb : XQ i ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact h
  obtain ⟨c1, c2, -, -⟩ := fold_check i
  have hsF : (((gamX i + eo73 i * rX i) ^ 2 + 627 / 500 * cpX i ^ 2 : ℚ) : ℝ) ≤
      (paperKappa i).sF := by
    change _ ≤ ((kSF i : ℚ) : ℝ)
    exact_mod_cast c1
  have haF : ((627 / 500 * cpX i ^ 2 : ℚ) : ℝ) ≤ (paperKappa i).aF := by
    change _ ≤ ((kAF i : ℚ) : ℝ)
    exact_mod_cast c2
  exact specRest4_of_inputs hW (paperIn f1Cell) (paperKappa i) i hXb (paperKappa_nonneg i).2.2.1
    hsF haF (specF hW A b) (blk b) (R b i hs)

end Sarkozy.NormBoundsPaper4
