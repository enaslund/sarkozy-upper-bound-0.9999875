module

public import Sarkozy.SignedEstimates.Final

@[expose] public section



namespace Sarkozy.SignedEstimates

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.PartVLaws (PaperBlockSpec paperAtomMap blockPrimes)
open Sarkozy.FirstStagePaper Sarkozy.PartV Sarkozy.BlockSpecPaper
open Sarkozy.PaperNumbers (paperCell)

theorem paperMiddleEstimates_η (hW : Target.Weil) (b : Blk)
    (hne : MiddleNonempty (blockPrimes bOf b)) (i) :
    (paperMiddleEstimates hW b hne).η i = 10 / (blockPrimes bOf b i : ℝ) := rfl

theorem paperMiddleEstimates_e (hW : Target.Weil) (b : Blk)
    (hne : MiddleNonempty (blockPrimes bOf b)) (i) :
    (paperMiddleEstimates hW b hne).e i =
      2 * (1 / (blockPrimes bOf b i : ℝ)) /
        ((1 - 3 * (1 / (blockPrimes bOf b i : ℝ))) * (1 - 4 * (1 / (blockPrimes bOf b i : ℝ)))) :=
  e0_eq_paper (by
    have h : (16777216 : ℝ) ≤ blockPrimes bOf b i := by exact_mod_cast blockPrime_ge b i
    linarith)

/-- The upper-block part of K2's `SignedSpec`. -/
def UpperSpec.ofSigned (hW : Target.Weil) {b : Blk} :
    (S : PaperBlockSpec bOf b) → SignedSpec hW S → UpperSpec hW S
  | .upper _, U => U
  | .middleUniform _, _ => PUnit.unit
  | .middleIndividual _, _ => PUnit.unit
  | .middleCoherent _, _ => PUnit.unit

theorem toSigned_ofSigned_upper (hW : Target.Weil) {b : Blk} (U) (E : SignedSpec hW
    (PaperBlockSpec.upper (blockOf := bOf) (b := b) U)) :
    UpperSpec.toSigned hW _ (UpperSpec.ofSigned hW _ E) = E := rfl

/-- **Every `ComparisonParts2` gives a `ComparisonParts3`** (drop the middle blocks). -/
noncomputable def ComparisonParts3.ofCP2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    (C : ComparisonParts2 hW hMR hFour A) : ComparisonParts3 hW hMR hFour A where
  clique := C.clique
  blkU b := UpperSpec.ofSigned hW _ (C.blk b)
  Rp := C.Rp
  hcap := C.hcap

end Sarkozy.SignedEstimates
