module

public import Sarkozy.MainFinalF1c.Main

@[expose] public section

/-!
# The tail at TC's constants against the ledger, and the comparison with `final3d`

* **`tailTC_le_allowance`**: `S_tail + A_tail = 3/2¹⁵¹ ≤ 10⁻¹²`, the allowance that the paper's
  `T = S_E + A_E + S_oth + A_oth + T_K + S_u + A_u + 10⁻¹²` reserves ("The matching exponent";
  `NumericalFields/Reduced.lean`); exact rational arithmetic;
* **`tailTC_fit`**: an inequality of `final3d`'s form (tail entered as `11/10⁷⁰`) with `10⁻⁴⁴` to
  spare gives the same inequality at TC's tail bound: this is what `SAPartsTC.hsum` and
  `MainFinalObligations3e.hmid` ask beyond their `final3d` versions;
* **`ComparisonParts3.toTC`**: every `final3d` comparison input gives a `final3e` one (forget
  `Rp`, `hcap`);
* **`SAParts3.toTC`**: every `final3d` `hSA` input with `10⁻⁴⁴` to spare in `hsum` and constants
  `κ ≥ κ′ = paperKappa` gives the `final3e` one (the other eight fields are the same: the upper
  records `hR` read only the upper blocks, which RP's re-pricing leaves unchanged
  (`specUpperRec_at`), and the norm bounds `hN` only the middle blocks). Since RP, `final3e`
  prices the middle records at their bounds at `κ′` and `final3d` at their optimal norms, so the two
  comparison laws share their records (`ComparisonParts3.blk_toTC`) but not their prices.
-/

namespace Sarkozy.MainFinalF1c

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.MainFinal (midK2 midK3 midK4 midK5 pieceScale)
open Sarkozy.NumericalFields (bandBound)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3)
open Sarkozy.MainFinalF1 (Blk specF)

/-- **The tail total at TC's constants is within the ledger's `10⁻¹²` allowance.** -/
theorem tailTC_le_allowance : tailStTC + tailAtTC ≤ 1 / 10 ^ 12 := by
  rw [tailTC_eq]
  norm_num

/-- **`final3d`'s numerical form with `10⁻⁴⁴` to spare gives `final3e`'s.** -/
theorem tailTC_fit {X B : ℝ} (h : X + 11 / 10 ^ 70 + 1 / 10 ^ 44 ≤ B) :
    X + (tailStTC + tailAtTC) ≤ B := by
  have := tailTC_lt
  have h0 : (0 : ℝ) ≤ 11 / 10 ^ 70 := by norm_num
  linarith

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **`final3d`'s comparison inputs give `final3e`'s** (forget `Rp` and `hcap`). -/
def ComparisonParts3.toTC (C : MainFinalF1.ComparisonParts3 hW hMR hFour A) :
    ComparisonPartsTC hW hMR hFour A :=
  ⟨C.blkU⟩

/-- The signed block inputs of `final3d`'s comparison parts are those of `final3e`'s (RP: the K1
data then differ only in the prices of the middle records). -/
theorem ComparisonParts3.blk_toTC (C : MainFinalF1.ComparisonParts3 hW hMR hFour A) (b : Blk) :
    C.toK2.blk b = (ComparisonParts3.toTC C).blk b := rfl

/-- **`final3d`'s `hSA` inputs, with `10⁻⁴⁴` to spare in `hsum`, give `final3e`'s.** -/
noncomputable def SAParts3.toTC {C : MainFinalF1.ComparisonParts3 hW hMR hFour A}
    (S : MainFinalF1.SAParts3 hW hMR hFour A C)
    (hm : 12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (S.Cs β) (S.Ca β) (S.hCs β) (S.hCa β)).coefS d *
          bandBound targetDecay d β +
        (upperLedger (UpperRecords.bandWeights β) (S.Cs β) (S.Ca β) (S.hCs β) (S.hCa β)).coefA d *
          bandBound targetDecay d β) +
      ∑ i : Fin 33, (midK2 S.κ i * f1c2 i +
        (midK3 S.κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
      11 / 10 ^ 70 + 1 / 10 ^ 44 ≤ targetLedger.S + targetLedger.A)
    (hκP : ∀ i, KappaLe (HsumProof.paperKappa i) (S.κ i)) :
    SAPartsTC hW hMR hFour A (ComparisonParts3.toTC C) where
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR b k hb := specUpperRec_at hW (paperIn f1Cell) _ _ _ _ (specF hW A b)
    ((ComparisonParts3.toTC C).blk b) (S.hR b k hb)
  κ := S.κ
  hκ := S.hκ
  hκP := hκP
  hN := S.hN
  hsum := tailTC_fit hm

end Sarkozy.MainFinalF1c
