module

public import Sarkozy.LetterTotals.Basic
public import Sarkozy.LetterTotals.Totals
public import Sarkozy.LetterTotals.MiddleNum
public import Sarkozy.LetterTotals.UpperNum
public import Sarkozy.E1Closure.Main

@[expose] public section

/-!
# The two formal totals at the data of the main statement (HX)

HX, 8 November 2026. `Totals.lean`'s `symTotal_le`, `skewTotal_le` at the block data
`(F.X hB hRR).data` of the companion front, where every hypothesis is already proved by the chain
that proves `hSA`:

* the comparison inputs are `(F.toK.Up.toCmp hMR hFour).toK1` (TC's `ComparisonPartsTC.toK1`), with
  the clique bound `12/2^{534}` (C10, `cliquePrice_le`) and the tail numbers
  `S_tail = tailStTC`, `A_tail = tailAtTC` (TC);
* `UpperRecs` is UR's `UpperRepairDataS.upperRecs` (from `F.rep`, `F.hs`, `F.ha` and `UpT`);
* the middle norm sizes are `specNorm_of_bounds` of `hNG` (ND's proved norm bounds), at
  `κ = paperKappa` (`paperKappa_nonneg`); since RP, `specNormAt_of_bounds`, as the middle records
  are priced at their bounds at `κ′ = paperKappa` (`SAPartsTC.hκP`).

**`SForm F`**, **`AForm F`**: the two explicit bounds,
`12/2^{534} + upperS(Up) + middleS(paperKappa) + tailStTC` and
`12/2^{534} + upperA(Up) + middleA(paperKappa) + tailAtTC`. They depend on the front only through
the upper record tables `Up.Cs`, `Up.Ca` (which `UpT.hLed` bounds by `c ≤ 5/4` times the paper's
ledgers). **`symTotal_le_front`**, **`skewTotal_le_front`**: at every scale,
`∑_𝔟 s_𝔟 ≤ SForm F` and `∑_𝔟 a_𝔟 ≤ AForm F`. `SForm_add_AForm`: their sum is the left side of
`hSA`'s numerical inequality (`hsum_scaled`), so the split loses nothing. `SForm_le`, `AForm_le`:
with the middle totals evaluated (`MiddleNum.lean`), `SForm F ≤ upperS + 0.0179 + 10⁻⁴⁵` and
`AForm F ≤ upperA + 0.8171 + 10⁻⁴⁵`; only the upper sums are not evaluated. `SForm_le_ledgers`:
with UR's scaled ledgers (`UpperNum.lean`), `SForm F ≤ c · upperSQ + 0.0179 + 10⁻⁴⁵`, where
`c ≤ 5/4` is the front's upper scale and `upperSQ` a rational number fixed by the paper's tables.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.LetterTotals

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.BlockSpecPaper
open Sarkozy.UpperComparison (upperLedger upperDegrees)
open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk analyticInputs SpecNormBounds)
open Sarkozy.MainFinalF1c (FinalBlockData3e SAPartsTC ComparisonPartsTC midOthersK1 tailStTC
  tailAtTC)
open Sarkozy.NumericalFields (KappaNonneg bandBound)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.HsumProof (paperKappa paperKappa_nonneg)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.MainCombined (dvG hmidG)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-! ## At TC's block data -/

/-- **The symmetric total at TC's block data** (`FinalBlockData3e.toK1`): every hypothesis of
`symTotal_le` is a field of `SAPartsTC` or proved by TC (clique bound, tail numbers). -/
theorem symTotal_le_3e (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (D : FinalBlockData3e hW hMR hFour)
    (S : SAPartsTC hW hMR hFour (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) D.Cmp)
    (hmid : ∀ L, midOthersK1 D.Cmp.toK1 D.MR L +
      max (∑ β, D.MR.toPrefix.KL β) (∑ β, D.MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + (tailStTC + tailAtTC)) ≤ targetLedger.T)
    (L : ℕ) :
    ∑ b, symTotal ((D.toK1 hB S hmid).data.CL.π L) b ≤
      12 / 2 ^ 534 + upperS S.Cs S.Ca S.hCs S.hCa + middleS S.κ + tailStTC :=
  symTotal_le hB hRR D.Cmp.toK1 D.Cmp.cliquePrice_le S.Cs S.Ca S.hCs S.hCa S.hR S.κ S.hκ
    (fun b i hs => MainFinalF1c.specNormAt_of_bounds hW (paperIn f1Cell)
      (MainFinalF1c.blockKappa b) (S.κ i) (blockLeast b)
      (by rw [MainFinalF1c.blockKappa_eq hs]; exact S.hκP i)
      (specF hW (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) b) (D.Cmp.blk b) (S.hN b i hs)) L

/-- **The skew total at TC's block data**. -/
theorem skewTotal_le_3e (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (D : FinalBlockData3e hW hMR hFour)
    (S : SAPartsTC hW hMR hFour (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) D.Cmp)
    (hmid : ∀ L, midOthersK1 D.Cmp.toK1 D.MR L +
      max (∑ β, D.MR.toPrefix.KL β) (∑ β, D.MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + (tailStTC + tailAtTC)) ≤ targetLedger.T)
    (L : ℕ) :
    ∑ b, skewTotal ((D.toK1 hB S hmid).data.CL.π L) b ≤
      12 / 2 ^ 534 + upperA S.Cs S.Ca S.hCs S.hCa + middleA S.κ + tailAtTC :=
  skewTotal_le hB hRR D.Cmp.toK1 D.Cmp.cliquePrice_le S.Cs S.Ca S.hCs S.hCa S.hR S.κ S.hκ
    (fun b i hs => MainFinalF1c.specNormAt_of_bounds hW (paperIn f1Cell)
      (MainFinalF1c.blockKappa b) (S.κ i) (blockLeast b)
      (by rw [MainFinalF1c.blockKappa_eq hs]; exact S.hκP i)
      (specF hW (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) b) (D.Cmp.blk b) (S.hN b i hs)) L

/-! ## At the companion front -/

variable {UpT : UpperRecordTables}

/-- **The symmetric bound of the front**: `12/2^{534} + upperS + middleS(paperKappa) + tailStTC`,
at the front's upper record tables. -/
noncomputable def SForm (F : CompanionFrontND hW hMR hFour UpT) : ℝ :=
  12 / 2 ^ 534 + upperS F.toK.Up.Cs F.toK.Up.Ca F.toK.Up.hCs F.toK.Up.hCa + middleS paperKappa +
    tailStTC

/-- **The skew bound of the front**: `12/2^{534} + upperA + middleA(paperKappa) + tailAtTC`. -/
noncomputable def AForm (F : CompanionFrontND hW hMR hFour UpT) : ℝ :=
  12 / 2 ^ 534 + upperA F.toK.Up.Cs F.toK.Up.Ca F.toK.Up.hCs F.toK.Up.hCa + middleA paperKappa +
    tailAtTC

/-- **`∑_𝔟 s_𝔟 ≤ SForm F` at every scale**, at the data of the main statement. -/
theorem symTotal_le_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (L : ℕ) :
    ∑ b, symTotal ((F.X hB hRR).data.CL.π L) b ≤ SForm F :=
  symTotal_le_3e hB hRR _ _ _ L

/-- **`∑_𝔟 a_𝔟 ≤ AForm F` at every scale**, at the data of the main statement. -/
theorem skewTotal_le_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (L : ℕ) :
    ∑ b, skewTotal ((F.X hB hRR).data.CL.π L) b ≤ AForm F :=
  skewTotal_le_3e hB hRR _ _ _ L

/-- **The split loses nothing**: `SForm F + AForm F` is the left side of `hSA`'s numerical
inequality (`SAPartsTC.hsum`) at the front's data, plus one more clique term `12/2^{534}`. -/
theorem SForm_add_AForm (F : CompanionFrontND hW hMR hFour UpT) :
    SForm F + AForm F = 12 / 2 ^ 534 + (12 / 2 ^ 534 +
      Uup F.toK.Up.Cs F.toK.Up.Ca F.toK.Up.hCs F.toK.Up.hCa +
      ∑ i : Fin 33, (MainFinal.midK2 paperKappa i * AnalyticCells.f1c2 i +
        (MainFinal.midK3 paperKappa i + MainFinal.midK4 i * MainFinal.pieceScale i +
          MainFinal.midK5 i * MainFinal.pieceScale i ^ 2) * AnalyticCells.f1c3 i) +
      (tailStTC + tailAtTC)) := by
  unfold SForm AForm
  rw [← upperS_add_upperA, ← middleS_add_middleA]
  generalize (12 : ℝ) / 2 ^ 534 = c
  ring

/-- **`SForm` with the middle part evaluated**: `SForm F ≤ 12/2^{534} + upperS + 0.0179 + tailStTC`
(`middleS_paperKappa`). -/
theorem SForm_le (F : CompanionFrontND hW hMR hFour UpT) :
    SForm F ≤ 12 / 2 ^ 534 + upperS F.toK.Up.Cs F.toK.Up.Ca F.toK.Up.hCs F.toK.Up.hCa +
      179 / 10000 + tailStTC := by
  unfold SForm
  exact add_le_add (add_le_add le_rfl middleS_paperKappa) le_rfl

/-- **`AForm` with the middle part evaluated**: `AForm F ≤ 12/2^{534} + upperA + 0.8171 + tailAtTC`
(`middleA_paperKappa`). -/
theorem AForm_le (F : CompanionFrontND hW hMR hFour UpT) :
    AForm F ≤ 12 / 2 ^ 534 + upperA F.toK.Up.Cs F.toK.Up.Ca F.toK.Up.hCs F.toK.Up.hCa +
      8171 / 10000 + tailAtTC := by
  unfold AForm
  exact add_le_add (add_le_add le_rfl middleA_paperKappa) le_rfl

/-- **`SForm` at the paper's ledgers**: `SForm F ≤ 12/2^{534} + c · upperSQ + 0.0179 + tailStTC`,
with `c` the front's upper scale (`1 ≤ c ≤ 5/4`, `ScaledLedgers c`) and `upperSQ` the rational
symmetric upper total at the paper's state ledgers (`upperS_le_scaled`). -/
theorem SForm_le_ledgers (F : CompanionFrontND hW hMR hFour UpT) :
    SForm F ≤ 12 / 2 ^ 534 + F.toK.Up.c * (upperSQ : ℝ) + 179 / 10000 + tailStTC :=
  (SForm_le F).trans (add_le_add (add_le_add (add_le_add le_rfl
    (upperS_le_scaled _ _ _ _ F.toK.Up.hc F.toK.Up.hLed)) le_rfl) le_rfl)

end Sarkozy.LetterTotals
