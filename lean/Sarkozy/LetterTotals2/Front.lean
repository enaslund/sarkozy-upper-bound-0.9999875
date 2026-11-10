module

public import Sarkozy.LetterTotals2.Basic
public import Sarkozy.LetterTotals.Front

@[expose] public section

/-!
# The supremal letter totals at the data of the main statement (HX2)

HX2, 8 November 2026. At the block data `(F.X hB hRR).data` of a companion front `F`, HX's proved
type totals (`LetterTotals.symTotal_le_front`, `skewTotal_le_front`: `∑_𝔟 s_𝔟 ≤ SForm F` and
`∑_𝔟 a_𝔟 ≤ AForm F` at every scale) bound the letter totals of **every** lettering:

* **`totalsBdd_front`**: every lettering's totals are bounded uniformly in `L`;
* **`totalsLe_front`**: `TotalsLe (F.X hB hRR).data ℓ (letterSup …)` for every lettering, i.e.
  `hX` holds at the supremal totals, with no hypothesis beyond nonnegative prices;
* `letterSup_le_front`: `letterSup ≤ SForm F + AForm F` for every letter (crude);
* `letterSup_le_SForm`, `letterSup_le_AForm`: a letter carried by exactly one change type has
  supremal total at most `SForm F` or `AForm F` (HX's `σ`, now a fact about `letterSup` and not a
  restriction of the lettering).

The nonnegativity of the prices is a field of the class data (`ClassData.π_nonneg`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.LetterTotals2

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.Companion (TotalsLe)
open Sarkozy.LetterTotals (SForm AForm symTotal_le_front skewTotal_le_front)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.CompanionND (CompanionFrontND)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables} {C : Type} [DecidableEq C]

/-- **Every lettering has bounded letter totals** at the data of the main statement. -/
theorem totalsBdd_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ (F.X hB hRR).data.CL.π L b t e) : TotalsBdd (F.X hB hRR).data ℓ :=
  totalsBdd_of_types _ ℓ hπ (SForm F) (AForm F) (symTotal_le_front F hB hRR)
    (skewTotal_le_front F hB hRR)

/-- **`hX` at the supremal totals, for every lettering** at the data of the main statement. -/
theorem totalsLe_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ (F.X hB hRR).data.CL.π L b t e) :
    TotalsLe (F.X hB hRR).data ℓ (letterSup (F.X hB hRR).data ℓ) :=
  totalsLe_letterSup _ ℓ (totalsBdd_front F hB hRR ℓ hπ)

/-- The supremal total of every letter is at most `SForm F + AForm F`. -/
theorem letterSup_le_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ (F.X hB hRR).data.CL.π L b t e) (l : MLetter ⊕ C) :
    letterSup (F.X hB hRR).data ℓ l ≤ SForm F + AForm F :=
  letterSup_le_types _ ℓ hπ _ _ (symTotal_le_front F hB hRR) (skewTotal_le_front F hB hRR) l

/-- A letter carried by exactly the symmetric entries has supremal total at most `SForm F`. -/
theorem letterSup_le_SForm (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ C)
    (σ : MLetter ⊕ C) (hσ : ∀ L e, ℓ L e = σ ↔ e.2.2 = .sym) :
    letterSup (F.X hB hRR).data ℓ σ ≤ SForm F :=
  letterSup_le_of_sym _ ℓ σ hσ _ (symTotal_le_front F hB hRR)

/-- A letter carried by exactly the skew entries has supremal total at most `AForm F`. -/
theorem letterSup_le_AForm (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ C)
    (α : MLetter ⊕ C) (hα : ∀ L e, ℓ L e = α ↔ e.2.2 = .skew) :
    letterSup (F.X hB hRR).data ℓ α ≤ AForm F :=
  letterSup_le_of_skew _ ℓ α hα _ (skewTotal_le_front F hB hRR)

end Sarkozy.LetterTotals2
