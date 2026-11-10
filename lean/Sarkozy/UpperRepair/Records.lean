module

public import Sarkozy.UpperRepair.NewGraphBlock
public import Sarkozy.UpperRepair.Kernel
public import Sarkozy.UpperRepair.Paper

@[expose] public section

/-!
# The paper's inputs of the 92 changed records (`def:upper-comparison`(b), (b′))

`paper/sections/26_upper_comparison.tex`, `def:upper-comparison`(b), (b′) and W8's `changeKind`:
of the `92` changed records of an upper block, `84` are repaired one way ((F7)), the `6` LE records
(state `LR`) are replaced by the LE mixture (`prop:le-mixture`) and the `2` nonaccepting EL records
(state `RL`) by the dense law (`prop:dense-comparison`).

* `RecInput pr hne t φ k`: the input of a record by its kind: `OneWayGraphInput` (one way, with
  `π^new = λ_𝔅(G^new)`) or `KernelInput` (mixture or dense law);
* `RecInput.toRepl`; `PaperBlockInputs pr hne`, **`PaperBlockInputs.toBlockRepl`**;
* **`UpperRecordData hW A`**: `UpperRepairData` with the replacing laws given by kind, and
  `toRepairData`. So `MainFinalObligations3g` can be filled from the paper-shaped inputs.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.PartVLaws (blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.BlockSpecPaper (PaperAnalyticInputs)
open Sarkozy.MainFinalF1 (specF Blk bOf bandIdx)
open Sarkozy.HsumProof (PaperLedgers)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The input of a changed record by its kind** (`changeKind`): one-way repair of
`λ_𝔅(G^new)`, LE mixture or dense EL law (`none` is never the kind of a changed record). -/
def RecInput (hne : UpperNonempty pr) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    Option ChangeKind → Type
  | some .oneWay => OneWayGraphInput pr hne t φ
  | some .leMixture => KernelInput pr hne t φ
  | some .denseEL => KernelInput pr hne t φ
  | none => ReplRecord pr hne t φ

variable {pr}

/-- The replacing law of a record from its input. -/
noncomputable def RecInput.toRepl {hne : UpperNonempty pr} {t : PType × PType}
    {φ : t.1.Pat × t.2.Pat} :
    (k : Option ChangeKind) → RecInput pr hne t φ k → ReplRecord pr hne t φ
  | some .oneWay, I => OneWayGraphInput.toRepl I
  | some .leMixture, I => KernelInput.toRepl I
  | some .denseEL, I => KernelInput.toRepl I
  | none, R => R

variable (pr) in
/-- **The paper's inputs of an upper block**: for every changed record, the input of its kind. -/
def PaperBlockInputs (hne : UpperNonempty pr) : Type :=
  ∀ (t : PType × PType) (φ : t.1.Pat × t.2.Pat), upperFate (true, ⟨t, φ⟩) = .changed →
    RecInput pr hne t φ (changeKind (true, ⟨t, φ⟩))

/-- The replacing laws of the block. -/
noncomputable def PaperBlockInputs.toBlockRepl {hne : UpperNonempty pr}
    (P : PaperBlockInputs pr hne) : BlockRepl pr hne :=
  fun t φ h => RecInput.toRepl _ (P t φ h)

/-- **`UpperRepairData` with the replacing laws given by kind** (`def:upper-comparison`(b),(b′)):
the one-way records from `OneWayGraphInput`, the LE and dense EL records from `KernelInput`. -/
structure UpperRecordData (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell) where
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The coefficients have the paper's state ledgers. Finite. -/
  hLed : PaperLedgers Cs Ca
  /-- The inputs of the changed records at every upper block. *Open* (analytic). -/
  rep : ∀ (b : Blk) (U : UpperBlockInputs bOf b), specF hW A b = .upper U →
    PaperBlockInputs (blockPrimes bOf b) (upperNe hW U)
  /-- `C^s_ρ ≤ Cs_{k,ρ} r_𝔅`. *Open* (numerical). -/
  hs : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).toBlockRepl.coef ρ .sym ≤ Cs (bandIdx b) ρ * U.r
  /-- `C^a_ρ ≤ Ca_{k,ρ} r_𝔅`. *Open* (numerical). -/
  ha : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).toBlockRepl.coef ρ .skew ≤ Ca (bandIdx b) ρ * U.r

/-- `UpperRepairData` from the inputs by kind. -/
noncomputable def UpperRecordData.toRepairData {hW : Target.Weil} {A : PaperAnalyticInputs f1Cell}
    (D : UpperRecordData hW A) : UpperRepairData hW A where
  Cs := D.Cs
  Ca := D.Ca
  hCs := D.hCs
  hCa := D.hCa
  hLed := D.hLed
  rep b U h := (D.rep b U h).toBlockRepl
  hs := D.hs
  ha := D.ha

end Sarkozy.UpperRepair
