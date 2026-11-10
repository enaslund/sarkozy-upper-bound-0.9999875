module

public import Sarkozy.LetterTotals2.Front
public import Sarkozy.LetterTotals.Main
public import Sarkozy.BlockRows.Main

@[expose] public section

/-!
# The companion statement with `hX` proved at the supremal letter totals (`main_goal_rebased_hx2`)

HX2, 8 November 2026. In RW's `CompanionObligationsRW` the lettering `ℓ` and the letter bounds `X`
are free data (D), and `X` occurs only in `hX0`, `hX : TotalsLe … ℓ X`, `hC` and (through `Cv`)
`hCv`. The comparison series is monotone in `X` (`c ≥ 0`, `series_mono`), and the smallest `X`
with `hX` is the supremal letter total `letterSup … ℓ` (`letterSup_le`). So `X` can be taken to be
`letterSup … ℓ`, and then `hX` and `hX0` are theorems for **every** lettering
(`totalsLe_front`, from HX's proved type totals). This is a transport of the same data, not a
restriction of it:

* **`CompanionObligationsHX2`**: RW's obligations without `X`, `hX0`, `hX`; the comparison series
  `hC` is stated at `letterSup … ℓ`. Every other field is a verbatim copy of RW's. 32 fields.
* **`toRW`** (the bridge, `X := letterSup … ℓ`); **`ofRW`** (**every** RW obligation set gives an
  HX2 one: `Cv` is replaced by the series' sum at `letterSup … ℓ`, which is at most RW's `Cv`;
  nothing else changes); `ofRW_toRW` (the round trip `HX2 → RW → HX2` is the identity);
  `toRW_ofRW_X` (the round trip `RW → HX2 → RW` lowers `X` to the supremal totals);
  **`nonempty_iff`**: RW's and HX2's obligations are satisfiable together.
* **`main_goal_rebased_hx2`**: `Target.SarkozyBound TargetGoal.epsGoal`, by `main_goal_rebased_rw`
  at `O.toRW`.

**What this does and does not do.** The field `hX` is closed without strengthening. Its content is
not removed: `hC` at `letterSup` asks for the comparison series at the *actual* supremal letter
totals, so it is no longer a finite numerical claim. The per-letter bounds that RW's `hX` and
`hC` asked for separately are now one claim. A finite numerical certificate for it is any `X`
with RW's `hX` and RW's `hC`, `hCv` at `X` (`hC_of_le`; HX's symmetric-letter route `hC_of_sym`
is one such certificate, now a sufficient condition and not a restriction).
-/

namespace Sarkozy.LetterTotals2

open Filter Finset Function
open scoped Topology BigOperators

open Sarkozy.ClassSlack
open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ThetaOne Sarkozy.SharpBase2
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.Companion (ResidualId CompId TotalsLe)
open Sarkozy.BlockRows (CompanionFrontRW CompanionObligationsRW main_goal_rebased_rw)

/-! ## The comparison series at the supremal totals, from any bounds -/

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : CancellationSteps.PaperJ0 → B}
  {C : Type} [Fintype C] [DecidableEq C]

/-- **The comparison series at the supremal totals from any letter bounds** (the finite numerical
route to HX2's `hC`, `hCv`): if `TotalsLe D ℓ X` and the series converges to `Cv` at `X`, it
converges at `letterSup D ℓ`, to a sum at most `Cv`. -/
theorem hC_of_le (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ D.CL.π L b t e) (c : (MLetter ⊕ C → ℕ) → ℝ) (hc0 : ∀ d, 0 ≤ c d)
    (X : MLetter ⊕ C → ℝ) (hX : TotalsLe D ℓ X) {Cv : ℝ}
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv) :
    HasSum (fun d => c d * ∏ l, letterSup D ℓ l ^ d l / (d l).factorial)
        (∑' d, c d * ∏ l, letterSup D ℓ l ^ d l / (d l).factorial) ∧
      (∑' d, c d * ∏ l, letterSup D ℓ l ^ d l / (d l).factorial) ≤ Cv :=
  series_mono c hc0 X (letterSup D ℓ) (letterSup_nonneg D ℓ hπ) (letterSup_le D ℓ X hX) hC

end Generic

section Sym

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables} {C : Type} [Fintype C] [DecidableEq C]

/-- **HX's symmetric-letter route, as a sufficient condition for HX2's `hC`, `hCv`** (not a
restriction of the lettering): if the lettering happens to have a letter `σ` carried by exactly the
symmetric entries, with `SForm F ≤ X σ` (F), and the other letters' totals are at most `X` (C),
then the series at `X` bounds the series at the supremal totals (HX's `totalsLe_of_sym`,
`symTotal_le_front`). -/
theorem hC_of_sym (F : CompanionND.CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ C)
    (hπ : ∀ L b t e, 0 ≤ (F.X hB hRR).data.CL.π L b t e) (c : (MLetter ⊕ C → ℕ) → ℝ)
    (hc0 : ∀ d, 0 ≤ c d) (X : MLetter ⊕ C → ℝ) (σ : MLetter ⊕ C)
    (hσ : ∀ L e, ℓ L e = σ ↔ e.2.2 = .sym) (hXσ : LetterTotals.SForm F ≤ X σ)
    (hXr : ∀ L l, l ≠ σ → letterTotal (ℓ L) ((F.X hB hRR).data.CL.π L) l ≤ X l) {Cv : ℝ}
    (hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv) :
    HasSum (fun d => c d * ∏ l, letterSup (F.X hB hRR).data ℓ l ^ d l / (d l).factorial)
        (∑' d, c d * ∏ l, letterSup (F.X hB hRR).data ℓ l ^ d l / (d l).factorial) ∧
      (∑' d, c d * ∏ l, letterSup (F.X hB hRR).data ℓ l ^ d l / (d l).factorial) ≤ Cv :=
  hC_of_le _ ℓ hπ c hc0 X (LetterTotals.totalsLe_of_sym _ ℓ X σ hσ (LetterTotals.SForm F)
    (LetterTotals.symTotal_le_front F hB hRR) hXσ hXr) hC

end Sym

/-! ## The obligations -/

/-- **The obligations of `main_goal_rebased_hx2`**: RW's `CompanionObligationsRW` without the letter
bounds `X` and the fields `hX0`, `hX`; the comparison series `hC` is stated at the supremal letter
totals `letterSup … ℓ`, where `hX` is a theorem (`totalsLe_front`). Every other field is a
verbatim copy of RW's. 32 fields. -/
structure CompanionObligationsHX2 (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (as RW's: `PCu` (C + F), `BI` (6 fields, all C + F), `rep` (C), `hs`, `ha`
  (F + R)). -/
  FB : CompanionFrontRW hW hMR hFour UpT
  /-- (D) As RW. -/
  cd : ClassData (FB.toBA.toND.X hB hRR).data.CL
  /-- (D) As RW. -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) As RW. -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) As RW. -/
  labS : ∀ L, Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → Option K
  /-- (D) As RW. -/
  labK : K → PaperDiag
  /-- (D) As RW. -/
  Zs : ∀ L, Finset ℤ → Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As RW. -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) As RW. -/
  ρ : ∀ L, Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As RW. -/
  r : ∀ L, Choice ((FB.toBA.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) As RW. -/
  Vv : ℝ
  /-- (D) As RW: the lettering of the record expansion. Its letter bounds are no longer data:
  they are the supremal letter totals `letterSup … ℓ`. -/
  ℓ : ∀ L, Entry ((FB.toBA.toND.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) As RW. -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) As RW: the sum of the completed comparison series. -/
  Cv : ℝ
  τ : ℝ
  /-- (S) As RW. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) As RW. -/
  hwHalf : WeightsHalf (FB.toBA.toND.X hB hRR).data cd labK wc
  /-- (S) As RW. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (FB.toBA.toND.X hB hRR).data cd labS Vv
  /-- (S) As RW. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) As RW. -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) As RW. -/
  hτ : τ ≤ 13 / 625
  /-- **(C)** RW's `hC` at the supremal letter totals: `C_v = ∑_d c(d) ∏_l X_l^{d_l}/d_l!` with
  `X_l = sup_L X_l(L)` (`eq:final-joint-closing` at the price bounds of
  `lem:four-routes-normalized`, taken to be the actual totals). It carries the content of RW's
  `hX` and `hC` together; a finite certificate is any `X` with RW's `hX` and RW's `hC` at `X`
  (`hC_of_le`). *Open*. -/
  hC : HasSum (fun d => c d * ∏ l,
    letterSup (FB.toBA.toND.X hB hRR).data ℓ l ^ d l / (d l).factorial) Cv
  /-- **(F)** As RW. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  /-- **(R)** As RW. *Open*. -/
  hup : SelUpper (FB.toBA.toND.X hB hRR).data cd labS (wtHalf K) Zs wc
  /-- **(C)** As RW. *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ
  /-- **(C)** As RW. *Open*. -/
  hρ : ResidualId (FB.toBA.toND.X hB hRR).data cd ρ r
  /-- **(C)** As RW. *Open*. -/
  hcomp : CompId (FB.toBA.toND.X hB hRR).data cd labS labK ℓ c r

attribute [instance] CompanionObligationsHX2.instFK CompanionObligationsHX2.instDK
  CompanionObligationsHX2.instFLt CompanionObligationsHX2.instDLt

namespace CompanionObligationsHX2

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **The letter bounds**: the supremal letter totals of the lettering. -/
noncomputable def X (O : CompanionObligationsHX2 hW hMR hFour hB hRR UpT) : MLetter ⊕ O.Lt → ℝ :=
  letterSup (O.FB.toBA.toND.X hB hRR).data O.ℓ

/-- **RW's `hX0`** (proved): the supremal totals of nonnegative prices are nonnegative. -/
theorem hX0 (O : CompanionObligationsHX2 hW hMR hFour hB hRR UpT) (l : MLetter ⊕ O.Lt) :
    0 ≤ O.X l :=
  letterSup_nonneg _ O.ℓ (fun L => O.cd.π_nonneg L) l

/-- **RW's `hX`** (proved): every letter total is at most its supremal total, which exists by
HX's type totals (`totalsLe_front`). -/
theorem hX (O : CompanionObligationsHX2 hW hMR hFour hB hRR UpT) :
    TotalsLe (O.FB.toBA.toND.X hB hRR).data O.ℓ O.X :=
  totalsLe_front O.FB.toBA.toND hB hRR O.ℓ fun L => O.cd.π_nonneg L

/-- **RW's obligations** (the bridge): `X := letterSup … ℓ`, with `hX0`, `hX` proved; every other
field copied. -/
noncomputable def toRW (O : CompanionObligationsHX2 hW hMR hFour hB hRR UpT) :
    CompanionObligationsRW hW hMR hFour hB hRR UpT where
  FB := O.FB
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  Zs := O.Zs
  wc := O.wc
  ρ := O.ρ
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hC := O.hC
  hCv := O.hCv
  hup := O.hup
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX

/-- **Every RW obligation set gives an HX2 one** (no further input): the series at the supremal
totals converges to at most RW's `Cv` (`hC_of_le` at RW's `X`, `hX`, `hC`), so `hCv` carries
over; every other field is copied. -/
noncomputable def ofRW (O : CompanionObligationsRW hW hMR hFour hB hRR UpT) :
    CompanionObligationsHX2 hW hMR hFour hB hRR UpT where
  FB := O.FB
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  Zs := O.Zs
  wc := O.wc
  ρ := O.ρ
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  Cv := ∑' d, O.c d * ∏ l,
    letterSup (O.FB.toBA.toND.X hB hRR).data O.ℓ l ^ d l / (d l).factorial
  τ := O.τ
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hc0 := O.hc0
  hτ := O.hτ
  hC := (hC_of_le _ O.ℓ (fun L => O.cd.π_nonneg L) O.c O.hc0 O.X O.hX O.hC).1
  hCv := (hC_of_le _ O.ℓ (fun L => O.cd.π_nonneg L) O.c O.hc0 O.X O.hX O.hC).2.trans O.hCv
  hup := O.hup
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp

/-- **`ofRW` lowers `Cv`**: the HX2 sum is at most RW's. -/
theorem ofRW_Cv_le (O : CompanionObligationsRW hW hMR hFour hB hRR UpT) : (ofRW O).Cv ≤ O.Cv :=
  (hC_of_le _ O.ℓ (fun L => O.cd.π_nonneg L) O.c O.hc0 O.X O.hX O.hC).2

/-- **The round trip `RW → HX2 → RW` lowers `X` to the supremal totals** (every other field is
copied). -/
theorem toRW_ofRW_X (O : CompanionObligationsRW hW hMR hFour hB hRR UpT) (l : MLetter ⊕ O.Lt) :
    (ofRW O).toRW.X l ≤ O.X l :=
  letterSup_le _ O.ℓ O.X O.hX l

/-- **The round trip `HX2 → RW → HX2` is the identity**: the recomputed sum is `Cv`
(`HasSum.tsum_eq`); every other field is copied. -/
theorem ofRW_toRW (O : CompanionObligationsHX2 hW hMR hFour hB hRR UpT) : ofRW O.toRW = O := by
  have h := O.hC.tsum_eq
  cases O
  simp only [ofRW, toRW]
  congr

/-- **RW's and HX2's obligations are satisfiable together**: HX2 neither strengthens nor weakens
RW. -/
theorem nonempty_iff : Nonempty (CompanionObligationsRW hW hMR hFour hB hRR UpT) ↔
    Nonempty (CompanionObligationsHX2 hW hMR hFour hB hRR UpT) :=
  ⟨fun ⟨O⟩ => ⟨ofRW O⟩, fun ⟨O⟩ => ⟨O.toRW⟩⟩

end CompanionObligationsHX2

/-- **The rebased companion statement with `hX` proved at the supremal letter totals**
(`thm:main` at `ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT`
(F) and `O : CompanionObligationsHX2`, whose letter bounds are the supremal letter totals of its
lettering, so that RW's `hX` and `hX0` are theorems: `main_goal_rebased_rw` at `O.toRW`. -/
theorem main_goal_rebased_hx2 (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsHX2 hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_rw hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toRW

end Sarkozy.LetterTotals2
