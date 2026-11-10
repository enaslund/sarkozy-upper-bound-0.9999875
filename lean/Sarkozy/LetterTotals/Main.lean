module

public import Sarkozy.LetterTotals.Front
public import Sarkozy.BlockInputs.MainEC

@[expose] public section

/-!
# The companion statement with the symmetric letter total proved (`main_goal_rebased_hx`)

HX, 8 November 2026. The field `hX : TotalsLe (FB.toND.X hB hRR).data ℓ X` of BA's
`CompanionObligationsBAEC` (EC's obligations with the front's `BA` split; `hX` is EC's verbatim)
asks every letter total of the lettering `ℓ` to be at most `X`, uniformly in the scale. Its
symmetric side is now a theorem: `symTotal_le_front` bounds `∑_𝔟 s_𝔟` by the explicit `SForm F`
(`F = FB.toND`) at every scale (`Front.lean`;
`lem:middle-comparison-prices`, `prop:record:upper`(ii), `lem:record:block-charge`,
`lem:frontier:iidenergy`(iii), `lem:tail-prices`(iv), all through the proved `hSA` chain, split by
change type). So, for a lettering with **one symmetric letter `σ`** (carried by exactly the
symmetric entries), `hX` reduces to

* (D) `σ`, (S) `hσ : ∀ L e, ℓ L e = σ ↔ e is symmetric`;
* (F) `hXσ : SForm FB.toND ≤ X σ`, a finite numerical claim on explicit data (the front's upper
  record tables, `paperKappa`, `bandBound a_T`, `f1c2`, `f1c3`, TC's tail numbers);
* (C) `hXr`: the letter totals of the other letters, which are all skew (`hσ`), are at most `X`.
  Together they are at most `AForm F` (`skewLetters_le`, proved).

* `totalsLe_of_sym` (generic, in `TotalsLe`'s own context);
* **`CompanionObligationsHX`**: BA-EC's `CompanionObligationsBAEC` with `hX` replaced by `σ`,
  `hσ`, `hXσ`, `hXr` (38 fields);
* `toBAEC` (the bridge), `toEC`; **`ofBAEC`** (non-vacuity: a BA-EC obligation set whose
  lettering has one symmetric letter with `X σ ≥ SForm` gives an HX one; `toBAEC_ofBAEC` is
  `rfl`), `ofEC` (through BA's `ofEC`), `skewLetters_le`;
* **`main_goal_rebased_hx`**: `Target.SarkozyBound TargetGoal.epsGoal`, through BA's
  `main_goal_rebased_baec`.
-/

namespace Sarkozy.LetterTotals

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.SharpSums
open Sarkozy.Param (Params)
open Sarkozy.ClassSlack
open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ThetaOne Sarkozy.SharpBase2
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.Companion (ResidualId CompId TotalsLe)
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.E1Closure (CompanionObligationsEC)
open Sarkozy.BlockInputs (CompanionFrontBA CompanionObligationsBAEC main_goal_rebased_baec)

/-! ## `TotalsLe` from a symmetric letter -/

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {C : Type} [Fintype C] [DecidableEq C]

omit [Fintype C] in
/-- **`TotalsLe` from one symmetric letter** (in `TotalsLe`'s own context): if the letter `σ` is
carried by exactly the symmetric entries, the symmetric total is at most `Sb ≤ X σ` at every scale,
and every other letter total is at most `X`, then `TotalsLe D ℓ X`. -/
theorem totalsLe_of_sym (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (X : MLetter ⊕ C → ℝ) (σ : MLetter ⊕ C) (hσ : ∀ L e, ℓ L e = σ ↔ e.2.2 = .sym) (Sb : ℝ)
    (hS : ∀ L, ∑ b, symTotal (D.CL.π L) b ≤ Sb) (hXσ : Sb ≤ X σ)
    (hXr : ∀ L l, l ≠ σ → letterTotal (ℓ L) (D.CL.π L) l ≤ X l) : TotalsLe D ℓ X := by
  intro L l
  by_cases hl : l = σ
  · subst hl
    rw [letterTotal_eq_symTotal (ℓ L) (D.CL.π L) l (hσ L)]
    exact (hS L).trans hXσ
  · exact hXr L l hl

/-- **The letters other than `σ` are skew, and together at most the skew total.** -/
theorem skew_letters_le (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (σ : MLetter ⊕ C) (hσ : ∀ L e, ℓ L e = σ ↔ e.2.2 = .sym)
    (hπ : ∀ L b t e, 0 ≤ D.CL.π L b t e) (L : ℕ) :
    ∑ l ∈ univ.erase σ, letterTotal (ℓ L) (D.CL.π L) l ≤ ∑ b, skewTotal (D.CL.π L) b := by
  refine sum_letterTotal_le_skewTotal (ℓ L) (hπ L) _ fun e he => ?_
  have hne : ℓ L e ≠ σ := (mem_erase.mp he).1
  rcases h : e.2.2 with _ | _
  · exact absurd ((hσ L e).mpr h) hne
  · rfl

end Generic

/-! ## The obligations -/

/-- **The obligations of `main_goal_rebased_hx`**: BA-EC's `CompanionObligationsBAEC` with the
field `hX` replaced by a symmetric letter `σ` (D), its definition `hσ` (S), the numerical claim
`hXσ` (F) and the skew letters' bound `hXr` (C). Every other field is a verbatim copy of BA-EC's.
38 fields. -/
structure CompanionObligationsHX (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (as BA-EC's: `PCu`, `BI`, `rep`, `hs`, `ha`; its ND front is `FB.toND`). -/
  FB : CompanionFrontBA hW hMR hFour UpT
  /-- (D) The classes `ι`, `cls` of `def:cp5` (as EC's). -/
  cd : ClassData (FB.toND.X hB hRR).data.CL
  /-- (D) The labels of the aggregated diagonals (as EC's). -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) The letters other than `MLetter` (as EC's). -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) The label of each selection (as EC's). -/
  labS : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → Option K
  /-- (D) The paper type of each label (as EC's). -/
  labK : K → PaperDiag
  /-- (D) The per-selection diagonal energies (as EC's). -/
  Zs : ∀ L, Finset ℤ → Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The class weights on the labels (as EC's). -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) The evaluated residuals of the selections (as EC's). -/
  ρ : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The per-selection residual coefficients (as EC's). -/
  r : ∀ L, Choice ((FB.toND.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The uniform bound of the label prices (as EC's). -/
  Vv : ℝ
  /-- (D) The lettering of the record expansion (as EC's). -/
  ℓ : ∀ L, Entry ((FB.toND.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) The comparison coefficient of a letter degree (as EC's). -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) The letter totals (as EC's). -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) The completed comparison series and its slack (as EC's). -/
  Cv : ℝ
  τ : ℝ
  /-- (D) **New**: the symmetric letter. -/
  σ : MLetter ⊕ Lt
  /-- (S) As EC's. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) As EC's (`hwHalf`). -/
  hwHalf : WeightsHalf (FB.toND.X hB hRR).data cd labK wc
  /-- (S) As EC's. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (FB.toND.X hB hRR).data cd labS Vv
  /-- (S) As EC's. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) As EC's. -/
  hX0 : ∀ l, 0 ≤ X l
  /-- (S) As EC's. -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) As EC's: `τ ≤ 13/625`. -/
  hτ : τ ≤ 13 / 625
  /-- (S) **New**: the letter `σ` is carried by exactly the symmetric entries (one symmetric
  letter; every other letter is skew). -/
  hσ : ∀ L e, ℓ L e = σ ↔ e.2.2 = .sym
  /-- **(F)** As EC's: `C_v = ∑_d c(d) ∏_l X_l^{d_l}/d_l!`. -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** As EC's: `C_v ≤ 𝓔_h + τ`. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  /-- **(F)** **New**: the symmetric letter total is at least the proved symmetric bound,
  `SForm FB.toND ≤ X σ` (`def:closing-quantities`, `lem:four-routes-normalized`: the symmetric
  assignment). A finite claim on explicit data. *Open* (not evaluated). -/
  hXσ : SForm FB.toND ≤ X σ
  /-- **(R)** As EC's (`SelUpper`). *Open*. -/
  hup : SelUpper (FB.toND.X hB hRR).data cd labS (wtHalf K) Zs wc
  /-- **(C)** As EC's (`ops`). *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ
  /-- **(C)** As EC's (`hρ`). *Open*. -/
  hρ : ResidualId (FB.toND.X hB hRR).data cd ρ r
  /-- **(C)** As EC's (`hcomp`). *Open*. -/
  hcomp : CompId (FB.toND.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** **`hXr`**, EC's `hX` on the letters other than `σ`, which are skew (`hσ`): the
  skew letter totals of the refined lettering are at most `X` (the skew price bounds of
  `lem:middle-comparison-prices`, `lem:four-routes-normalized`, per letter). Together these
  totals are at most `AForm F` (`skewLetters_le`, proved). *Open*. -/
  hXr : ∀ L l, l ≠ σ → letterTotal (ℓ L) ((FB.toND.X hB hRR).data.CL.π L) l ≤ X l

attribute [instance] CompanionObligationsHX.instFK CompanionObligationsHX.instDK
  CompanionObligationsHX.instFLt CompanionObligationsHX.instDLt

namespace CompanionObligationsHX

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **EC's `hX`**, from `hσ`, `hXσ`, `hXr` and the proved symmetric bound `symTotal_le_front`. -/
theorem hX (O : CompanionObligationsHX hW hMR hFour hB hRR UpT) :
    TotalsLe (O.FB.toND.X hB hRR).data O.ℓ O.X :=
  totalsLe_of_sym _ O.ℓ O.X O.σ O.hσ (SForm O.FB.toND) (symTotal_le_front O.FB.toND hB hRR) O.hXσ
    O.hXr

/-- **The skew letters together**: at every scale, the letter totals of the letters other than
`σ` add up to at most `AForm F` (proved; `skewTotal_le_front`). -/
theorem skewLetters_le (O : CompanionObligationsHX hW hMR hFour hB hRR UpT) (L : ℕ) :
    ∑ l ∈ univ.erase O.σ, letterTotal (O.ℓ L) ((O.FB.toND.X hB hRR).data.CL.π L) l ≤
      AForm O.FB.toND :=
  (skew_letters_le _ O.ℓ O.σ O.hσ (fun L => O.cd.π_nonneg L) L).trans
    (skewTotal_le_front O.FB.toND hB hRR L)

/-- **The BA-EC obligations** (the bridge): every field copied, `hX` from `O.hX`. -/
def toBAEC (O : CompanionObligationsHX hW hMR hFour hB hRR UpT) :
    CompanionObligationsBAEC hW hMR hFour hB hRR UpT where
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

/-- **EC's obligations**, through BA-EC's bridge. -/
noncomputable def toEC (O : CompanionObligationsHX hW hMR hFour hB hRR UpT) :
    CompanionObligationsEC hW hMR hFour hB hRR UpT :=
  O.toBAEC.toEC

/-- **Non-vacuity**: a BA-EC obligation set whose lettering has one symmetric letter `σ`, with
`X σ ≥ SForm`, gives an HX one (`hXr` is BA-EC's `hX` on the other letters). -/
def ofBAEC (O : CompanionObligationsBAEC hW hMR hFour hB hRR UpT) (σ : MLetter ⊕ O.Lt)
    (hσ : ∀ L e, O.ℓ L e = σ ↔ e.2.2 = .sym) (hXσ : SForm O.FB.toND ≤ O.X σ) :
    CompanionObligationsHX hW hMR hFour hB hRR UpT where
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
  σ := σ
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hσ := hσ
  hC := O.hC
  hCv := O.hCv
  hXσ := hXσ
  hup := O.hup
  ops := O.ops
  hρ := O.hρ
  hcomp := O.hcomp
  hXr := fun L l _ => O.hX L l

/-- The round trip `toBAEC ∘ ofBAEC` is the identity (definitionally). -/
theorem toBAEC_ofBAEC (O : CompanionObligationsBAEC hW hMR hFour hB hRR UpT)
    (σ : MLetter ⊕ O.Lt) (hσ : ∀ L e, O.ℓ L e = σ ↔ e.2.2 = .sym)
    (hXσ : SForm O.FB.toND ≤ O.X σ) : (ofBAEC O σ hσ hXσ).toBAEC = O := rfl

/-- **Non-vacuity from EC**: an EC obligation set with one symmetric letter (`X σ ≥ SForm`) and
BA's certificate families gives an HX one (BA's `ofEC`, then `ofBAEC`). -/
noncomputable def ofEC (O : CompanionObligationsEC hW hMR hFour hB hRR UpT)
    (C : Sarkozy.BlockInputs.BlockCertsBA) (σ : MLetter ⊕ O.Lt)
    (hσ : ∀ L e, O.ℓ L e = σ ↔ e.2.2 = .sym)
    (hXσ : SForm (CompanionObligationsBAEC.ofEC O C).FB.toND ≤ O.X σ) :
    CompanionObligationsHX hW hMR hFour hB hRR UpT :=
  ofBAEC (CompanionObligationsBAEC.ofEC O C) σ hσ hXσ

/-- The round trip from EC is the identity (definitionally). -/
theorem toEC_ofEC (O : CompanionObligationsEC hW hMR hFour hB hRR UpT)
    (C : Sarkozy.BlockInputs.BlockCertsBA) (σ : MLetter ⊕ O.Lt)
    (hσ : ∀ L e, O.ℓ L e = σ ↔ e.2.2 = .sym)
    (hXσ : SForm (CompanionObligationsBAEC.ofEC O C).FB.toND ≤ O.X σ) :
    (ofEC O C σ hσ hXσ).toEC = O := rfl

end CompanionObligationsHX

/-- **The rebased companion statement with the symmetric letter total proved** (`thm:main` at
`ε = 10⁻⁵`): `s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT` (F) and the
obligations `O : CompanionObligationsHX`, in which BA-EC's `hX` is replaced by the symmetric
letter (`hσ`, `hXσ`) and the skew letters (`hXr`): `main_goal_rebased_baec` at `O.toBAEC`. -/
theorem main_goal_rebased_hx (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsHX hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_baec hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT
    O.toBAEC

end Sarkozy.LetterTotals
