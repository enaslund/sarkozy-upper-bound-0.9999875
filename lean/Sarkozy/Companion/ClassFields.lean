module

public import Sarkozy.MeanCredit2.Classes

@[expose] public section

/-!
# The hypotheses of CM's class constructor, one definition per field (FC)

`MeanCredit2.classPartsPaper` takes its hypotheses as arguments. The companion statement lists
them as fields, in groups by kind. Each field type that involves the formal prices or the class
data is given a name here, in the same variable context as `classPartsPaper`, so that the field
and the argument are elaborated with the same instances (stated directly at the concrete data,
the instances on the block atoms are found by another path and the two types are not
recognisably equal). The bodies are verbatim copies of `classPartsPaper`'s argument types; Lean
checks this when `CompanionObligations.Cls` passes the fields to `classPartsPaper`.

* (S) **`WeightsPaper`** (`hwPaper`, stated on `wc`; `aggED … .w` is `∑_i wc`),
  **`PriceBound`** (`hvV`, stated on `agg π`; `aggED … .v` is `agg π`, `PriceBound.toAggED`);
* (C) **`ResidualId`** (`hρ`), **`CompId`** (`hcomp`), **`MeanId`** (`hmean`), **`TotalsLe`**
  (`hX`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.Companion

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.CancellationSteps (PaperJ0)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {K : Type} [Fintype K] [DecidableEq K] {C : Type} [Fintype C] [DecidableEq C]

/-- **(S) `hwPaper`**: the aggregated class weight `w_k = ∑_i w_{ik}` of a label is
`diagW(k)/wtOf(k)`, the paper's class weight net of the variance credit per unit of the exact
weight (`prop:joint-middle-mean`, the residual table, aggregated). It pins `wc`. -/
def WeightsPaper (D : CD blockOf) (cd : ClassData D.CL) (labK : K → PaperDiag) (μK : K → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) : Prop :=
  ∀ L k, ∑ i, wc L i k = diagW (labK k) / wtOf labK μK k

/-- **(S) `hvV`**: the aggregated label prices `agg π` are uniformly bounded by `Vv`. -/
def PriceBound (D : CD blockOf) (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (μK : K → ℝ) (Vv : ℝ) : Prop :=
  ∀ L k, agg (cd.sel L) (labS L) (wtOf labK μK) (monomial (D.CL.π L)) k ≤ Vv

/-- `PriceBound` is the bound `hvV` of `classPartsPaper` (`aggED … .v` is `agg π`). Stated in this
generic context, the identification is checked without evaluating the selections. -/
theorem PriceBound.toAggED {D : CD blockOf} {cd : ClassData D.CL}
    {labS : ∀ L, Choice (D.CL.T L) → Option K} {labK : K → PaperDiag} {μK : K → ℝ} {Vv : ℝ}
    (hμ0 : ∀ k, 0 ≤ μK k) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) (wc_nonneg : ∀ L i j, 0 ≤ wc L i j)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtOf labK μK) (Zs L A)) wc ρ)
    (hup : SelUpper D cd labS (wtOf labK μK) Zs wc) (h : PriceBound D cd labS labK μK Vv) :
    ∀ L k, (aggED labS (wtOf labK μK) (wtOf_nonneg labK hμ0) Zs wc wc_nonneg ρ ops
      hup).v L k ≤ Vv := h

/-- **(C) `hρ`**: the evaluated residual of a class selection is at most `r_ω` times its
monomial (`cor:envelope-costs`). -/
def ResidualId (D : CD blockOf) (cd : ClassData D.CL) (ρ r : ∀ L, Choice (D.CL.T L) → ℝ) :
    Prop :=
  ∀ L, ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ρ L ω ≤ r L ω * monomial (D.CL.π L) ω

/-- **(C) `hcomp`**: the comparison coefficient of a selection's letter degree dominates its
class bound: `B` off the classes, `r_ω` on them, plus `diagW` on its label (`thm:envelopes`(i),
`cor:envelope-costs`, the residual table). -/
def CompId (D : CD blockOf) (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (c : (MLetter ⊕ C → ℕ) → ℝ) (r : ∀ L, Choice (D.CL.T L) → ℝ) : Prop :=
  ∀ L, ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then D.B else r L ω) +
    (labS L ω).elim 0 (fun k => (diagW (labK k) : ℝ)) ≤ c (deg (ℓ L) ω)

/-- **(C) `hmean`**: a selection's letter degree carries at most its label's family credit
(`prop:joint-middle-mean`, families (i)–(iv), per selection). -/
def MeanId (D : CD blockOf) (cd : ClassData D.CL) (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (μK : K → ℝ) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C) : Prop :=
  ∀ L, ∀ ω ∈ cd.sel L, mLift (deg (ℓ L) ω) ≤ (labS L ω).elim 0 μK

/-- **(C) `hX`**: the formal letter totals are at most `X` (the price bounds of
`lem:four-routes-normalized`). -/
def TotalsLe (D : CD blockOf) (ℓ : ∀ L, Entry (D.CL.T L) → MLetter ⊕ C)
    (X : MLetter ⊕ C → ℝ) : Prop :=
  ∀ L l, letterTotal (ℓ L) (D.CL.π L) l ≤ X l

end Sarkozy.Companion
