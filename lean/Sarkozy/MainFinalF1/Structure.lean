module

public import Sarkozy.MainFinal.All
public import Sarkozy.AnalyticCells.F1Cell

@[expose] public section





open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap PrefixCoord)
open Sarkozy.EnvelopesPaper (PrefixRefinement)
open Sarkozy.ComparisonLawPaper (DeletionInputs TailAtomInputs tailNe paperPrefixAccepted
  P4_le_paperTail ComparisonInputs SAExplicit)
open Sarkozy.MiddleComparison (SpecData comparisonInputsOfData)
open Sarkozy.MainFinal (PrimeCertificates BlockAnalytic hCF hrepl_of_others)

/-- **B1's analytic inputs `A` at the paper's partition** from the per-prime certificates and the
block-level inputs, through B6's block adapter (`paperAnalyticInputs_B6`): `PaperBudget f1Cell`
is N1's `paperCell_budget`, the E21 certificates are `middleE21Caps_proved`, the upper `E × E`
layer caps are `upperLayerCaps_EE`, the coordinate-`1` upper fields follow by the coordinate
exchange. -/
theorem analyticInputs (PC : PrimeCertificates) (BA : BlockAnalytic) :
    PaperAnalyticInputs AnalyticCells.f1Cell :=
  BlockAdapter.paperAnalyticInputs_B6 AnalyticCells.f1Cell_budget
    (fun k => BlockAdapter.upperBandLemma_of_rest
      (BlockAdapter.upperBandRest_of_rows (BlockAdapter.upperBandRows_of_nonEE (BA.hUR k))
        (PC.hUC k)) (PC.hUC k))
    BA.hMB BA.hIB PC.h20 PC.h10 PC.h21 BlockAdapter.middleE21Caps_proved

/-! ## The constructed block specification -/

/-- The block type of the paper's partition. -/
abbrev Blk : Type := PaperBlock AnalyticCells.f1Cell

/-- The block map of the paper's partition (`def:construction`(b)). -/
noncomputable abbrev bOf : PaperJ0 → Blk := paperBlockOf AnalyticCells.f1Cell

/-- The block specification (B1's `paperSpec`). -/
noncomputable abbrev specF (hW : Target.Weil) (A : PaperAnalyticInputs AnalyticCells.f1Cell) :
    ∀ b, PaperBlockSpec bOf b :=
  paperSpec hW A

/-! ## (CP4): the comparison inputs (B2, B7) -/

/-- **The open inputs of (CP4)** (`def:cp4`), in B7's form: B2's clique and tail inputs, and per
class-three block `SpecData` (B2's `UpperAtomInputs` on an upper block; B7's `ReplacementData` on
a middle block). 7 fields, of which `St`, `At` are numbers. -/
structure ComparisonParts (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs AnalyticCells.f1Cell) where
  /-- Square-clique atoms: the deletion `ν_p = μ_p − ω κ̄` (`lem:frontier:iidenergy`(ii),
  `lem:frontier:iidlocal`(iv),(v)). *Open* (analytic). -/
  clique : ∀ q : PrefixCoord, DeletionInputs
    ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
    (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries
  /-- Class-three blocks: on an upper block B2's `UpperAtomInputs` (the replacing laws of the 92
  changed records, `prop:record:upper`(i)); on a middle block B7's `ReplacementData` (the signed
  fold components `lem:signed-components`, `def:record:mixture`(b)–(e), and the twelve norms
  `prop:signed-bounds`(a),(b),(e), `lem:record:exact-marginal-e`(ii), `lem:merge-repair`,
  `lem:record:accepting-c2`). *Open* (analytic; B8 works on `ReplacementData`). -/
  blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b)
  /-- Tail primes `q ≥ P₄`: V3's `AcceptedTailData` and the (b) records (`lem:tail-prices`(i),
  (ii)). *Open* (analytic). -/
  tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
    TailAtomInputs q (tailNe hW h4)
      (signedIntegral ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μp q).weight)
  /-- The tail bound `S_tail` (`lem:tail-prices`(iv)). Data. -/
  St : ℝ
  /-- The tail bound `A_tail` (`lem:tail-prices`(iv)). Data. -/
  At : ℝ
  /-- `∑_{P₄ ≤ p ≤ N^{1/20}} s_p ≤ S_tail` at every scale (`lem:tail-prices`(iv)). *Open*. -/
  tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
    (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St
  /-- `∑_{P₄ ≤ p ≤ N^{1/20}} a_p ≤ A_tail` at every scale (`lem:tail-prices`(iv)). *Open*. -/
  tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
    (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At

namespace ComparisonParts

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs AnalyticCells.f1Cell}

/-- B2's `ComparisonInputs`, through B7's `comparisonInputsOfData`. -/
noncomputable abbrev Ci (C : ComparisonParts hW hMR hFour A) :
    ComparisonInputs bOf hW (specF hW A) (hCF hW hMR hFour) (paperIn AnalyticCells.f1Cell) :=
  comparisonInputsOfData bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn AnalyticCells.f1Cell) C.clique C.blk C.tail C.St C.At C.tail_S C.tail_A

/-- **(CP4) of the paper's construction** (`def:cp4`): B2's `comparisonLawTarget` at `C.Ci`. -/
noncomputable abbrev CL (C : ComparisonParts hW hMR hFour A) :
    TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap bOf) paperTail
      (paperSelAt (paperAtomMap bOf) targetDecay) paperPP paperEP paperQueries
      (firstStageTarget bOf hW (specF hW A) (hCF hW hMR hFour)
        (paperIn AnalyticCells.f1Cell)) :=
  ComparisonLawPaper.comparisonLawTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn AnalyticCells.f1Cell) C.Ci

end ComparisonParts

/-! ## (CP6), (CP8)(c): the prefix refinement (B3) -/

/-- **The open inputs of (CP6) and (CP8)(c)** in B3's prefix form (`JointPrefixBlockData` without
the fixed `spec`, `hC`, `In`, `Gi`, `CL`). 6 fields, of which `TK`, `σCL` are numbers. -/
structure EnvelopeParts (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs AnalyticCells.f1Cell) (C : ComparisonParts hW hMR hFour A) where
  /-- The prefix refinement (`prop:record:matching`(i) on the middle blocks; nothing replaced or
  added at a tail atom). *Open*: the prefix bracket `bracket_pre` (B8) and the per-block bounds
  `KL`, `KR`. -/
  PR : PrefixRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn AnalyticCells.f1Cell) (paperGi hW A)) C.CL
  /-- The price `T_K` of the added diagonals (`prop:signed-sides`(iii)). Data. -/
  TK : ℝ
  /-- The per-block sums `∑_β KL β ≤ T_K`, `∑_β KR β ≤ T_K` (`prop:signed-sides`(iii),
  `prop:record:matching`(ii)). *Open* (finite sums). -/
  hK : ∑ β, PR.KL β ≤ TK ∧ ∑ β, PR.KR β ≤ TK
  /-- The replaced (fold and matching) records of `CL` carry at least
  `∑_𝔟(s_𝔟 + a_𝔟) − (T^{ledger} − T_K)` of its (CP4) price, at every scale
  (`prop:record:matching`(ii)). *Open* (a property of `CL`). -/
  hrepl : ∀ L, ∑ b, (symTotal (C.CL.π L) b + skewTotal (C.CL.π L) b) - (targetLedger.T - TK) ≤
    ∑ b, ∑ t ∈ PR.repl L b, (C.CL.π L b t .sym + C.CL.π L b t .skew)
  /-- The weighted (CP4) bound. Data. -/
  σCL : ℝ
  /-- The weighted (CP4) summability of `CL` (`def:cp8`(c)). *Open* (a property of `CL`). -/
  hCL : ∀ L, ∑ b, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L b ^
    ((1 : ℝ) / 4) * (symTotal (C.CL.π L) b + skewTotal (C.CL.π L) b) ≤ σCL

/-! ## The data -/

/-- **The block data of the combined statement**: the analytic inputs (B6), the (CP4) inputs
(B2, B7) and the (CP6)/(CP8)(c) inputs (B3). Everything else of the block data (`bOf`,
`spec`, `hC`, `In`, `Gi`, `CL`, `ME`, `SM`) is constructed. 4 fields. -/
structure FinalBlockData (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (B6). -/
  PC : PrimeCertificates
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (B2, B7). -/
  Cmp : ComparisonParts hW hMR hFour (analyticInputs PC BA)
  /-- The (CP6), (CP8)(c) inputs (B3). -/
  Env : EnvelopeParts hW hMR hFour (analyticInputs PC BA) Cmp

namespace FinalBlockData

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- The analytic inputs `A` of the data. -/
theorem AI (D : FinalBlockData hW hMR hFour) : PaperAnalyticInputs AnalyticCells.f1Cell :=
  analyticInputs D.PC D.BA

/-- B3's prefix data of `D`. -/
noncomputable def toPrefix (D : FinalBlockData hW hMR hFour) :
    JointPrefixBlockData bOf hW where
  spec := specF hW D.AI
  hC := hCF hW hMR hFour
  In := paperIn AnalyticCells.f1Cell
  Gi := paperGi hW D.AI
  CL := D.Cmp.CL
  PR := D.Env.PR
  TK := D.Env.TK
  hK := D.Env.hK
  hrepl := D.Env.hrepl
  σCL := D.Env.σCL
  hCL := D.Env.hCL

/-- **B1's joint block data of `D`**: `CL` (B2, B7), and `ME`, `SM` through B3's prefix refinement
(`EnvelopeRefinement.toME`, `summabilityOf`). -/
noncomputable def toFixed (D : FinalBlockData hW hMR hFour) :
    B1JointBlockData AnalyticCells.f1Cell hW hMR hFour D.AI where
  CL := D.Cmp.CL
  ME := D.toPrefix.toB3.toJoint.ME
  SM := D.toPrefix.toB3.toJoint.SM

/-- B3's joint block data of `D`. -/
noncomputable abbrev toJoint (D : FinalBlockData hW hMR hFour) : JointBlockDataTarget bOf hW :=
  D.toFixed.toJoint

/-- The comparison data of `D` (`TheoremCBlock.ComparisonData` at `a_T`). -/
noncomputable abbrev data (D : FinalBlockData hW hMR hFour) :
    TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap bOf) paperTail paperPr
      paperH Chamber :=
  D.toJoint.data

end FinalBlockData

/-! ## `hrepl` from the other records (K1's `Matching.lean`) -/

section Matching

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs AnalyticCells.f1Cell} {C : ComparisonParts hW hMR hFour A}

/-- **B3's (CP6)/(CP8)(c) inputs with `hrepl` from the other records**
(`prop:record:matching`(ii)): `hrepl` is proved from `hoth` (the records not replaced cost at
most `T_oth` at every scale; *open*, a property of `CL`) and the scalar gate
`T_K + T_oth ≤ T^{ledger}` (*open*, numerical). -/
noncomputable def EnvelopeParts.ofOthers
    (PR : PrefixRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn AnalyticCells.f1Cell) (paperGi hW A)) C.CL)
    (TK : ℝ) (hK : ∑ β, PR.KL β ≤ TK ∧ ∑ β, PR.KR β ≤ TK) (Toth : ℝ)
    (hoth : ∀ L, ∑ b, ∑ t ∈ univ \ PR.repl L b, (C.CL.π L b t .sym + C.CL.π L b t .skew) ≤ Toth)
    (hTK : TK + Toth ≤ targetLedger.T) (σCL : ℝ)
    (hCL : ∀ L, ∑ b, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L b ^
      ((1 : ℝ) / 4) * (symTotal (C.CL.π L) b + skewTotal (C.CL.π L) b) ≤ σCL) :
    EnvelopeParts hW hMR hFour A C where
  PR := PR
  TK := TK
  hK := hK
  hrepl := fun L => hrepl_of_others (C.CL.π L) (PR.repl L) (hoth L) hTK
  σCL := σCL
  hCL := hCL

end Matching

end Sarkozy.MainFinalF1
