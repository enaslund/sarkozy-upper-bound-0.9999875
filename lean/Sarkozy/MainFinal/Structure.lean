module

public import Sarkozy.BlockAdapter.Final
public import Sarkozy.PaperNumbers.Costs
public import Sarkozy.MiddleComparison.PaperData
public import Sarkozy.ComparisonLawPaper.Main
public import Sarkozy.ComparisonLawPaper.Prices
public import Sarkozy.JointClosing.MainPrefix
public import Sarkozy.ClassBoundsPaper.Main
public import Sarkozy.EnvelopeEnergiesPaper.Main

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal

open Sarkozy.TheoremC Sarkozy.RecordExpansion
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap PrefixCoord)
open Sarkozy.EnvelopesPaper (PrefixRefinement)
open Sarkozy.ComparisonLawPaper (DeletionInputs TailAtomInputs tailNe paperPrefixAccepted
  P4_le_paperTail ComparisonInputs SAExplicit)
open Sarkozy.MiddleComparison (SpecData comparisonInputsOfData)
open Sarkozy.ClassBoundsPaper (ClassInputs PolynomialData ClassEnergyInputs MeanAllocation)
open Sarkozy.EnvelopeEnergiesPaper (CoupledFibreMoment FixedIntervalInputsCRT
  EnvelopeEnergyInputsCRT paper_pairwise)

/-! ## The analytic block inputs (B6) -/

/-- **The per-prime cut certificates** (B6's per-prime families; C8 works on `h20`, `h10`, `h21`).
*Hypotheses* (analytic, one spectral statement per prime of a piece or band). 4 fields. -/
structure PrimeCertificates : Prop where
  /-- Upper bands (310): for each field type, ordinary and reserved, constants `(g, B, X)` with
  `g e^{B L_k/(X log X)} ≤ d` and the chamber-cut certificate `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` at
  every prime of the band (`cert:upper-root-caps`). *Open*. -/
  hUC : ∀ k, BlockAdapter.UpperRootCaps k
  /-- Middle, 31 uniform pieces: the L20 cut `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` at the recorded ALLp
  constants `(allpG i 0, allpB i 0)` (`lem:front12:reference`(ii), `cert:l20-grid`). *Open*. -/
  h20 : ∀ i, allpIndividual i = none → BlockAdapter.MiddleRootCaps (Fin 2) 0 i
  /-- Middle, 33 pieces: the same for the L10 cut (`lem:layer12-caps`(b)). *Open*. -/
  h10 : ∀ i, BlockAdapter.MiddleRootCaps (Fin 1) 1 i
  /-- Middle, 31 uniform pieces: the same for the L21 layer cut (`lem:layer12-caps`(b)). *Open*. -/
  h21 : ∀ i, allpIndividual i = none → BlockAdapter.MiddleL21Caps i

/-- **The block-level analytic inputs** (B6's remaining block statements). *Hypotheses*
(spectral, one statement per piece or band, quantified over the blocks of that site). 3 fields. -/
structure BlockAnalytic : Prop where
  /-- Upper bands (310): the coordinate-`0` rows `rows20`, `rows10` (V2) and the layer caps (V3)
  of the 16 type pairs other than `E × E` (`lem:upper-reference-rp`(ii)). *Open*. -/
  hUR : ∀ k, BlockAdapter.UpperBandRowsNonEE k
  /-- Middle, 31 uniform pieces: the rows `j = 2, 1` (`lem:front12:reference`(i)) and the F21
  layer caps at the recorded `k_D` (`lem:old-f-law`(e)). *Open*. -/
  hMB : ∀ i, allpIndividual i = none → BlockAdapter.MiddleUniformBlockInputs i
  /-- Middle, pieces `2³⁶`, `2⁴⁰`: the rows, the L20 envelope and L21 cap of the individual-square
  root (`def:positive-root`, `cert:positive-root-caps`) and the F21 caps. *Open*. -/
  hIB : ∀ i u, allpIndividual i = some u → BlockAdapter.MiddleIndividualBlockInputs i u

/-- **B1's analytic inputs `A` at the paper's partition** from the per-prime certificates and the
block-level inputs, through B6's block adapter (`paperAnalyticInputs_B6`): `PaperBudget paperCell`
is N1's `paperCell_budget`, the E21 certificates are `middleE21Caps_proved`, the upper `E × E`
layer caps are `upperLayerCaps_EE`, the coordinate-`1` upper fields follow by the coordinate
exchange. -/
theorem analyticInputs (PC : PrimeCertificates) (BA : BlockAnalytic) :
    PaperAnalyticInputs PaperNumbers.paperCell :=
  BlockAdapter.paperAnalyticInputs_B6 PaperNumbers.paperCell_budget
    (fun k => BlockAdapter.upperBandLemma_of_rest
      (BlockAdapter.upperBandRest_of_rows (BlockAdapter.upperBandRows_of_nonEE (BA.hUR k))
        (PC.hUC k)) (PC.hUC k))
    BA.hMB BA.hIB PC.h20 PC.h10 PC.h21 BlockAdapter.middleE21Caps_proved

/-! ## The numerical certificates (N1) -/

/-- **The 66 per-piece charge bounds** `pieceBound a_T d i ≤ c_d(i)`, `d = 2, 3`, `i < 33`, at
N1's recorded numbers `c_d(i) = 1.0004 · t · I_d(i)` (`chargeC2`, `chargeC3`). *Hypotheses*,
numerical: M2's explicit bound of the paper's blocks (the price buckets of the greedy blocks below
`X_Ch`, the cell integrals above it) against the certified degree charges
(`cert:record:middle-price`) repriced to `a_T` (`lem:record:repricing`). 2 fields. -/
structure NumericalCertificates : Prop where
  /-- The 33 bounds of degree 2. *Open* (numerical). -/
  h₂ : ∀ i, PaperNumbers.pieceBound targetDecay 2 i ≤ PaperNumbers.chargeC2 i
  /-- The 33 bounds of degree 3. *Open* (numerical). -/
  h₃ : ∀ i, PaperNumbers.pieceBound targetDecay 3 i ≤ PaperNumbers.chargeC3 i

/-! ## The constructed block specification -/

/-- The block type of the paper's partition. -/
abbrev Blk : Type := PaperBlock PaperNumbers.paperCell

/-- The block map of the paper's partition (`def:construction`(b)). -/
noncomputable abbrev bOf : PaperJ0 → Blk := paperBlockOf PaperNumbers.paperCell

/-- The block specification (B1's `paperSpec`). -/
noncomputable abbrev specF (hW : Target.Weil) (A : PaperAnalyticInputs PaperNumbers.paperCell) :
    ∀ b, PaperBlockSpec bOf b :=
  paperSpec hW A

noncomputable abbrev hCF (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle) :
    TailInputsCorr PartV.P4 :=
  TailCorrCore.tailInputsCorr hW hMR hFour

/-! ## (CP4): the comparison inputs (B2, B7) -/

/-- **The open inputs of (CP4)** (`def:cp4`), in B7's form: B2's clique and tail inputs, and per
class-three block `SpecData` (B2's `UpperAtomInputs` on an upper block; B7's `ReplacementData` on
a middle block). 7 fields, of which `St`, `At` are numbers. -/
structure ComparisonParts (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs PaperNumbers.paperCell) where
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
  blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b)
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
  {A : PaperAnalyticInputs PaperNumbers.paperCell}

/-- B2's `ComparisonInputs`, through B7's `comparisonInputsOfData`. -/
noncomputable abbrev Ci (C : ComparisonParts hW hMR hFour A) :
    ComparisonInputs bOf hW (specF hW A) (hCF hW hMR hFour) (paperIn PaperNumbers.paperCell) :=
  comparisonInputsOfData bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn PaperNumbers.paperCell) C.clique C.blk C.tail C.St C.At C.tail_S C.tail_A

/-- **(CP4) of the paper's construction** (`def:cp4`): B2's `comparisonLawTarget` at `C.Ci`. -/
noncomputable abbrev CL (C : ComparisonParts hW hMR hFour A) :
    TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap bOf) paperTail
      (paperSelAt (paperAtomMap bOf) targetDecay) paperPP paperEP paperQueries
      (firstStageTarget bOf hW (specF hW A) (hCF hW hMR hFour)
        (paperIn PaperNumbers.paperCell)) :=
  ComparisonLawPaper.comparisonLawTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn PaperNumbers.paperCell) C.Ci

end ComparisonParts

/-! ## (CP6), (CP8)(c): the prefix refinement (B3) -/

/-- **The open inputs of (CP6) and (CP8)(c)** in B3's prefix form (`JointPrefixBlockData` without
the fixed `spec`, `hC`, `In`, `Gi`, `CL`). 6 fields, of which `TK`, `σCL` are numbers. -/
structure EnvelopeParts (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs PaperNumbers.paperCell) (C : ComparisonParts hW hMR hFour A) where
  /-- The prefix refinement (`prop:record:matching`(i) on the middle blocks; nothing replaced or
  added at a tail atom). *Open*: the prefix bracket `bracket_pre` (B8) and the per-block bounds
  `KL`, `KR`. -/
  PR : PrefixRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn PaperNumbers.paperCell) (paperGi hW A)) C.CL
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
theorem AI (D : FinalBlockData hW hMR hFour) : PaperAnalyticInputs PaperNumbers.paperCell :=
  analyticInputs D.PC D.BA

/-- B3's prefix data of `D`. -/
noncomputable def toPrefix (D : FinalBlockData hW hMR hFour) :
    JointPrefixBlockData bOf hW where
  spec := specF hW D.AI
  hC := hCF hW hMR hFour
  In := paperIn PaperNumbers.paperCell
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
    B1JointBlockData PaperNumbers.paperCell hW hMR hFour D.AI where
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

/-! ## The final obligations -/

/-- **The open inputs of the joint bound `JB`** (B4; `cor:joint-closing` at the ledger's joint
constant). 5 fields. -/
structure ClassParts (D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap bOf)
    paperTail paperPr paperH Chamber) where
  /-- The classes of (CP5) with their robust evaluated class bounds (`def:cp5`,
  `cor:envelope-costs`, `thm:envelopes`(i), `cor:var-classes`, `lem:var-gain`). *Open*
  (analytic). -/
  CI : ClassInputs D.CL
  /-- The upper data of the class polynomial (`prop:closing-data`(b),(d),
  `lem:record:record-expansion`(iii)) and the variance credit `D_var`
  (`cor:variance:final`(iv), `lem:class-credit`); the sixteen savings are kernel-checked
  (`paperSavings_ge`). *Open* (data with numerical gates). -/
  PD : PolynomialData CI
  /-- The class bounds at energy level on labelled positive diagonals (`thm:envelopes`(i),
  `cor:envelope-costs`). *Open* (analytic). -/
  CE : ClassEnergyInputs D CI
  /-- (E1) for the selections in no class (`def:robust`). *Open* (analytic). -/
  E1 : D.EnvelopeBoundNonneg
  /-- The joint mean allocation: (J2) `prop:record:mean-credit`, (J3) `lem:bracket-energy`, the
  residual gates `b ≤ 63 w` (`cert:four-routes-closing`) and `∑ b u ≥ 64Δ`
  (`prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (analytic; `resid` and `alloc` are
  numerical once `b`, `w`, `u` are explicit). -/
  MA : MeanAllocation D CE

/-- **The open inputs of `SF`, `fix`, `env`** (B5). `SF` goes through `lem:density:coupled` on
the block atoms, with the per-block moments of the first stage proved
(`paperStageMoments_proved`); what remains is the per-term `fibre`, with the scalars `θ ≤ 12/11`,
`ε → 0`, `c₁ ≥ 0`. `fix`, `env` are G1's bundles on the cyclic coordinates. 13 fields, of which
9 are scalars with their side conditions. -/
structure SharpParts {hW : Target.Weil} (D : JointBlockDataTarget bOf hW) where
  /-- The density endpoint `θ` (the paper's `ϑ = 1.014587`), below the catalog's `12/11`. -/
  θ : ℝ
  hθ : 0 < θ
  hθ' : θ ≤ 12 / 11
  /-- The relative error and the remainder constant of the sharp terms. -/
  ε : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ ε L
  hεt : Tendsto ε atTop (𝓝 0)
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  /-- **Per term of the coupled expansion of `lem:sharp-first`: the fibre-moment input**
  (`CoupledFibreMoment`; `prop:density:production` with `lem:record:density-dc`,
  `lem:record:fibre-scale`). *Open* (analytic). -/
  fibre : Param.AtCounterexamples (Param.Params.ofDecay targetDecay) D.data.Y
    (fun L A => ∀ σ : (∀ b, Option (D.data.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ RecordExpansion.countVec (D.data.FS.tag L) σ j →
      ∀ f : (∀ b, EnvelopeInputsBlock.CPiece D.data L b),
      (∀ b, EnvelopeInputsBlock.cpieceCoef D.data L σ j b (f b) ≠ 0) →
        CoupledFibreMoment D.data L A f θ (ε L) c₁)
  /-- The fixed-interval envelope energies on the cyclic coordinates (G1's `fix`,
  `lem:envelope-energy`, `lem:twointerval`(ii)). *Open* (analytic). -/
  fixC : FixedIntervalInputsCRT (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise
  /-- The envelope energies on the cyclic coordinates (G1's `env`, `lem:envelope-energy`,
  `lem:hyb:moment`). *Open* (analytic). -/
  envC : EnvelopeEnergyInputsCRT (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise

structure MainFinalObligations (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  /-- The block data. -/
  Dv : FinalBlockData hW hMR hFour
  /-- The 66 per-piece charge bounds (N1). *Open* (numerical). -/
  NC : NumericalCertificates
  /-- **`S + A ≤ S^{ledger} + A^{ledger}` in explicit per-atom form** (`SAExplicit`;
  `def:closing-quantities`, `def:cp4`(b)): the square-clique prices `λ^ex_p(1) q_p^{2a}`, the
  class-three block prices `s_𝔅 + a_𝔅` and the tail bounds. *Open*; `SAExplicit_of_bands` (B2)
  reduces it to the clique bound `H_iid`, W8's band sums, B7's middle prices `price_sum_le` and a
  numerical sum. -/
  hSA : SAExplicit Dv.Cmp.Ci
  /-- The inputs of the joint bound (B4). -/
  Cls : ClassParts Dv.data
  /-- The inputs of `SF`, `fix`, `env` (B5). -/
  Sh : SharpParts Dv.toJoint

end Sarkozy.MainFinal
