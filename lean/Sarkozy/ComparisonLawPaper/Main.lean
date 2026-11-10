module

public import Sarkozy.ComparisonLawPaper.Paper
public import Sarkozy.GramBracketPaper.ProvedTail

@[expose] public section

/-!
# The main statement at `a_T` with the comparison law assembled from per-atom inputs

A2's `GramBracketPaper.main_target_paper_block_A2` with the obligation `CL` (`def:cp4` at `a_T`)
replaced by the assembly `comparisonLawTarget blockOf hW spec hC In Ci`
(`Sarkozy.ComparisonLawPaper.Paper`) from the named per-atom inputs
`Ci : ComparisonInputs blockOf hW spec hC In`, and the obligation `hSA` replaced by its explicit
form over the per-atom prices.

* `B2BlockDataTarget`: A2's `A2BlockDataTarget` (8 fields) with `CL` replaced by `Ci`; `ME`, `MC`,
  `SM` are over the assembled law. `toA2` maps it to A2's structure, with
  `CL := comparisonLawTarget …`. `ofProvedTail` supplies `hC` as A2's does.
* `B2FinalObligationsTarget`: A2's `A2FinalObligationsTarget` (13 fields) over `B2BlockDataTarget`,
  with `hSA` replaced by **`hSA'`**: `∑_{p ≡ 1 (4)} λ^ex_p(1) q_p^{2a} + ∑_𝔅 (s_𝔅 + a_𝔅) + S_tail
  + A_tail ≤ S^{ledger} + A^{ledger}`, the per-atom prices at `paperSelAt · a_T`. The other eleven
  fields are A2's, verbatim over `Dv.toA2`. `toA2` maps it to A2's, with `hSA` from `hSA'`
  (`hSA_of_prices`).
* **`main_target_paper_block_B2`**: the bound `N^{1 − a_T/71}` from the literature inputs and
  `B2FinalObligationsTarget blockOf hWeil`.

**Field count.** A2's 18 open obligations (`spec`, `Gi`, `CL`, `ME`, `MC`, `SM`; `CB`, `hΨ`, `hCB`,
`hB`, `hL₀`, `hT`, `hSA`, `hm`, `E1`, `SF`, `fix`, `env`) stay 18 in number, with `CL` replaced by
`Ci` and `hSA` by `hSA'`. `Ci : ComparisonInputs` has 7 fields: 5 open (`clique`, `block`, `tail`,
`tail_S`, `tail_A`) and the numbers `St`, `At`; `block` is per specification (`UpperAtomInputs`, 6
fields, on an upper block; the atom data on a middle block). `hSA'` is an explicit inequality
between sums of per-atom prices and two ledger entries (`SAExplicit`; by ranges in
`Sarkozy.ComparisonLawPaper.Prices`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
open Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec TailInputsCorr paperAtomMap PaperAtom PrefixCoord)

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- **A2's `A2BlockDataTarget` with the comparison law assembled** (`def:cp4` by
`comparisonLawTarget`): `spec`, `hC`, `In`, `Gi` as in A2, the per-atom inputs `Ci` of (CP4),
and the Part V data `ME`, `MC`, `SM` at `a_T` over the constructed bracket and the assembled law.
8 fields. -/
structure B2BlockDataTarget (hW : Target.Weil) where
  /-- The paper's block laws with their inputs (`def:construction`(b)). *Open* (V2's `spec`). -/
  spec : ∀ b, PaperBlockSpec blockOf b
  /-- The tail inputs in correlation form (supplied by `ofProvedTail`). -/
  hC : TailInputsCorr PartV.P4
  /-- The per-block constants of the first stage (A1's `FirstStageInputs`). Data. -/
  In : FirstStageInputs blockOf
  /-- The gates of the Gram bracket (A2's `GramInputs`). *Open*. -/
  Gi : GramInputs blockOf spec
  /-- **The per-atom inputs of (CP4)** (`ComparisonInputs`). Replaces A2's `CL`. *Open*. -/
  Ci : ComparisonInputs blockOf hW spec hC In
  /-- (CP6) at `a_T`, over the constructed bracket and the assembled law. *Open* (Part V). -/
  ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (gramBracketTarget blockOf hW spec hC In Gi) (comparisonLawTarget blockOf hW spec hC In Ci)
  /-- (CP7) at `a_T`. *Open* (Part V). -/
  MC : TheoremCBlock.MeanCredit targetDecay paperM0 (paperAtomMap blockOf) paperTail ME
  /-- (CP8) at `a_T`. *Open* (Part V). -/
  SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME

variable {blockOf}

/-- **To A2's data**: `CL := comparisonLawTarget blockOf hW spec hC In Ci`, the other seven fields
copied. -/
noncomputable def B2BlockDataTarget.toA2 {hW : Target.Weil} (D : B2BlockDataTarget blockOf hW) :
    A2BlockDataTarget blockOf hW where
  spec := D.spec
  hC := D.hC
  In := D.In
  Gi := D.Gi
  CL := comparisonLawTarget blockOf hW D.spec D.hC D.In D.Ci
  ME := D.ME
  MC := D.MC
  SM := D.SM

variable (blockOf) in
/-- **The data with the proved tail** (A2's `ofProvedTail`): `hC := tailInputsCorr hW hMR hFour`. -/
noncomputable def B2BlockDataTarget.ofProvedTail
    (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (spec : ∀ b, PaperBlockSpec blockOf b) (In : FirstStageInputs blockOf)
    (Gi : GramInputs blockOf spec)
    (Ci : ComparisonInputs blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In)
    (ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (gramBracketTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In Gi)
      (comparisonLawTarget blockOf hW spec (TailCorrCore.tailInputsCorr hW hMR hFour) In Ci))
    (MC : TheoremCBlock.MeanCredit targetDecay paperM0 (paperAtomMap blockOf) paperTail ME)
    (SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME) :
    B2BlockDataTarget blockOf hW where
  spec := spec
  hC := TailCorrCore.tailInputsCorr hW hMR hFour
  In := In
  Gi := Gi
  Ci := Ci
  ME := ME
  MC := MC
  SM := SM

/-- **The explicit form of `hSA`** (`def:closing-quantities`, `def:cp4`(b)): the square-clique
prices `λ^ex_p(1) q_p^{2a}`, the class-three block prices `s_𝔅 + a_𝔅` (both at `paperSelAt · a_T`)
and the tail bounds sum to at most `S^{ledger} + A^{ledger}`. -/
def SAExplicit {hW : Target.Weil} {spec : ∀ b, PaperBlockSpec blockOf b}
    {hC : TailInputsCorr PartV.P4} {In : FirstStageInputs blockOf}
    (Ci : ComparisonInputs blockOf hW spec hC In) : Prop :=
  ∑ q, Ci.cliquePrice q + ∑ b, Ci.blockPrice b + (Ci.St + Ci.At) ≤ targetLedger.S + targetLedger.A

/-- **`hSA` from the per-atom prices** (`def:cp4`(b): `S = ∑_𝔟 s_𝔟`, `A = ∑_𝔟 a_𝔟`): for the
assembled law, `S + A ≤ S^{ledger} + A^{ledger}` is `SAExplicit`. -/
theorem hSA_of_prices {hW : Target.Weil} (D : B2BlockDataTarget blockOf hW) (h : SAExplicit D.Ci) :
    D.toA2.toA1.toV2.toCertData.toData.CL.S + D.toA2.toA1.toV2.toCertData.toData.CL.A ≤
      targetLedger.S + targetLedger.A := by
  change (comparisonLawTarget blockOf hW D.spec D.hC D.In D.Ci).S +
    (comparisonLawTarget blockOf hW D.spec D.hC D.In D.Ci).A ≤ _
  rw [comparisonLawTarget_SA]
  exact h

variable (blockOf)

/-- **A2's `A2FinalObligationsTarget` with the comparison law assembled.** 13 fields: the data `Dv`,
A2's eleven other fields verbatim over `Dv.toA2`, and `hSA'` (the explicit form of `hSA`). -/
structure B2FinalObligationsTarget (hW : Target.Weil) where
  /-- The data, with the first stage, the Gram bracket and the comparison law constructed. -/
  Dv : B2BlockDataTarget blockOf hW
  /-- The (CP5) class bounds at `a_T`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds targetDecay paperM0 (paperAtomMap blockOf) paperTail
    Dv.toA2.toA1.toV2.toCertData.toData.CL
  /-- The complete polynomial with class bounds is at most the ledger's `E`. *Open*. -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter
      (fun ω : Choice (Dv.toA2.toA1.toV2.toCertData.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then
      Dv.toA2.toA1.toV2.toCertData.toData.B *
        monomial (Dv.toA2.toA1.toV2.toCertData.toData.CL.π L) ω
      else CB.phi L ω) ≤ targetLedger.E
  /-- The class bounds are robust with nonnegative remainders. *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` (A2's `hB_of_prices`). *Open*. -/
  hB : Dv.toA2.toA1.toV2.toCertData.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀` (A1's `hL₀_of_prices`). *Open*. -/
  hL₀ : Dv.toA2.toA1.toV2.toCertData.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T`. *Open*. -/
  hT : Dv.toA2.toA1.toV2.toCertData.toData.ME.T ≤ targetLedger.T
  /-- **`S + A ≤` the ledger's `S + A`, in explicit form** (`SAExplicit`): the per-atom prices of
  the square-clique atoms and the class-three blocks, and the tail bounds. *Open*. -/
  hSA' : SAExplicit Dv.Ci
  /-- The mean credit pays the joint-closing allocations. *Open*. -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dv.toA2.toA1.toV2.toCertData.toData.MC.m
  /-- (E1), per term. *Open* (G1's `E1`). -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dv.toA2.toA1.toV2.toCertData.toData
  /-- The sharp first-stage terms, per term. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toA2.toA1.toV2.toCertData.toData
  /-- The fixed-interval envelope energies, per term. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toA2.toA1.toV2.toCertData.toData)
    Dv.toA2.toA1.toV2.toCertData.toData
  /-- The envelope energies, per term. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toA2.toA1.toV2.toCertData.toData)
    Dv.toA2.toA1.toV2.toCertData.toData

variable {blockOf}

/-- **To A2's obligations**: `Dv := Dv.toA2`, `hSA := hSA_of_prices Dv hSA'`, the other eleven
fields copied. -/
noncomputable def B2FinalObligationsTarget.toA2 {hW : Target.Weil}
    (O : B2FinalObligationsTarget blockOf hW) : A2FinalObligationsTarget blockOf hW where
  Dv := O.Dv.toA2
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := hSA_of_prices O.Dv O.hSA'
  hm := O.hm
  E1 := O.E1
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵`, with the first stage, the Gram bracket and
the comparison law of the paper's construction** (`thm:main` at `ε = a_T/71`, via
`thm:comparison` and `thm:density:induction` at `a_T`): from the literature inputs (`Weil`,
`MovingRoot`, `FourCycle`, H2″) and `B2FinalObligationsTarget blockOf`, in which
(CP2) is A1's `firstStageTarget`, (CP3) is A2's `gramBracketTarget`, and (CP4) is
`comparisonLawTarget` (`def:cp4`), assembled from the per-atom inputs `ComparisonInputs`;
`hSA` is in explicit per-atom form (`SAExplicit`). -/
theorem main_target_paper_block_B2 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (O : B2FinalObligationsTarget blockOf hWeil) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_A2 hWeil hMovingRoot hFourCycle hThetaSmallRR O.toA2

end Sarkozy.ComparisonLawPaper
