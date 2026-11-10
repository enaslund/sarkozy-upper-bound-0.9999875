module

public import Sarkozy.MainTarget.Block
public import Sarkozy.PartVLaws.FinalBridge

@[expose] public section

/-!
# The final block statement at the target `a_T`, with the paper's block atoms and the tail inputs
in correlation form

V2's `PartVLaws.FinalBridge` (`main_anchor_paper_block_v2`) at the owner's target
`a_T = 212956239/250000000000` (`Target.epsTarget = 3/250000`, the bound `N^{0.999988}`)
(since RG's rebase of 7 November 2026 the ledger's exponent `TargetLedger.targetDecay` is
`a_G = 71/10⁵`, its saving `10⁻⁵`, and `Θ < 0.72`; the `a_T` below names that exponent).

`V2BlockDataTarget` and `V2FinalObligationsTarget` are V2's `V2BlockData` and
`V2FinalObligations` with the exponent `a₀` replaced by `a_T` in every Part V field, the prices
`paperSel` by `paperSelAt · a_T` (`def:price` at `a_T`) and the ledger `anchorLedger` by
`targetLedger`. What does not depend on the exponent is V2's, reused unchanged:
* the paper's block laws with their spectral inputs, `PartVLaws.PaperBlockSpec blockOf b`
  (`def:construction`(b), `lem:upper-reference-rp`, `lem:front12:reference`), and K0's bridge to
  the four prefix fields `μ₀`, `rp₀`, `inv₀`, `unif₀` (`BlockAnchor.v2BlockLaws`, `_rp`, `_inv`,
  `_unif`);
* the tail inputs in correlation form `PartVLaws.TailInputsCorr P₄` (`lem:tail-law`(i)), with the
  count-type inputs proved (`PartVLaws.tailInputsValid_of_corr`);
* the reference `PartVLaws.v2Reference` (`def:cp1`).

`V2FinalObligationsTarget.toFinal` maps the new structure to
`MainTarget.BlockFinalObligationsTarget` (G1's `BlockFinalObligations` at `a_T`) field for
field, as V2's `toFinal` does at `a₀`.
`main_target_paper_block_v2_of_hR` concludes the target from the literature inputs, the index moment
`hR` (`cert:index-moment` at `a_T`) and the obligations; `MainTarget.Main` discharges `hR` from H2″.

**Field count** (as V2's at `a₀`). `V2FinalObligationsTarget`: 13 fields (`Dv` and 12 others), with
`V2BlockDataTarget` of 8 (`spec`, `hC`, `FS`, `GB`, `CL`, `ME`, `MC`, `SM`); 20 open leaves.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.MainTarget

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor
open Sarkozy.PartVLaws (PaperBlockSpec paperBlockAtomsOf v2Reference TailInputsCorr
  tailInputsValid_of_corr paperAtomMap)

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-! ## The data and the obligations at `a_T` -/

/-- **The open parts of the comparison data at `a_T`, with the paper's block laws and the tail
inputs in correlation form** (`def:cp0`–`def:cp8`, `def:construction`). V2's `V2BlockData` at the
price exponent `a_T`, priced by `paperSelAt (paperAtomMap blockOf) a_T`. 8 fields. -/
structure V2BlockDataTarget (hW : Target.Weil) where
  /-- **The paper's block laws with their inputs** (`def:construction`(b);
  `lem:upper-reference-rp`(ii), `lem:front12:reference`(i)–(iii)). *Open* (per block: the
  recorded weights and inputs, and the spectral inputs). No exponent. -/
  spec : ∀ b, PaperBlockSpec blockOf b
  /-- **The tail inputs in correlation form** (`lem:tail-law`(i)). *Open* (spectral); the
  count-type inputs are proved (`tailInputsValid_of_corr`). No exponent. -/
  hC : TailInputsCorr PartV.P4
  /-- (CP2) at `a_T` on the block atoms, priced by `paperSelAt · a_T`. *Open* (Part V). -/
  FS : TheoremCBlock.FirstStage targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) (v2Reference blockOf hW spec hC)
  /-- (CP3) at `a_T`. *Open* (Part V). -/
  GB : TheoremCBlock.GramBracket targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) FS
  /-- (CP4) at `a_T`. *Open* (Part V). -/
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP paperQueries FS
  /-- (CP6) at `a_T`. *Open* (Part V). -/
  ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 (paperAtomMap blockOf) paperTail GB CL
  /-- (CP7) at `a_T`. *Open* (Part V). -/
  MC : TheoremCBlock.MeanCredit targetDecay paperM0 (paperAtomMap blockOf) paperTail ME
  /-- (CP8) at `a_T`. *Open* (Part V). -/
  SM : TheoremCBlock.Summability targetDecay paperM0 (paperAtomMap blockOf) paperTail ME

variable {blockOf}

/-- **The data at `a_T` from the paper's block laws**: the four prefix fields are K0's bridge of
the paper's block atoms, and `hV := tailInputsValid_of_corr le_rfl hC` (as V2's `toCertData`). -/
noncomputable def V2BlockDataTarget.toCertData {hW : Target.Weil}
    (D : V2BlockDataTarget blockOf hW) : BlockCertDataTarget (paperAtomMap blockOf) hW where
  μ₀ := BlockAnchor.v2BlockLaws blockOf (paperBlockAtomsOf hW D.spec)
  rp₀ := BlockAnchor.v2BlockLaws_rp blockOf (paperBlockAtomsOf hW D.spec)
  inv₀ := BlockAnchor.v2BlockLaws_inv blockOf (paperBlockAtomsOf hW D.spec)
  unif₀ := BlockAnchor.v2BlockLaws_unif blockOf (paperBlockAtomsOf hW D.spec)
  hV := tailInputsValid_of_corr le_rfl D.hC
  FS := D.FS
  GB := D.GB
  CL := D.CL
  ME := D.ME
  MC := D.MC
  SM := D.SM

variable (blockOf)

/-- **Everything that remains between the tree and the bound `N^{1 − a_T/71}`, for the paper's
block laws and the tail inputs in correlation form.** V2's `V2FinalObligations` at the price
exponent `a_T` with the ledger `targetLedger` (`TargetLedger.Numerics`, `Θ < 0.72` at `a_G`). 13
fields: the open data `Dv` and 12 others, with V2's (G1's, K0's, D1's, P1's) labels and
statuses, now at `a_T`. -/
structure V2FinalObligationsTarget (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`) at `a_T`. *Open*
  (Part V). -/
  Dv : V2BlockDataTarget blockOf hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a_T`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds targetDecay paperM0 (paperAtomMap blockOf) paperTail
    Dv.toCertData.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dv.toCertData.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dv.toCertData.toData.B * monomial (Dv.toCertData.toData.CL.π L) ω
      else CB.phi L ω) ≤ targetLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dv.toCertData.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)), with the first-stage prices at the paper's block factors
  at `a_T`. *Open* (Part V). -/
  hL₀ : Dv.toCertData.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dv.toCertData.toData.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dv.toCertData.toData.CL.S + Dv.toCertData.toData.CL.A ≤ targetLedger.S + targetLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dv.toCertData.toData.MC.m
  /-- **(E1), per term** (`lem:bracket-energy`, `lem:density:coupled`), at `a_T`, on the block
  atoms. *Open* (G1's `E1`). -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dv.toCertData.toData
  /-- **The sharp first-stage terms, per term** (`lem:sharp-first`, `lem:density:coupled`), at
  `a_T`, on the block atoms. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toCertData.toData
  /-- **The fixed-interval envelope energies, per term** (`lem:envelope-energy`,
  `lem:hyb:moment`), at `a_T`, on the block atoms. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toCertData.toData) Dv.toCertData.toData
  /-- **The envelope energies, per term** (`lem:envelope-energy`, `lem:hyb:moment`), at `a_T`, on
  the block atoms. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toCertData.toData) Dv.toCertData.toData

variable {blockOf}

/-- **The `a_T` obligations at G1's level from the paper's block laws**: `Dp := Dv.toCertData`;
the other twelve fields are copied. -/
noncomputable def V2FinalObligationsTarget.toFinal {hW : Target.Weil}
    (O : V2FinalObligationsTarget blockOf hW) :
    BlockFinalObligationsTarget (paperAtomMap blockOf) hW where
  Dp := O.Dv.toCertData
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  hm := O.hm
  E1 := O.E1
  SF := O.SF
  fix := O.fix
  env := O.env

/-- **The bound `N^{1 − a_T/71}` for the paper's block laws, with the tail inputs in correlation
form, given the index moment at `a_T`** (`thm:main` at the target exponent, via `thm:comparison`
and `thm:density:induction` at `a = a_T`). From the literature inputs, `cert:index-moment` at
`a_T` as the hypothesis `hR`, and `V2FinalObligationsTarget blockOf`, for any partition
`blockOf` of the class-three primes into blocks. -/
theorem main_target_paper_block_v2_of_hR (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hR : paperRIAt targetDecay ≤ targetLedger.R_I)
    (O : V2FinalObligationsTarget blockOf hWeil) : Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_final_of_hR hWeil hMovingRoot hFourCycle hR O.toFinal

end Sarkozy.MainTarget
