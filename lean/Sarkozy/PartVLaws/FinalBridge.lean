module

public import Sarkozy.EnvelopeInputsBlock.Final
public import Sarkozy.BlockAnchor.PrefixBridge
public import Sarkozy.BlockAnchor.Partition
public import Sarkozy.PartVLaws.PaperBlocks
public import Sarkozy.PartVLaws.TailRowsAll

@[expose] public section

/-!
# The final block statement with the paper's block atoms and the tail inputs in correlation form

`main_anchor_paper_block_v2` is G1's `EnvelopeInputsBlock.main_anchor_paper_block_final` at the
block assignment `blk := paperAtomMap blockOf` (each square-clique prime `{p}` its own atom, each
class-three prime to its block `blockOf j`), with two of CERT1's data fields reduced:

* the four prefix fields `μ₀`, `rp₀`, `inv₀`, `unif₀` (`def:construction`(b), (R1)–(R3)) are
  **proved** from `spec : ∀ b, PaperBlockSpec blockOf b`: for each class-three block, the paper's
  block law (an upper block reference, `lem:upper-reference-rp`, or a middle block reference with
  the uniform, individual or coherent root, `lem:front12:reference`) with its spectral inputs as
  named fields. The square-clique atoms `{p}` need no input (`prefixAtom_rp`, `_inv`, `_unif`).
  The bridge is K0's `BlockAnchor.PrefixBridge` (`v2BlockLaws`, `_rp`, `_inv`, `_unif`);
* `hV` (`lem:tail-law`(i)) is `tailInputsValid_of_corr le_rfl hC`, from
  `hC : TailInputsCorr P₄`: the root envelopes (V1), the correlations (F4) with the numerical
  conditions of (F5)(b), and the layer caps (V3). The count-type inputs are proved
  (`TailRowsAll`).

`V2FinalObligations.toFinal` maps the new structure to G1's `BlockFinalObligations`, field for
field; the other twelve fields and the four `TheoremCBlock` data fields after `FS` are G1's and
CERT1's, with their labels and statuses.

No compatibility condition between `blk` and `blockOf` is needed: G1's theorem holds for every
block assignment, and here `blk` *is* `paperAtomMap blockOf`. For the paper's partition, K0's
`IsPaperPartition` (used by the price lemmas `paperSel_class3_le`, `toy_partition_L₀_le`) follows
from its class-three half alone (`isPaperPartition_paperAtomMap`): the prefix half holds by
construction.

**Field count.**
* G1's `BlockFinalObligations`: 13 fields (`Dp` and 12 others), with `BlockCertData` of 11
  (`μ₀`, `rp₀`, `inv₀`, `unif₀`, `hV`, `FS`, `GB`, `CL`, `ME`, `MC`, `SM`); 23 open leaves.
* `V2FinalObligations`: 13 fields (`Dv` and the same 12 others), with `V2BlockData` of 8 (`spec`,
  `hC`, `FS`, `GB`, `CL`, `ME`, `MC`, `SM`); 20 open leaves. Of the 8, `spec` is per block: an
  upper block has 9 named fields (`UpperBlockInputs`), a middle block 13 to 17
  (`MiddleUniformInputs` 13, `MiddleIndividualInputs` 14, `MiddleCoherentInputs` 17), data
  (weights, inputs, roots) and spectral inputs; `hC` has 9 conjuncts (`TailInputsCorr`).
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.PartVLaws

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (anchorLedger)
open Sarkozy.Labellings Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.FiveType.TwoCoord

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-! ## The paper's block laws with their spectral inputs -/

/-- **The inputs of an upper block** (`lem:upper-reference-rp`, `def:record:upper-bands`): the
band's weights and inputs (data) and the validity of the band inputs (V1)–(V3) on the block
(*open*, spectral, `lem:upper-reference-rp`(ii)). 9 fields. -/
structure UpperBlockInputs (b : B) where
  /-- The primes of the block are at least `81·10¹²` (every block of `[P₃, P₄)`). -/
  hp : ∀ j, (81 * 10 ^ 12 : ℝ) ≤ blockPrimes blockOf b j
  /-- The weights of the block's band (`def:record:upper-bands`). Data. -/
  W : UpperWeights
  /-- The scale `r` of the band inputs. Data. -/
  r : ℝ
  hr : 0 < r
  /-- The ordinary inputs of the band. Data. -/
  ord : FieldTy → CompletionInput
  /-- The reserved inputs of the band. Data. -/
  res : FieldTy → CompletionInput
  /-- The layer caps of the band. Data. -/
  k : PType → PType → ℝ
  /-- **The gates of the weights** (`eq:upper-slice`, `eq:independent-fold-domination`).
  *Open* (rational checks of the band's record). -/
  hWOK : WeightsOK W ord res k
  /-- **(V1)–(V3) on the block** (`lem:upper-reference-rp`(ii)): root envelopes, valid rows and
  layer caps of the block's field laws. *Open* (spectral). -/
  hV : ∀ hne hW' hp', ValidInputs (upperBlockFieldLaws (blockPrimes blockOf b) hne)
    (block_upperDatumHyp (blockPrimes blockOf b) hW' hp' hne) r ord res k

/-- **The inputs of a middle block with the uniform root** (`lem:front12:reference`(iii), pieces
below `2³⁰`): the weights and inputs of its piece (data), the thirteen inequalities `Completes`,
and V1's spectral inputs (*open*, `lem:front12:reference`(i),(ii)). 13 fields. -/
structure MiddleUniformInputs (b : B) where
  /-- The six middle labelling sets are nonempty (`middleNonempty_explicit` at primes `≥ 2²⁰`). -/
  hne : MiddleNonempty (blockPrimes blockOf b)
  /-- The weights of the piece. Data. -/
  W : MiddleWeights
  /-- The inputs of the piece. Data. -/
  I : MiddleInputs
  /-- The scale `r`. Data. -/
  r : ℝ
  hr : 0 ≤ r
  /-- The thirteen inequalities of the piece (`lem:front12:reference`). *Open* (rational). -/
  hW : W.Completes I
  hf₂ : 0 ≤ I.f₂
  hf₁ : 0 ≤ I.f₁
  /-- **The rows** (`lem:front12:reference`(i)), two-layer. *Open* (spectral). -/
  hrows₂ : RowBounds (fieldDatum (middleBlock_datumHyp₂ (blockPrimes blockOf b) hne)) I.f₂ I.h₂ r
  /-- **The rows**, one-layer. *Open* (spectral). -/
  hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.f₁ I.h₁ r
  /-- **The root envelope** (`lem:front12:reference`(ii)), two-layer. *Open* (spectral). -/
  hroot₂ : RootEnvelope (fieldDatum (middleBlock_datumHyp₂ (blockPrimes blockOf b) hne)) I.d r
  /-- **The root envelope**, one-layer. *Open* (spectral). -/
  hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.d₁ r
  /-- **The layer caps** (`lem:front12:reference`(ii)). *Open* (spectral). -/
  hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
    (uniformRoot (blockPrimes blockOf b) hne)) I.k r

/-- **The inputs of a middle block with the individual-square root** (`def:positive-root`, pieces
from `2³⁰`). 14 fields: those of `MiddleUniformInputs` and the root's parameter `u`. -/
structure MiddleIndividualInputs (b : B) where
  /-- The six middle labelling sets are nonempty. -/
  hne : MiddleNonempty (blockPrimes blockOf b)
  /-- The parameter of the individual-square root. Data. -/
  u : ℚ
  W : MiddleWeights
  I : MiddleInputs
  r : ℝ
  hr : 0 ≤ r
  /-- The thirteen inequalities of the piece. *Open* (rational). -/
  hW : W.Completes I
  hf₂ : 0 ≤ I.f₂
  hf₁ : 0 ≤ I.f₁
  /-- **The rows**, two-layer, with the individual-square root. *Open* (spectral). -/
  hrows₂ : RowBounds
    (fieldDatum (middleBlock_datumHyp₂_individual (blockPrimes blockOf b) hne u)) I.f₂ I.h₂ r
  /-- **The rows**, one-layer. *Open* (spectral). -/
  hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.f₁ I.h₁ r
  /-- **The root envelope**, two-layer. *Open* (spectral). -/
  hroot₂ : RootEnvelope
    (fieldDatum (middleBlock_datumHyp₂_individual (blockPrimes blockOf b) hne u)) I.d r
  /-- **The root envelope**, one-layer. *Open* (spectral). -/
  hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.d₁ r
  /-- **The layer caps**. *Open* (spectral). -/
  hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
    (individualBlockRoot (blockPrimes blockOf b) u hne.L2)) I.k r

/-- **The inputs of a middle block with the coherent root** (`def:positive-root`,
`lem:imp:coherent39-law`). 17 fields: those of `MiddleIndividualInputs` and the dictionary with
its invariance and the parameter `η > 0`. -/
structure MiddleCoherentInputs (b : B) where
  /-- The six middle labelling sets are nonempty. -/
  hne : MiddleNonempty (blockPrimes blockOf b)
  /-- The dictionary of the coherent root (`lem:imp:coherent39-law`). Data. -/
  D : Dictionary
  /-- Its `𝒢₆`-invariance. *Open* (finite check of the recorded dictionary). -/
  hD : D.Invariant
  u : ℚ
  η : ℚ
  hη : 0 < η
  W : MiddleWeights
  I : MiddleInputs
  r : ℝ
  hr : 0 ≤ r
  /-- The thirteen inequalities of the piece. *Open* (rational). -/
  hW : W.Completes I
  hf₂ : 0 ≤ I.f₂
  hf₁ : 0 ≤ I.f₁
  /-- **The rows**, two-layer, with the coherent root. *Open* (spectral). -/
  hrows₂ : RowBounds
    (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne D hD u hη))
    I.f₂ I.h₂ r
  /-- **The rows**, one-layer. *Open* (spectral). -/
  hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.f₁ I.h₁ r
  /-- **The root envelope**, two-layer. *Open* (spectral). -/
  hroot₂ : RootEnvelope
    (fieldDatum (middleBlock_datumHyp₂_coherent (blockPrimes blockOf b) hne D hD u hη)) I.d r
  /-- **The root envelope**, one-layer. *Open* (spectral). -/
  hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes blockOf b) hne)) I.d₁ r
  /-- **The layer caps**. *Open* (spectral). -/
  hcap : MiddleLayerCaps (middleBlockFieldLaws (blockPrimes blockOf b) hne
    (coherentBlockRoot (blockPrimes blockOf b) D u hη hne.L2)) I.k r

/-- **The paper's law of one class-three block, with its inputs** (`def:construction`(b)): an
upper block, or a middle block with one of the three roots. -/
inductive PaperBlockSpec (b : B) : Type
  | upper (U : UpperBlockInputs blockOf b)
  | middleUniform (M : MiddleUniformInputs blockOf b)
  | middleIndividual (M : MiddleIndividualInputs blockOf b)
  | middleCoherent (M : MiddleCoherentInputs blockOf b)

variable {blockOf}

/-- **The block atom of a specification**: the paper's block law with (R1)–(R3), from
`upperBlockAtom` or `middleBlockAtom_*`. -/
noncomputable def PaperBlockSpec.toAtom (hW : Target.Weil) {b : B} :
    PaperBlockSpec blockOf b → BlockAtom blockOf b
  | .upper U => upperBlockAtom blockOf hW U.hp U.W U.hr U.hWOK U.hV
  | .middleUniform M => middleBlockAtom_uniform blockOf M.hne M.W M.I M.hr M.hW M.hf₂ M.hf₁
      M.hrows₂ M.hrows₁ M.hroot₂ M.hroot₁ M.hcap
  | .middleIndividual M => middleBlockAtom_individual blockOf M.hne M.u M.W M.I M.hr M.hW M.hf₂
      M.hf₁ M.hrows₂ M.hrows₁ M.hroot₂ M.hroot₁ M.hcap
  | .middleCoherent M => middleBlockAtom_coherent blockOf M.hne M.D M.hD M.u M.hη M.W M.I M.hr
      M.hW M.hf₂ M.hf₁ M.hrows₂ M.hrows₁ M.hroot₂ M.hroot₁ M.hcap

/-- **The paper's block atoms** of the specifications. -/
noncomputable def paperBlockAtomsOf (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b) :
    PaperBlockAtoms blockOf :=
  PaperBlockAtoms.ofAtoms fun b => (spec b).toAtom hW

variable (blockOf)

/-- **The paper's reference on the block atoms** (`def:cp1`), with the paper's block laws (K0's
`v2BlockLaws` of `paperBlockAtomsOf`) and the tail inputs in correlation form. -/
noncomputable abbrev v2Reference (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) :
    TheoremCBlock.Reference paperM0 (paperAtomMap blockOf) :=
  BlockAnchor.blockPaperReference (paperAtomMap blockOf) hW
    (BlockAnchor.v2BlockLaws blockOf (paperBlockAtomsOf hW spec))
    (BlockAnchor.v2BlockLaws_rp blockOf (paperBlockAtomsOf hW spec))
    (BlockAnchor.v2BlockLaws_inv blockOf (paperBlockAtomsOf hW spec))
    (BlockAnchor.v2BlockLaws_unif blockOf (paperBlockAtomsOf hW spec))
    (tailInputsValid_of_corr le_rfl hC)

/-! ## The data and the obligations -/

/-- **The open parts of the comparison data, with the paper's block laws and the tail inputs in
correlation form** (`def:cp0`–`def:cp8`, `def:construction`). CERT1's `BlockCertData` at
`blk := paperAtomMap blockOf`, with `μ₀`, `rp₀`, `inv₀`, `unif₀` replaced by `spec` and `hV` by
`hC`. 8 fields. -/
structure V2BlockData (hW : Target.Weil) where
  /-- **The paper's block laws with their inputs** (`def:construction`(b);
  `lem:upper-reference-rp`(ii), `lem:front12:reference`(i)–(iii)). *Open* (per block: the
  recorded weights and inputs, and the spectral inputs). The square-clique atoms `{p}` are
  proved. -/
  spec : ∀ b, PaperBlockSpec blockOf b
  /-- **The tail inputs in correlation form** (`lem:tail-law`(i)): the root envelopes (V1), the
  correlations (F4) with the numerical conditions of (F5)(b), and the layer caps (V3) at every
  tail prime. *Open* (spectral); the count-type inputs are proved (`tailInputsValid_of_corr`). -/
  hC : TailInputsCorr PartV.P4
  /-- (CP2) at `a₀` on the block atoms, priced by `paperSel`. *Open* (Part V). -/
  FS : TheoremCBlock.FirstStage Params.anchorDecay paperM0 (paperAtomMap blockOf) paperTail
    (BlockAnchor.paperSel (paperAtomMap blockOf)) (v2Reference blockOf hW spec hC)
  /-- (CP3). *Open* (Part V). -/
  GB : TheoremCBlock.GramBracket Params.anchorDecay paperM0 (paperAtomMap blockOf) paperTail
    (BlockAnchor.paperSel (paperAtomMap blockOf)) FS
  /-- (CP4). *Open* (Part V). -/
  CL : TheoremCBlock.ComparisonLaw Params.anchorDecay paperM0 (paperAtomMap blockOf) paperTail
    (BlockAnchor.paperSel (paperAtomMap blockOf)) paperPP paperEP MainAnchor.paperQueries FS
  /-- (CP6). *Open* (Part V). -/
  ME : TheoremCBlock.MatchingEnvelopes Params.anchorDecay paperM0 (paperAtomMap blockOf) paperTail
    GB CL
  /-- (CP7). *Open* (Part V). -/
  MC : TheoremCBlock.MeanCredit Params.anchorDecay paperM0 (paperAtomMap blockOf) paperTail ME
  /-- (CP8). *Open* (Part V). -/
  SM : TheoremCBlock.Summability Params.anchorDecay paperM0 (paperAtomMap blockOf) paperTail ME

variable {blockOf}

/-- **CERT1's data from the paper's block laws**: the four prefix fields are K0's bridge of the
paper's block atoms, and `hV := tailInputsValid_of_corr le_rfl hC`. -/
noncomputable def V2BlockData.toCertData {hW : Target.Weil} (D : V2BlockData blockOf hW) :
    IndexCert.BlockCertData (paperAtomMap blockOf) hW where
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

/-- **Everything that remains between the tree and the target at `a₀`, for the paper's block laws
and the tail inputs in correlation form.** G1's `BlockFinalObligations` at
`blk := paperAtomMap blockOf` over `V2BlockData`. 13 fields: the open data `Dv` and 12 others,
which are G1's (K0's, D1's, P1's), with their labels and statuses. -/
structure V2FinalObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dv : V2BlockData blockOf hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a₀`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds Params.anchorDecay paperM0 (paperAtomMap blockOf) paperTail
    Dv.toCertData.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dv.toCertData.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dv.toCertData.toData.B * monomial (Dv.toCertData.toData.CL.π L) ω
      else CB.phi L ω) ≤ anchorLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dv.toCertData.toData.B ≤ anchorLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)), with the first-stage prices at the paper's block factors.
  *Open* (Part V). -/
  hL₀ : Dv.toCertData.toData.L₀ ≤ anchorLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dv.toCertData.toData.ME.T ≤ anchorLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dv.toCertData.toData.CL.S + Dv.toCertData.toData.CL.A ≤ anchorLedger.S + anchorLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
    anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
    anchorLedger.upperError) ≤ Dv.toCertData.toData.MC.m
  /-- **(E1), per term** (`lem:bracket-energy`, `lem:density:coupled`), at `a₀`, on the block
  atoms. *Open* (G1's `E1`). -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dv.toCertData.toData
  /-- **The sharp first-stage terms, per term** (`lem:sharp-first`, `lem:density:coupled`), at
  `a₀`, on the block atoms. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toCertData.toData
  /-- **The fixed-interval envelope energies, per term** (`lem:envelope-energy`,
  `lem:hyb:moment`), at `a₀`, on the block atoms. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs
    (BlockAnchor.index_coprime_block Dv.toCertData.toData) Dv.toCertData.toData
  /-- **The envelope energies, per term** (`lem:envelope-energy`, `lem:hyb:moment`), at `a₀`, on
  the block atoms. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs
    (BlockAnchor.index_coprime_block Dv.toCertData.toData) Dv.toCertData.toData

variable {blockOf}

/-- **G1's obligations from the paper's block laws**: `Dp := Dv.toCertData`; the other twelve
fields are copied. -/
noncomputable def V2FinalObligations.toFinal {hW : Target.Weil}
    (O : V2FinalObligations blockOf hW) :
    EnvelopeInputsBlock.BlockFinalObligations (paperAtomMap blockOf) hW where
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

/-- **The target at `a₀` for the paper's block laws, with the tail inputs in correlation form**
(`thm:main` at the formal exponent, via `thm:comparison` and `thm:density:induction`). From the
literature inputs, H2″ (`Target.ThetaSmall`) and `V2FinalObligations blockOf`, for any partition
`blockOf` of the class-three primes into blocks: G1's `main_anchor_paper_block_final` at
`blk := paperAtomMap blockOf`, with `V2FinalObligations.toFinal`. -/
theorem main_anchor_paper_block_v2 (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmall : Target.ThetaSmall) (O : V2FinalObligations blockOf hWeil) :
    Target.SarkozyBound Param.anchorSaving :=
  EnvelopeInputsBlock.main_anchor_paper_block_final hWeil hMovingRoot hFourCycle
    hThetaSmall O.toFinal

/-! ## The paper's partition -/

variable (blockOf)

omit [Fintype B] [DecidableEq B] in
/-- **K0's `IsPaperPartition` for the atom map**: the square-clique primes are singletons by
construction, so only the class-three half (`def:record:exact-blocks`,
`def:record:upper-bands`(b)) is a condition on `blockOf`. -/
theorem isPaperPartition_paperAtomMap
    (h3 : ∀ β : PaperAtom B, (∃ i : PaperJ0, paperAtomMap blockOf i = β ∧ i.1 % 4 = 3) →
      (∃ M : PartV.MiddleBlock, ∀ i : PaperJ0, paperAtomMap blockOf i = β ↔ i.1 ∈ M.primes) ∨
        (∃ U : PartV.UpperBlock, ∀ i : PaperJ0, paperAtomMap blockOf i = β ↔ i.1 ∈ U.primes)) :
    BlockAnchor.IsPaperPartition (paperAtomMap blockOf) where
  prefix_singleton i j hi hji := by
    have hpi : paperAtomMap blockOf i = .inl ⟨i, hi⟩ := by
      simp only [paperAtomMap, hi, ↓reduceDIte]
    rw [hpi] at hji
    have := paperAtomMap_inl blockOf hji
    exact this
  class3_block := h3

end Sarkozy.PartVLaws
