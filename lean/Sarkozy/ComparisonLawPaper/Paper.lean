module

public import Sarkozy.ComparisonLawPaper.Blocks
public import Sarkozy.FirstStagePaper.Paper

@[expose] public section






open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.FirstStagePaper Sarkozy.PartVLaws Sarkozy.CancellationSteps Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay)

variable {B : Type} [Fintype B] [DecidableEq B] (blockOf : PaperJ0 → B)

/-- **The first-stage law `λ_β` of a prefix atom** of the paper's construction: `ρ + δ_E` of A1's
`paperStage` (`def:cp2`). It is `μ_β` on the square-clique atoms and the upper blocks. -/
noncomputable abbrev paperLam (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (β : PaperAtom B) :
    SlotMeasure (BlockRes paperM0 (paperAtomMap blockOf) β) :=
  (paperStage blockOf hW spec hC In β).ρ +
    ∑ i, ((paperStage blockOf hW spec hC In β).κ' i - (paperStage blockOf hW spec hC In β).κ i)

/-- The acceptance relation of a prefix atom of the paper (`def:cp4`(a)). -/
abbrev paperPrefixAccepted (β : PaperAtom B) :
    BlockRes paperM0 (paperAtomMap blockOf) β → BlockRes paperM0 (paperAtomMap blockOf) β → Prop :=
  prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP β

/-- A tail prime of the scale `L` is at least `P₄`. -/
theorem P4_le_paperTail {L : ℕ} (j : PaperJt L) : PartV.P4 ≤ paperTail L j :=
  (mem_paperTailPrimes.mp j.2).2.1

/-- **The inputs of (CP4) for the paper's construction** (`def:cp4`, at `a_T`), relative to A1's
first stage. 7 fields; `St`, `At` are numbers. Field review against the paper:
* `clique` (`lem:frontier:iidenergy`(ii), `lem:frontier:iidlocal`(iv),(v)): at the square-clique
  atom `{p}`, `ν_p = λ_p - λ^ex_p`, as `DeletionInputs` relative to `μ_p` (`λ_p = μ_p`,
  `paperLam_inl`; not a first-stage atom): the normalized exception `κ̄ = λ^ex_p/λ^ex_p(1)`
  (symmetric at `ι`, uniform one-slot marginals), its mass `ω = λ^ex_p(1) < 1`, and the retained
  law `ν̄` with `(1 - ω) ν̄ = μ_p - ω κ̄`, accepted (its uniform marginals follow, from (R3) of
  `μ_p`). The (CP4)(b)
  data (`ζ^s = -λ^ex_p`, `ζ^a = 0`, `π̃^s = λ^ex_p(1)`, `π̃^a = 0`) and the brackets are then
  constructed (`DeletionInputs.toAtom`), with the envelope `Diag_ι(m_+(κ̄))` (`= κ̄` when `κ̄` is
  fixed samplewise by `ι`, as in the paper).
* `block` (`BlockInputs`, by the block's specification): on an upper block (`prop:record:upper`(i),
  `def:upper-comparison`) W8's construction with `UpperAtomInputs` (the replacing laws of the
  changed records with their acceptance and uniform marginals, and the brackets of their changes);
  on a middle block (`lem:middle-comparison-prices`, `subsec:middle-comparison`) the atom data
  relative to A1's `λ_𝔅 = ρ + δ_E` (the paper: "the two-layer records enter `λ_𝔅` with the weights
  of `μ_𝔅`"; three components `ν⁺`, `Π^{--}_{F₁}`, `Π^{--}_{F₂}`).
* `tail` (`lem:tail-prices`(i),(ii)): at a tail prime `q ≥ P₄`, the law `ν_q = w ν̄_q` relative to
  `μ_q` (the tail atoms carry no first-stage records), as `TailAtomInputs` (with `TailNonempty q`
  proved under H1, `tailNe`): `ν̄_q` with V3's `AcceptedTailData` (the facts of (i) that
  `lem:record:tail-mixing` uses), the mass
  `w > 0`, and the records and brackets of (ii). Acceptance, uniform marginals, one nonnegative
  component and (R4) for `ν̄_q` at `q ≥ P₅` are proved from it (`TailAtomInputs.toAtom`,
  `toAtom_single`, `toAtom_mixing`).
* `St`, `At`, `tail_S`, `tail_A` (`lem:tail-prices`(iv)): the tail price sums
  `∑_{P₄ ≤ p ≤ N^{1/20}} s_p ≤ S_tail`, `∑ a_p ≤ A_tail` at every scale, at `a_T`.

The pair-marginal convention is the paper's: `TailMixing` asks the query pairs of `ν̄_q` to be
`Unif(Ω_q)` (strict-square pairs), consistent with `accept` (`tailAccepted`: nonzero squares). -/
structure ComparisonInputs (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) where
  /-- (CP4) at the square-clique atoms (`lem:frontier:iidenergy`(ii)), as a deletion. *Open*. -/
  clique : ∀ q : PrefixCoord, DeletionInputs ((v2Reference blockOf hW spec hC).μ₀ (.inl q))
    (paperPrefixAccepted blockOf (.inl q)) MainAnchor.paperQueries
  /-- (CP4) at the class-three blocks, by their specification (`prop:record:upper`(i) through
  `UpperAtomInputs`; `lem:middle-comparison-prices`). *Open*. -/
  block : ∀ b : B, BlockInputs hW In (spec b)
  /-- (CP4) at the tail primes (`lem:tail-prices`(i),(ii)), as `TailAtomInputs`. *Open*. -/
  tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
    TailAtomInputs q (tailNe hW h4) (signedIntegral ((v2Reference blockOf hW spec hC).μp q).weight)
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

variable {blockOf}

omit [Fintype B] in
/-- At a square-clique atom the first-stage law is the reference: `λ_p = μ_p`. -/
theorem paperLam_inl (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (q : PrefixCoord) :
    paperLam blockOf hW spec hC In (.inl q) =
      signedIntegral ((v2Reference blockOf hW spec hC).μ₀ (.inl q)).weight := by
  change signedIntegral _ + ∑ i : Empty, _ = _
  rw [Finset.univ_eq_empty, sum_empty, add_zero]

/-- The data of a prefix atom: `clique` at a square-clique atom, `block` at a class-three block. -/
noncomputable def ComparisonInputs.pre {hW : Target.Weil} {spec : ∀ b, PaperBlockSpec blockOf b}
    {hC : TailInputsCorr PartV.P4} {In : FirstStageInputs blockOf}
    (I : ComparisonInputs blockOf hW spec hC In) :
    ∀ β : PaperAtom B, AtomComparison (paperLam blockOf hW spec hC In β)
      (paperPrefixAccepted blockOf β) MainAnchor.paperQueries
  | .inl q => ((I.clique q).toAtom ((v2Reference blockOf hW spec hC).unif₀ (.inl q))).congrLam
      (paperLam_inl hW spec hC In q).symm
  | .inr b => BlockInputs.toAtom hW In (spec b) (I.block b)

/-- The atom data of a class-three block. -/
noncomputable abbrev ComparisonInputs.blockAtom {hW : Target.Weil}
    {spec : ∀ b, PaperBlockSpec blockOf b} {hC : TailInputsCorr PartV.P4}
    {In : FirstStageInputs blockOf} (I : ComparisonInputs blockOf hW spec hC In) (b : B) :
    AtomComparison (specLam hW In (spec b))
      (prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b))
      MainAnchor.paperQueries :=
  BlockInputs.toAtom hW In (spec b) (I.block b)

/-- The price `s_p + a_p = λ^ex_p(1) q_p^{2a}` of a square-clique atom. -/
noncomputable def ComparisonInputs.cliquePrice {hW : Target.Weil}
    {spec : ∀ b, PaperBlockSpec blockOf b} {hC : TailInputsCorr PartV.P4}
    {In : FirstStageInputs blockOf} (I : ComparisonInputs blockOf hW spec hC In) (q : PrefixCoord) :
    ℝ :=
  (I.clique q).ω * MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q)

/-- The price `s_𝔅 + a_𝔅` of a class-three block. -/
noncomputable def ComparisonInputs.blockPrice {hW : Target.Weil}
    {spec : ∀ b, PaperBlockSpec blockOf b} {hC : TailInputsCorr PartV.P4}
    {In : FirstStageInputs blockOf} (I : ComparisonInputs blockOf hW spec hC In) (b : B) : ℝ :=
  (I.blockAtom b).sprice (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inr b)) +
    (I.blockAtom b).aprice (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inr b))

/-- The data of a tail atom of the scale `L`. -/
noncomputable def ComparisonInputs.tailAt {hW : Target.Weil}
    {spec : ∀ b, PaperBlockSpec blockOf b} {hC : TailInputsCorr PartV.P4}
    {In : FirstStageInputs blockOf} (I : ComparisonInputs blockOf hW spec hC In) (L : ℕ)
    (j : PaperJt L) :
    AtomComparison (signedIntegral ((v2Reference blockOf hW spec hC).μp (paperTail L j)).weight)
      (tailAccepted (paperTail L j)) MainAnchor.paperQueries :=
  (I.tail (paperTail L j) (P4_le_paperTail j)).toAtom

variable (blockOf) in
/-- **(CP4) for the paper's construction** (`def:cp4`) at `a_T` with the paper's prices
`paperSelAt · a_T`, over A1's `firstStagePaper`: `comparisonLawOfAtoms` with the inputs `I`. -/
noncomputable def comparisonLawPaper (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) (I : ComparisonInputs blockOf hW spec hC In) :
    TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP
      MainAnchor.paperQueries (firstStagePaper blockOf targetDecay
        (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay) hW spec hC In) :=
  comparisonLawOfAtoms targetDecay paperM0 (paperAtomMap blockOf) paperTail
    (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay) (v2Reference blockOf hW spec hC)
    (Fin 2) tagCut tagCut_family (firstChamberCut 0) firstChamberCut_zero_family
    (paperStage blockOf hW spec hC In) paperPP paperEP MainAnchor.paperQueries I.pre I.tailAt
    (fun L j => (I.tail (paperTail L j) (P4_le_paperTail j)).toAtom_single)
    (fun L j i h => (I.tail (paperTail L j) (P4_le_paperTail j)).toAtom_mixing hW h i)
    I.St I.At I.tail_S I.tail_A

variable (blockOf) in
/-- **(CP4) for the paper's construction at the target `a_T`** (`def:cp4`), over A1's
`firstStageTarget`: exactly the type of A2's field `A2BlockDataTarget.CL`. It is
`comparisonLawPaper`. Irreducible, as `firstStageTarget`; `comparisonLawTarget_S`, `_A` give its
totals. -/
@[irreducible] noncomputable def comparisonLawTarget (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) (I : ComparisonInputs blockOf hW spec hC In) :
    TheoremCBlock.ComparisonLaw targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay) paperPP paperEP
      MainAnchor.paperQueries (firstStageTarget blockOf hW spec hC In) := by
  with_unfolding_all exact comparisonLawPaper blockOf hW spec hC In I

/-- **The symmetric total of the paper's comparison law**: `S = ∑_β s_β + S_tail`, the sum over the
prefix atoms of their symmetric prices at `paperSelAt · a_T`, plus the tail bound. -/
theorem comparisonLawTarget_S (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf)
    (I : ComparisonInputs blockOf hW spec hC In) :
    (comparisonLawTarget blockOf hW spec hC In I).S =
      ∑ β, (I.pre β).sprice (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay β) +
        I.St := by
  unfold comparisonLawTarget
  rfl

/-- **The skew total of the paper's comparison law**: `A = ∑_β a_β + A_tail`. -/
theorem comparisonLawTarget_A (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf)
    (I : ComparisonInputs blockOf hW spec hC In) :
    (comparisonLawTarget blockOf hW spec hC In I).A =
      ∑ β, (I.pre β).aprice (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay β) +
        I.At := by
  unfold comparisonLawTarget
  rfl

/-- **The totals split by range**: `S + A` is the square-clique sum `∑_p λ^ex_p(1) q_p^{2a}`, the
class-three block sum `∑_𝔅 (s_𝔅 + a_𝔅)` and the tail bounds `S_tail + A_tail`. -/
theorem comparisonLawTarget_SA (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf)
    (I : ComparisonInputs blockOf hW spec hC In) :
    (comparisonLawTarget blockOf hW spec hC In I).S +
        (comparisonLawTarget blockOf hW spec hC In I).A =
      ∑ q, I.cliquePrice q + ∑ b, I.blockPrice b + (I.St + I.At) := by
  rw [comparisonLawTarget_S, comparisonLawTarget_A, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hq : ∀ q, (I.pre (.inl q)).sprice
      (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q)) +
      (I.pre (.inl q)).aprice
        (MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q)) = I.cliquePrice q := by
    intro q
    unfold ComparisonInputs.pre
    rw [AtomComparison.congrLam_sprice, AtomComparison.congrLam_aprice,
      DeletionInputs.toAtom_sprice, DeletionInputs.toAtom_aprice, add_zero]
    rfl
  have hq' := Finset.sum_congr (s₁ := (univ : Finset PrefixCoord)) rfl fun q _ => hq q
  rw [sum_add_distrib] at hq'
  unfold ComparisonInputs.blockPrice
  rw [sum_add_distrib]
  change _ = _ + (∑ b, (I.pre (.inr b)).sprice _ + ∑ b, (I.pre (.inr b)).aprice _) + _
  linarith

end Sarkozy.ComparisonLawPaper
