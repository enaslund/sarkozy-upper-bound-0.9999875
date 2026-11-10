module

public import Sarkozy.FirstStagePaper.SharpRecord
public import Sarkozy.MainTarget.Bridge

@[expose] public section

/-!
# (CP2) for the paper's construction (`def:cp2`, `def:record:frame`)

The first stage of Theorem C on the paper's block atoms (`paperAtomMap blockOf`: each square-clique
prime its own atom, each class-three prime to its block), with V2's reference
`PartVLaws.v2Reference blockOf hW spec hC` (`def:cp1`, the paper's block laws of `spec`):

* the first-stage atoms are the **middle blocks** (a block whose specification is one of the three
  middle variants); there the data are V3's middle frame (`middleStage`):
  `ρ = μ - F_fold + E_add + G`
  (`lem:middle-polarization`), and the two tagged differences of `δ_E`
  (`lem:record:one-stage-folded-e`, `def:record:frame`(e));
* the square-clique atoms and the upper blocks carry the trivial data (`ρ = μ`, no records), as do
  the tail atoms.

`classThree_blockPrimes`: the primes of every class-three block are class-three primes `≥ Q₃`
(`p ≡ 3 (4)`, `p ≥ 19951586 > 2^{24}`), so V3's `ClassThreeBlock` holds and the block replacement
law is defined, for every block of every partition.

**The inputs** (`FirstStageInputs`), per block `b`: the piece start `X b` and the least prime
`bmin b`, with `2^{24} ≤ X b ≤ bmin b ≤` every prime of the block. They are data, not open
statements: `FirstStageInputs.default` (`X = 2^{24}`, `bmin = Q₃` for every block) satisfies them
for
every partition; the paper's choice (the piece start and the least prime) gives the sharp constant
`k_new(X) b^{-1/2}` of the ledger. The sharp bound of each block,
**`lem:record:one-stage-folded-e`(e)**, is proved (`blockSharp_of_block`, from (d)).

**`firstStagePaper`** is `TheoremCBlock.FirstStage` at any price exponent `a` and prefix prices
`selPre`; at `a_T` with `paperSelAt` it has exactly the type of T1's field `V2BlockDataTarget.FS`
(`firstStageTarget`). Its totals are `P = ∑_β p_β`, `d_j = ∑_β d_{β,j}`, `v_j = ∑_β v_{β,j}` over
the
middle blocks (`firstStagePaper_P`, …).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.FirstStagePaper

open Sarkozy.TheoremC Sarkozy.PartVRecords Sarkozy.PartV Sarkozy.Labellings Sarkozy.FiveType
  Sarkozy.RecordExpansion Sarkozy.PartVLaws Sarkozy.CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-! ## The primes of a class-three block -/

omit [Fintype B] [DecidableEq B] in
/-- The primes of a class-three block are class-three primes at least `Q₃`. -/
theorem blockPrimes_mod_ge (b : B) (j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}) :
    blockPrimes blockOf b j % 4 = 3 ∧ PartV.Q3 ≤ blockPrimes blockOf b j := by
  have hj : j.1.1 % 4 ≠ 1 := paperAtomMap_inr blockOf j.2
  have hm : blockPrimes blockOf b j = j.1.1 := paperM0_cls3 hj
  have hmem := j.1.2
  unfold paperFixedPrimes at hmem
  rw [mem_filter] at hmem
  rw [hm]
  rcases hmem.2.2 with h1 | h3
  · exact absurd h1 hj
  · exact h3

omit [Fintype B] [DecidableEq B] in
/-- **Every class-three block is a block of class-three primes `≥ 7`** (V3's `ClassThreeBlock`). -/
theorem classThree_blockPrimes (b : B) : ClassThreeBlock (blockPrimes blockOf b) where
  mod4 j := (blockPrimes_mod_ge b j).1
  ge7 j := le_trans (by norm_num [PartV.Q3]) (blockPrimes_mod_ge b j).2

/-- The block constant is nonnegative. -/
theorem blockConst_nonneg {X : ℝ} (hX : 2 ^ 24 ≤ X) (b : ℝ) : 0 ≤ blockConst X b := by
  have hX0 : 0 < X := by linarith
  unfold blockConst
  exact mul_nonneg (le_trans zero_le_one (one_le_knew (by positivity)
    (by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith) (by positivity))) (by positivity)

/-! ## The named inputs -/

variable (blockOf) in
/-- **The per-block constants of the first stage** (`lem:record:one-stage-folded-e`(d)): the piece
start `X` and the least prime `bmin` of each block, with `2^{24} ≤ X ≤ bmin ≤` every prime of the
block. Data (`default` is a valid choice for every partition). -/
structure FirstStageInputs where
  /-- The piece start `X` of each block. Data. -/
  X : B → ℝ
  /-- The least prime `b` of each block (any lower bound of its primes). Data. -/
  bmin : B → ℝ
  hX : ∀ b, 2 ^ 24 ≤ X b
  hXb : ∀ b, X b ≤ bmin b
  hbp : ∀ b j, bmin b ≤ (blockPrimes blockOf b j : ℝ)

variable (blockOf) in
/-- **A valid choice for every partition**: `X = 2^{24}` and `bmin = Q₃` (every class-three prime is
at least `Q₃ = 19951586 > 2^{24}`). -/
noncomputable def FirstStageInputs.default : FirstStageInputs blockOf where
  X _ := 2 ^ 24
  bmin _ := PartV.Q3
  hX _ := le_refl _
  hXb _ := by norm_num [PartV.Q3]
  hbp b j := by exact_mod_cast (blockPrimes_mod_ge b j).2

omit [Fintype B] in
/-- **`lem:record:one-stage-folded-e`(e) on every middle block of the paper's partition**, with the
constant `k_new(X) b^{-1/2}`: `blockSharp_of_block` with V3's `ClassThreeBlock`
(`classThree_blockPrimes`). -/
theorem FirstStageInputs.sharp (In : FirstStageInputs blockOf) (b : B)
    (hne : MiddleNonempty (blockPrimes blockOf b)) :
    BlockSharp (blockPrimes blockOf b) hne (classThree_blockPrimes b)
      (blockConst (In.X b) (In.bmin b)) :=
  blockSharp_of_block (blockPrimes blockOf b) (classThree_blockPrimes b) hne (In.hX b) (In.hXb b)
    (In.hbp b)

/-! ## The atom data -/

/-- **The first-stage data of one class-three block** from its specification: the middle frame on
a middle block, the trivial data on an upper block. -/
noncomputable def specStage (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B} :
    (S : PaperBlockSpec blockOf b) →
      AtomStage (signedIntegral (S.toAtom hW).law.weight) (Fin 2) tagCut (firstChamberCut 0)
  | .upper _ => AtomStage.trivial _ _ _ _
  | .middleUniform M => middleStage (blockPrimes blockOf b) M.hne
      (uniformRoot (blockPrimes blockOf b) M.hne) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne)
  | .middleIndividual M => middleStage (blockPrimes blockOf b) M.hne
      (individualBlockRoot (blockPrimes blockOf b) M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne)
  | .middleCoherent M => middleStage (blockPrimes blockOf b) M.hne
      (coherentBlockRoot (blockPrimes blockOf b) M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne)

variable (blockOf) in
/-- **The first-stage data of every prefix atom**: trivial at the square-clique atoms, `specStage`
at the class-three blocks. -/
noncomputable def paperStage (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) :
    ∀ β : PaperAtom B, AtomStage (signedIntegral ((v2Reference blockOf hW spec hC).μ₀ β).weight)
      (Fin 2) tagCut (firstChamberCut 0)
  | .inl _ => AtomStage.trivial _ _ _ _
  | .inr b => specStage hW In (spec b)

/-! ### The first-stage atoms are the middle blocks -/

omit [Fintype B] in
theorem paperStage_first_prefix (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (q : PrefixCoord) :
    (paperStage blockOf hW spec hC In (.inl q)).first = false := rfl

omit [Fintype B] in
theorem specStage_first_upper (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (U : UpperBlockInputs blockOf b) : (specStage hW In (.upper U)).first = false := rfl

omit [Fintype B] in
theorem specStage_first_middleUniform (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) : (specStage hW In (.middleUniform M)).first = true := rfl

omit [Fintype B] in
theorem specStage_first_middleIndividual (hW : Target.Weil) (In : FirstStageInputs blockOf)
    {b : B} (M : MiddleIndividualInputs blockOf b) :
    (specStage hW In (.middleIndividual M)).first = true := rfl

omit [Fintype B] in
theorem specStage_first_middleCoherent (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleCoherentInputs blockOf b) : (specStage hW In (.middleCoherent M)).first = true := rfl

/-! ## The first stage -/

variable (blockOf) in
/-- **(CP2) for the paper's construction** (`def:cp2`), at the price exponent `a` with the prefix
prices `selPre`: the first-stage atoms are the middle blocks, with V3's frame
(`lem:middle-polarization`, `lem:record:one-stage-folded-e`, `def:record:frame`); two tags with the
cuts `ϑ₁, ϑ₂`; `ϑ₀ = firstChamberCut 0`. -/
noncomputable def firstStagePaper (a : ℝ) (selPre : PaperAtom B → ℝ) (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) :
    TheoremCBlock.FirstStage a paperM0 (paperAtomMap blockOf) paperTail selPre
      (v2Reference blockOf hW spec hC) :=
  firstStageOfAtoms a paperM0 (paperAtomMap blockOf) paperTail selPre
    (v2Reference blockOf hW spec hC) (Fin 2) tagCut tagCut_family (firstChamberCut 0)
    firstChamberCut_zero_family (paperStage blockOf hW spec hC In)

variable (blockOf) in
/-- **(CP2) at the target `a_T`**, with the paper's prices `paperSelAt · a_T`: exactly the type of
T1's field `MainTarget.V2BlockDataTarget.FS`. Irreducible, as T1's `paperSelAt` (a structure field
over it otherwise sends the unifier into the `2^{512}`-range of `P₄`); `firstStageTarget_eq`
unfolds it. -/
@[irreducible] noncomputable def firstStageTarget (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) :
    TheoremCBlock.FirstStage TargetLedger.targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay)
      (v2Reference blockOf hW spec hC) :=
  firstStagePaper blockOf _ _ hW spec hC In

theorem firstStageTarget_eq (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) :
    firstStageTarget blockOf hW spec hC In =
      firstStagePaper blockOf TargetLedger.targetDecay
        (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay) hW spec hC In := by
  unfold firstStageTarget
  rfl

/-- The total variation price of the paper's first stage: the sum over the prefix atoms. -/
theorem firstStagePaper_P (a : ℝ) (selPre : PaperAtom B → ℝ) (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) :
    (firstStagePaper blockOf a selPre hW spec hC In).P =
      ∑ β, (paperStage blockOf hW spec hC In β).pvar (selPre β) := rfl

theorem firstStagePaper_dT (a : ℝ) (selPre : PaperAtom B → ℝ) (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) (j : Fin 2) :
    (firstStagePaper blockOf a selPre hW spec hC In).dT j =
      ∑ β, (paperStage blockOf hW spec hC In β).dTag (selPre β) j := rfl

theorem firstStagePaper_vT (a : ℝ) (selPre : PaperAtom B → ℝ) (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) (j : Fin 2) :
    (firstStagePaper blockOf a selPre hW spec hC In).vT j =
      ∑ β, (paperStage blockOf hW spec hC In β).vTag (selPre β) j := rfl

/-- **Non-vacuity of the inputs**: the first stage at `a_T` exists for every specification of the
blocks and every tail input, with the default constants. -/
noncomputable example (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) :
    TheoremCBlock.FirstStage TargetLedger.targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay)
      (v2Reference blockOf hW spec hC) :=
  firstStageTarget blockOf hW spec hC (FirstStageInputs.default blockOf)

end Sarkozy.FirstStagePaper
