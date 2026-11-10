module

public import Sarkozy.GramBracketPaper.MiddleGram
public import Sarkozy.FirstStagePaper.Paper

@[expose] public section

/-!
# (CP3) for the paper's construction (`def:cp3`, `lem:record:gram`)

The Gram bracket of Theorem C on the paper's block atoms, over A1's first stage
`firstStagePaper` / `firstStageTarget` (`Sarkozy.FirstStagePaper.Paper`), with V2's reference
`v2Reference blockOf hW spec hC`:

* at a **middle block**: V3's bracket of `lem:record:gram` (`middleGram`): `Ñ₀ - μ = E_add + G + H`
  (divided by `P(r)`), six positive reserved-diagonal records, and `(Ñ λ; λ Ñ) ⪰_ι 0`;
* at a **square-clique atom**, an **upper block** and a **tail atom**: `Ñ = μ`
  (`AtomGram.ofTrivial`),
  from (R2) of the reference at the family cut `ι` (`rp₀`, `rpp`).

**The input** (`GramInputs`), per middle block: the protection inequality `v_D ≥ 2 k_D w_D`
(`eq:protection`), a check on the recorded weights of the piece (`rem:middle-weights`,
`cert:record:frame-data`). It is the only input the paper lists for (CP3) besides
`lem:record:gram` (`tab:hypotheses`, row (CP3)). Every other hypothesis of
`lem:record:gram` is discharged:
* the layer caps and `v_𝔱 ≥ k_𝔱 w_𝔱` from V2's block specification (`hcap`, the last line of
  `hW : MiddleWeights.Completes`);
* the sign `(f₁ + h₁) r ≥ 0` of the polarization coefficient from the one-layer rows `hrows₁` of
  the specification (`polarCoef_nonneg`);
* the disjoint-triple bound from M2 (`Misc.matchingReservedBound_block`);
* `3 < bmin`, `bmin ≤ p` from A1's `FirstStageInputs`;
* the symmetry of `λ` at `ι` from (R2) of the reference at `ι` (no layer-swap input, so the
  coherent root is covered).

**`gramBracketPaper`** is `TheoremCBlock.GramBracket` at any price exponent `a` and prefix prices
`selPre` over `firstStagePaper`; **`gramBracketTarget`** at `a_T` has exactly the type of A1's field
`A1BlockDataTarget.GB`. Its total is `U₀ = ∑_β u_β` over the prefix atoms
(`gramBracketTarget_U₀`), with `u_β = specUprice` on the middle blocks (`paperGram_uprice`, the
identity of `lem:record:middle-prices`) and `0` elsewhere.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.GramBracketPaper

open Sarkozy.TheoremC Sarkozy.PartVRecords Sarkozy.PartV Sarkozy.Labellings Sarkozy.FiveType
  Sarkozy.RecordExpansion Sarkozy.PartVLaws Sarkozy.CancellationSteps Sarkozy.FirstStagePaper

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-! ## The gates of a block -/

/-- **The protection inequality of a block** (`eq:protection`, `lem:front12:reference`(iv)):
`v_D ≥ 2 k_D w_D` for the weights and inputs of a middle block; nothing for an upper block. -/
def specProtects {b : B} : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => M.W.Protects M.I
  | .middleIndividual M => M.W.Protects M.I
  | .middleCoherent M => M.W.Protects M.I

variable (blockOf) in
/-- **The input of the Gram bracket** (`def:cp3` for the paper's construction): the one gate of
`lem:record:gram`(ii) that V2's block specification does not contain, the protection inequality on
every middle block. It is a check on the recorded weights of the piece; every other hypothesis of
`lem:record:gram` is discharged (see the module docstring). 1 field. -/
structure GramInputs (spec : ∀ b, PaperBlockSpec blockOf b) : Prop where
  /-- **The protection inequality** `v_D ≥ 2 k_D w_D` (`eq:protection`, the fourteenth inequality
  of `lem:front12:reference`(iv)) on every middle block. *Open* (rational check of the recorded
  weights, `rem:middle-weights`, `cert:record:frame-data`). -/
  protects : ∀ b, specProtects (spec b)

omit [Fintype B] [DecidableEq B] in
/-- `7 ≤ bmin` for the constants of A1's first stage (`bmin ≥ X ≥ 2²⁴`). -/
theorem seven_le_bmin (In : FirstStageInputs blockOf) (b : B) :
    (7 : ℝ) ≤ In.bmin b := by
  have h1 := In.hX b
  have h2 := In.hXb b
  norm_num at h1
  linarith

/-! ## The atom data -/

/-- **The (CP3) data of one class-three block** from its specification, over A1's `specStage`: V3's
bracket (`middleGram`) on a middle block, `Ñ = μ` on an upper block. `hμ` is (R2) of the block law
at `ι`. -/
noncomputable def specGram (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B} :
    (S : PaperBlockSpec blockOf b) → specProtects S →
      reservedCut.Positive (signedIntegral (S.toAtom hW).law.weight) →
      AtomGram (specStage hW In S)
  | .upper _, _, hμ => AtomGram.ofTrivial _ hμ
  | .middleUniform M, hP, hμ => middleGram (blockPrimes blockOf b) M.hne
      (uniformRoot (blockPrimes blockOf b) M.hne) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP
  | .middleIndividual M, hP, hμ => middleGram (blockPrimes blockOf b) M.hne
      (individualBlockRoot (blockPrimes blockOf b) M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP
  | .middleCoherent M, hP, hμ => middleGram (blockPrimes blockOf b) M.hne
      (coherentBlockRoot (blockPrimes blockOf b) M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP

/-- `ι` is a cut of the family `𝔉` (`def:cp0`(a)). -/
theorem reservedCut_family : IsFamilyCut reservedCut := Or.inr (Or.inr rfl)

variable (blockOf) in
/-- **The (CP3) data of every prefix atom**: `Ñ = μ` at the square-clique atoms, `specGram` at the
class-three blocks, with `μ ⪰_ι 0` from (R2) of V2's reference (`rp₀` at the family cut `ι`). -/
noncomputable def paperGram (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec) :
    ∀ β : PaperAtom B, AtomGram (paperStage blockOf hW spec hC In β)
  | .inl q => AtomGram.ofTrivial _ ((v2Reference blockOf hW spec hC).rp₀ (.inl q) reservedCut
      reservedCut_family)
  | .inr b => specGram hW In (spec b) (Gi.protects b)
      ((v2Reference blockOf hW spec hC).rp₀ (.inr b) reservedCut reservedCut_family)

/-- **`μ_p ⪰_ι 0` at every tail atom**: (R2) of V2's reference (`rpp` at the family cut `ι`); the
tail moduli are primes (`paperTail_prime`). -/
theorem paperTail_positive (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (L : ℕ) (j : PaperJt L) :
    reservedCut.Positive ((v2Reference blockOf hW spec hC).law paperTail L (.inr j)) :=
  (v2Reference blockOf hW spec hC).rpp (paperTail L j) (paperTail_prime j) reservedCut
    reservedCut_family

/-! ## The Gram bracket -/

variable (blockOf) in
/-- **(CP3) for the paper's construction** (`def:cp3`, `lem:record:gram`), at the price exponent
`a` with the prefix prices `selPre`, over A1's first stage `firstStagePaper`: V3's bracket on the
middle blocks, `Ñ = μ` elsewhere; `U₀ = ∑_β u_β`. -/
noncomputable def gramBracketPaper (a : ℝ) (selPre : PaperAtom B → ℝ) (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec) :
    TheoremCBlock.GramBracket a paperM0 (paperAtomMap blockOf) paperTail selPre
      (firstStagePaper blockOf a selPre hW spec hC In) :=
  gramBracketOfAtoms a paperM0 (paperAtomMap blockOf) paperTail selPre
    (v2Reference blockOf hW spec hC) (Fin 2) tagCut tagCut_family (firstChamberCut 0)
    firstChamberCut_zero_family (paperStage blockOf hW spec hC In)
    (paperGram blockOf hW spec hC In Gi) (paperTail_positive hW spec hC)

variable (blockOf) in
/-- **(CP3) at the target `a_T`**, with the paper's prices `paperSelAt · a_T`, over A1's
`firstStageTarget`: exactly the type of A1's field `A1BlockDataTarget.GB`. Irreducible, as
`firstStageTarget`; `gramBracketTarget_U₀` gives its total. -/
@[irreducible] noncomputable def gramBracketTarget (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec) :
    TheoremCBlock.GramBracket TargetLedger.targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay)
      (firstStageTarget blockOf hW spec hC In) := by
  with_unfolding_all exact gramBracketPaper blockOf _ _ hW spec hC In Gi

/-- The total `U₀` of the paper's bracket: the sum of the prices of the prefix atoms. -/
theorem gramBracketPaper_U₀ (a : ℝ) (selPre : PaperAtom B → ℝ) (hW : Target.Weil)
    (spec : ∀ b, PaperBlockSpec blockOf b) (hC : TailInputsCorr PartV.P4)
    (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec) :
    (gramBracketPaper blockOf a selPre hW spec hC In Gi).U₀ =
      ∑ β, (paperGram blockOf hW spec hC In Gi β).uprice (selPre β) := rfl

/-- **The total `U₀` of the bracket at `a_T`**: `∑_β u_β (paperSelAt β)`. -/
theorem gramBracketTarget_U₀ (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec) :
    (gramBracketTarget blockOf hW spec hC In Gi).U₀ =
      ∑ β, (paperGram blockOf hW spec hC In Gi β).uprice
        (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay β) := by
  unfold gramBracketTarget
  rfl

/-! ## The prices `u_β` (`lem:record:middle-prices`) -/

/-- **The price `u_𝔅` of a block** from its specification (`lem:record:middle-prices`, `Ñ₀ - μ`):
`P(r)⁻¹ (2 v_D r² + 2 v_D (f₁ + h₁) r³ + 12 w_S r/(bmin - 3)) q_𝔅^{2a}` on a middle block, `0` on an
upper block. -/
noncomputable def specUprice (In : FirstStageInputs blockOf) {b : B} :
    PaperBlockSpec blockOf b → ℝ → ℝ
  | .upper _, _ => 0
  | .middleUniform M, sel => (midPoly M.W M.r)⁻¹ * (2 * M.W.v .D * M.r ^ 2 +
      2 * M.W.v .D * (M.I.f₁ + M.I.h₁) * M.r ^ 3 + 12 * M.W.w .S * M.r / (In.bmin b - 3)) * sel
  | .middleIndividual M, sel => (midPoly M.W M.r)⁻¹ * (2 * M.W.v .D * M.r ^ 2 +
      2 * M.W.v .D * (M.I.f₁ + M.I.h₁) * M.r ^ 3 + 12 * M.W.w .S * M.r / (In.bmin b - 3)) * sel
  | .middleCoherent M, sel => (midPoly M.W M.r)⁻¹ * (2 * M.W.v .D * M.r ^ 2 +
      2 * M.W.v .D * (M.I.f₁ + M.I.h₁) * M.r ^ 3 + 12 * M.W.w .S * M.r / (In.bmin b - 3)) * sel

omit [Fintype B] in
/-- **The price of a block's bracket data** is `specUprice` (`middleGram_uprice` on the middle
blocks; no record on an upper block). -/
theorem specGram_uprice (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (S : PaperBlockSpec blockOf b) (hP : specProtects S)
    (hμ : reservedCut.Positive (signedIntegral (S.toAtom hW).law.weight)) (sel : ℝ) :
    (specGram hW In S hP hμ).uprice sel = specUprice In S sel := by
  cases S with
  | upper U => exact AtomGram.ofTrivial_uprice _ hμ sel
  | middleUniform M =>
    exact middleGram_uprice (blockPrimes blockOf b) M.hne
      (uniformRoot (blockPrimes blockOf b) M.hne) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP sel
  | middleIndividual M =>
    exact middleGram_uprice (blockPrimes blockOf b) M.hne
      (individualBlockRoot (blockPrimes blockOf b) M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP sel
  | middleCoherent M =>
    exact middleGram_uprice (blockPrimes blockOf b) M.hne
      (coherentBlockRoot (blockPrimes blockOf b) M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP sel

omit [Fintype B] in
/-- **The prices of the prefix atoms**: `0` at a square-clique atom, `specUprice` at a block. -/
theorem paperGram_uprice (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec)
    (β : PaperAtom B) (sel : ℝ) :
    (paperGram blockOf hW spec hC In Gi β).uprice sel =
      Sum.elim (fun _ => 0) (fun b => specUprice In (spec b) sel) β := by
  cases β with
  | inl q =>
    exact AtomGram.ofTrivial_uprice _
      ((v2Reference blockOf hW spec hC).rp₀ (.inl q) reservedCut reservedCut_family) sel
  | inr b =>
    exact specGram_uprice hW In (spec b) (Gi.protects b)
      ((v2Reference blockOf hW spec hC).rp₀ (.inr b) reservedCut reservedCut_family) sel

/-- **`U₀` at `a_T` as an explicit sum over the class-three blocks** (`lem:record:middle-prices`):
`U₀ = ∑_𝔅 specUprice(𝔅) (paperSelAt 𝔅)`, the sum of
`P(r)⁻¹ (2 v_D r² + 2 v_D (f₁ + h₁) r³ + 12 w_S r/(bmin - 3)) q_𝔅^{2a}` over the middle blocks. -/
theorem gramBracketTarget_U₀_eq (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec) :
    (gramBracketTarget blockOf hW spec hC In Gi).U₀ =
      ∑ b, specUprice In (spec b)
        (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay (.inr b)) := by
  rw [gramBracketTarget_U₀, Fintype.sum_sum_type]
  simp only [paperGram_uprice, Sum.elim_inl, Sum.elim_inr, sum_const_zero, zero_add]

/-! ## The price bound of `lem:record:middle-prices` -/

/-- **The scale of a block is `r = bmin^{-1/2}`** (`lem:record:middle-prices`: `r = b^{-1/2}` for
the least prime `b`): `r² bmin = 1` on a middle block; nothing on an upper block. -/
def specScale (In : FirstStageInputs blockOf) {b : B} : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => M.r ^ 2 * In.bmin b = 1
  | .middleIndividual M => M.r ^ 2 * In.bmin b = 1
  | .middleCoherent M => M.r ^ 2 * In.bmin b = 1

/-- **The price bound of a block** (`lem:record:middle-prices`, `Ñ₀ - μ`), with the coefficient
evaluated at the piece start `X`:
`(2 v_D r² + (2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X)) r³) q_𝔅^{2a}` on a middle block, `0` on an upper
block. -/
noncomputable def specUbound (In : FirstStageInputs blockOf) {b : B} :
    PaperBlockSpec blockOf b → ℝ → ℝ
  | .upper _, _ => 0
  | .middleUniform M, sel => (2 * M.W.v .D * M.r ^ 2 + (2 * M.W.v .D * (M.I.f₁ + M.I.h₁) +
      12 * M.W.w .S / (1 - 3 / In.X b)) * M.r ^ 3) * sel
  | .middleIndividual M, sel => (2 * M.W.v .D * M.r ^ 2 + (2 * M.W.v .D * (M.I.f₁ + M.I.h₁) +
      12 * M.W.w .S / (1 - 3 / In.X b)) * M.r ^ 3) * sel
  | .middleCoherent M, sel => (2 * M.W.v .D * M.r ^ 2 + (2 * M.W.v .D * (M.I.f₁ + M.I.h₁) +
      12 * M.W.w .S / (1 - 3 / In.X b)) * M.r ^ 3) * sel

omit [Fintype B] [DecidableEq B] in
/-- `3 < X` for the piece starts of A1's first stage (`X ≥ 2²⁴`). -/
theorem three_lt_X (In : FirstStageInputs blockOf) (b : B) : (3 : ℝ) < In.X b := by
  have h1 := In.hX b
  norm_num at h1
  linarith

omit [Fintype B] in
/-- **`lem:record:middle-prices` for a block's bracket data**: when `r² bmin = 1`, the price is at
most `specUbound` (V3's `uprice_le` with `X ≤ bmin` from A1's `FirstStageInputs`). -/
theorem specGram_uprice_le (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (S : PaperBlockSpec blockOf b) (hP : specProtects S)
    (hμ : reservedCut.Positive (signedIntegral (S.toAtom hW).law.weight))
    (hsc : specScale In S) {sel : ℝ} (hsel : 0 ≤ sel) :
    (specGram hW In S hP hμ).uprice sel ≤ specUbound In S sel := by
  cases S with
  | upper U => exact (AtomGram.ofTrivial_uprice _ hμ sel).le
  | middleUniform M =>
    exact middleGram_uprice_le (blockPrimes blockOf b) M.hne
      (uniformRoot (blockPrimes blockOf b) M.hne) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP hsc
      (three_lt_X In b) (In.hXb b) hsel
  | middleIndividual M =>
    exact middleGram_uprice_le (blockPrimes blockOf b) M.hne
      (individualBlockRoot (blockPrimes blockOf b) M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP hsc
      (three_lt_X In b) (In.hXb b) hsel
  | middleCoherent M =>
    exact middleGram_uprice_le (blockPrimes blockOf b) M.hne
      (coherentBlockRoot (blockPrimes blockOf b) M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
      (In.sharp b M.hne) hμ (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP hsc
      (three_lt_X In b) (In.hXb b) hsel

/-- **`U₀` at `a_T` is at most the sum of the block bounds of `lem:record:middle-prices`**, when
every middle block has the scale `r = bmin^{-1/2}`: `U₀ ≤ ∑_𝔅 (2 v_D r² + (2 v_D (f₁ + h₁) +
12 w_S/(1 - 3/X)) r³) q_𝔅^{2a}`, the sum the paper groups into the block charges `b₂`, `b₃` of the
pieces (`subsec:middle-frame-prices`). -/
theorem gramBracketTarget_U₀_le (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf) (Gi : GramInputs blockOf spec)
    (hsc : ∀ b, specScale In (spec b)) :
    (gramBracketTarget blockOf hW spec hC In Gi).U₀ ≤
      ∑ b, specUbound In (spec b)
        (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay (.inr b)) := by
  rw [gramBracketTarget_U₀_eq]
  refine sum_le_sum fun b _ => ?_
  have hsel : 0 ≤ MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay (.inr b) :=
    le_trans zero_le_one (MainTarget.one_le_paperSelAt (paperAtomMap blockOf)
      TargetLedger.targetDecay_nonneg _)
  rw [← specGram_uprice hW In (spec b) (Gi.protects b)
    ((v2Reference blockOf hW spec hC).rp₀ (.inr b) reservedCut reservedCut_family)]
  exact specGram_uprice_le hW In (spec b) (Gi.protects b)
    ((v2Reference blockOf hW spec hC).rp₀ (.inr b) reservedCut reservedCut_family) (hsc b) hsel

/-! ## Non-vacuity -/

/-- **Non-vacuity of the inputs**: the bracket at `a_T` exists for every specification of the
blocks, every tail input, the default first-stage constants and every `GramInputs`. -/
noncomputable example (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (Gi : GramInputs blockOf spec) :
    TheoremCBlock.GramBracket TargetLedger.targetDecay paperM0 (paperAtomMap blockOf) paperTail
      (MainTarget.paperSelAt (paperAtomMap blockOf) TargetLedger.targetDecay)
      (firstStageTarget blockOf hW spec hC (FirstStageInputs.default blockOf)) :=
  gramBracketTarget blockOf hW spec hC _ Gi

/-- Toy weights of a middle piece in the paper's design (`rem:middle-weights`): `w_D = w_S = d = 1`,
`v_L = k_L = 1`, and `v_D = v_S = 2 k_D w_D = 2`, so that the protection holds with equality. -/
def toyWeights : MiddleWeights where
  w t := match t with
    | .L => 1 | .D => 1 | .S => 1 | .R => 0 | .C => 0
  v t := match t with
    | .L => 1 | .D => 2 | .S => 2 | .R => 0 | .C => 0
  w_L := rfl
  w_nonneg t := by cases t <;> norm_num
  v_nonneg t := by cases t <;> norm_num

/-- Toy inputs: root cap `d = 1`, layer caps `k = 1`, the other constants `0`. -/
def toyInputs : MiddleInputs where
  d := 1
  d₁ := 0
  f₁ := 0
  f₂ := 0
  h₁ := 0
  h₂ := 0
  k _ := 1

/-- **The gate is consistent with the thirteen inequalities**: the toy weights satisfy `Completes`
(the specification's gate) and the protection, which binds (`v_D = 2 k_D w_D`), as in the paper's
design. -/
example : toyWeights.Completes toyInputs ∧ toyWeights.Protects toyInputs := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t => ?_⟩, ?_⟩ <;>
    first
    | (cases t <;> norm_num [toyWeights, toyInputs])
    | norm_num [toyWeights, toyInputs, MiddleWeights.Protects]

end Sarkozy.GramBracketPaper
