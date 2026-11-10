module

public import Sarkozy.MiddleComparison.Block
public import Sarkozy.ComparisonLawPaper.Paper

@[expose] public section

/-!
# The middle-block (CP4) atoms of the paper's construction, and B2's `ComparisonInputs`

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`, `lem:middle-comparison-prices`;
`paper/sections/09_comparison_theorem.tex`, `def:cp4`.

On a middle block of the paper's partition with specification `M` (V2's `MiddleUniformInputs`,
`MiddleIndividualInputs` or `MiddleCoherentInputs`), A1's first stage is the frame's `λ`
(`middleStage_lam`). This file builds B2's open middle-block input `BlockInputs hW In S` from
`Replacements` on that frame:

* `frameU`, `frameI`, `frameC`: V3's frame of the block with the uniform, individual-square or
  coherent root, as in A1's `specStage`; `factsU`, `factsI`, `factsC`: its `FrameFacts`
  (`middleFrame_facts`, with `uniformRoot_supported`, `individualRoot_supported`,
  `coherentRoot_supported`); `lamU`, `lamI`, `lamC`: `λ` of the frame is A1's `specLam`.
* **`SpecInputs hW In S`**: by specification, `UpperAtomInputs` on an upper block (unchanged), and
  `Replacements` on a middle block (any root). **`SpecInputs.toBlockInputs`**: B2's `BlockInputs`,
  through `Replacements.toAtom`, the weakening of the acceptance relation
  (`paperPrefixAccepted_inr_iff`) and `congrLam`.
* **`comparisonInputsOf`**: B2's `ComparisonInputs` from `SpecInputs` at every block and B2's
  clique and tail inputs. `blockAtom_middle*`: the atom of a middle block is
  `Replacements.toAtom`, with the same prices (`rfl`).

Under ALLp (`BlockSpecPaper.paperSpec`) only the uniform root (pieces `2³⁰`–`2³⁴`, `2⁴⁵` and below
`2³⁰`) and the individual-square root (`2³⁶`, `2⁴⁰`) occur; the coherent case is included because
V2's specification type has it.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-! ## The frames of the three roots -/

/-- V3's frame of a middle block with the uniform root (A1's `specStage`). -/
noncomputable abbrev frameU (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) : FrameData (BlockLabel (blockPrimes blockOf b)) :=
  middleFrame (blockPrimes blockOf b) M.hne (uniformRoot (blockPrimes blockOf b) M.hne) M.W M.I
    M.hr (In.bmin b) (classThree_blockPrimes b)

/-- V3's frame of a middle block with the individual-square root. -/
noncomputable abbrev frameI (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleIndividualInputs blockOf b) : FrameData (BlockLabel (blockPrimes blockOf b)) :=
  middleFrame (blockPrimes blockOf b) M.hne
    (individualBlockRoot (blockPrimes blockOf b) M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
    (classThree_blockPrimes b)

/-- V3's frame of a middle block with the coherent root. -/
noncomputable abbrev frameC (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleCoherentInputs blockOf b) : FrameData (BlockLabel (blockPrimes blockOf b)) :=
  middleFrame (blockPrimes blockOf b) M.hne
    (coherentBlockRoot (blockPrimes blockOf b) M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
    (classThree_blockPrimes b)

omit [Fintype B] in
theorem factsU (In : FirstStageInputs blockOf) {b : B} (M : MiddleUniformInputs blockOf b) :
    FrameFacts (frameU In M) (blockSquareAccepted (blockPrimes blockOf b))
      MainAnchor.paperQueries :=
  middleFrame_facts _ M.hne _ M.W M.I M.hr _ _ (uniformRoot_supported _ M.hne)
    (uniformRoot_vertex_uniform _ M.hne)

omit [Fintype B] in
theorem factsI (In : FirstStageInputs blockOf) {b : B} (M : MiddleIndividualInputs blockOf b) :
    FrameFacts (frameI In M) (blockSquareAccepted (blockPrimes blockOf b))
      MainAnchor.paperQueries :=
  middleFrame_facts _ M.hne _ M.W M.I M.hr _ _ (individualRoot_supported _ M.u M.hne.L2)
    (individualBlockRoot_vertex_uniform _ M.u M.hne.L2)

omit [Fintype B] in
theorem factsC (In : FirstStageInputs blockOf) {b : B} (M : MiddleCoherentInputs blockOf b) :
    FrameFacts (frameC In M) (blockSquareAccepted (blockPrimes blockOf b))
      MainAnchor.paperQueries :=
  middleFrame_facts _ M.hne _ M.W M.I M.hr _ _ (coherentRoot_supported _ M.D M.u M.hη M.hne.L2)
    (coherentBlockRoot_vertex_uniform _ M.D M.u M.hη M.hne.L2)

omit [Fintype B] in
/-- The frame's `λ` is A1's first-stage law of the block (uniform root). -/
theorem lamU (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) : (frameU In M).lam = specLam hW In (.middleUniform M) :=
  (middleStage_lam (blockPrimes blockOf b) M.hne (uniformRoot (blockPrimes blockOf b) M.hne) M.W
    M.I M.hr (In.bmin b) (classThree_blockPrimes b) M.hrows₁
    (blockConst_nonneg (In.hX b) (In.bmin b)) (In.sharp b M.hne)).symm

omit [Fintype B] in
/-- The frame's `λ` is A1's first-stage law of the block (individual-square root). -/
theorem lamI (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleIndividualInputs blockOf b) :
    (frameI In M).lam = specLam hW In (.middleIndividual M) :=
  (middleStage_lam (blockPrimes blockOf b) M.hne
    (individualBlockRoot (blockPrimes blockOf b) M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
    (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
    (In.sharp b M.hne)).symm

omit [Fintype B] in
/-- The frame's `λ` is A1's first-stage law of the block (coherent root). -/
theorem lamC (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleCoherentInputs blockOf b) :
    (frameC In M).lam = specLam hW In (.middleCoherent M) :=
  (middleStage_lam (blockPrimes blockOf b) M.hne
    (coherentBlockRoot (blockPrimes blockOf b) M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
    (classThree_blockPrimes b) M.hrows₁ (blockConst_nonneg (In.hX b) (In.bmin b))
    (In.sharp b M.hne)).symm

/-! ## The inputs by specification -/

/-- **The (CP4) inputs of a class-three block, by its specification**: B2's `UpperAtomInputs` on an
upper block; `Replacements` on V3's frame of a middle block (`subsec:middle-comparison`). -/
def SpecInputs (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B} :
    PaperBlockSpec blockOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes blockOf b) (upperNe hW U) U.W U.r)
  | .middleUniform M => Replacements (frameU In M) (blockSquareAccepted (blockPrimes blockOf b))
      MainAnchor.paperQueries
  | .middleIndividual M => Replacements (frameI In M)
      (blockSquareAccepted (blockPrimes blockOf b)) MainAnchor.paperQueries
  | .middleCoherent M => Replacements (frameC In M) (blockSquareAccepted (blockPrimes blockOf b))
      MainAnchor.paperQueries

omit [Fintype B] [DecidableEq B] in
theorem acc_inr {b : B} (x y : BlockLabel (blockPrimes blockOf b))
    (h : blockSquareAccepted (blockPrimes blockOf b) x y) :
    prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b) x y :=
  (paperPrefixAccepted_inr_iff blockOf x y).mpr h

/-- **B2's `BlockInputs` from the inputs by specification**: unchanged on an upper block; on a
middle block the constructed atom `Replacements.toAtom` (`subsec:middle-comparison`), relative to
A1's `λ_𝔅`. -/
noncomputable def SpecInputs.toBlockInputs (hW : Target.Weil) (In : FirstStageInputs blockOf)
    {b : B} : (S : PaperBlockSpec blockOf b) → SpecInputs hW In S → BlockInputs hW In S
  | .upper _, D => D
  | .middleUniform M, R => ((Replacements.toAtom R (factsU In M)).mono acc_inr).congrLam
      (lamU hW In M)
  | .middleIndividual M, R => ((Replacements.toAtom R (factsI In M)).mono acc_inr).congrLam
      (lamI hW In M)
  | .middleCoherent M, R => ((Replacements.toAtom R (factsC In M)).mono acc_inr).congrLam
      (lamC hW In M)

omit [Fintype B] in
/-- The prices of a constructed middle atom are those of `Replacements.toAtom` (uniform root). -/
theorem toBlockInputs_uniform_prices (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) (R : SpecInputs hW In (.middleUniform M)) (sel : ℝ) :
    (SpecInputs.toBlockInputs hW In (.middleUniform M) R |> BlockInputs.toAtom hW In _).sprice sel =
        (Replacements.toAtom (D := frameU In M) R (factsU In M)).sprice sel ∧
      (SpecInputs.toBlockInputs hW In (.middleUniform M) R |> BlockInputs.toAtom hW In _).aprice
        sel = (Replacements.toAtom (D := frameU In M) R (factsU In M)).aprice sel :=
  ⟨rfl, rfl⟩

omit [Fintype B] in
/-- The prices of a constructed middle atom are those of `Replacements.toAtom` (individual
root). -/
theorem toBlockInputs_individual_prices (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleIndividualInputs blockOf b) (R : SpecInputs hW In (.middleIndividual M)) (sel : ℝ) :
    (SpecInputs.toBlockInputs hW In (.middleIndividual M) R |> BlockInputs.toAtom hW In _).sprice
        sel = (Replacements.toAtom (D := frameI In M) R (factsI In M)).sprice sel ∧
      (SpecInputs.toBlockInputs hW In (.middleIndividual M) R |> BlockInputs.toAtom hW In _).aprice
        sel = (Replacements.toAtom (D := frameI In M) R (factsI In M)).aprice sel :=
  ⟨rfl, rfl⟩


/-! ## The fold and matching changes of a middle block (for (CP6), `prop:record:matching`(i)) -/

omit [Fintype B] in
/-- The changes of the atom of a middle block (uniform root) are indexed by `Chg ⊕ Del`. -/
theorem blockAtom_uniform_T (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) (R : SpecInputs hW In (.middleUniform M)) :
    (BlockInputs.toAtom hW In (.middleUniform M)
      (SpecInputs.toBlockInputs hW In (.middleUniform M) R)).T = (Chg ⊕ Del) := rfl

omit [Fintype B] in
/-- **The fold changes of a middle block** (uniform root): at the index `.inl (.inl j)`,
`Δ_{F_j} = P(r)⁻¹ w_D r (ν'_{F_j} - Π_{F_j})`, `j ∈ {1, 2}` (`foldPat`). -/
theorem blockAtom_uniform_fold (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) (R : SpecInputs hW In (.middleUniform M)) (j : Fin 2) :
    (BlockInputs.toAtom hW In (.middleUniform M)
      (SpecInputs.toBlockInputs hW In (.middleUniform M) R)).Δ (Sum.inl (Sum.inl j)) =
      ((frameU In M).P⁻¹ * (M.W.w .D * M.r)) •
        (Replacements.newMeas (D := frameU In M) R (.inl j) -
          recM (frameU In M).F (true, ⟨.D, foldPat j⟩)) :=
  Replacements.toAtom_Δ_fold (D := frameU In M) R (factsU In M) j

omit [Fintype B] in
/-- **The matching changes of a middle block** (uniform root): at the index
`.inl (.inr (.inl s))`, `Δ_{E_s} = P(r)⁻¹ w_S r (ν'_{E_s} - Π_{E_s})`. -/
theorem blockAtom_uniform_match (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) (R : SpecInputs hW In (.middleUniform M)) (s : Fin 2) :
    (BlockInputs.toAtom hW In (.middleUniform M)
      (SpecInputs.toBlockInputs hW In (.middleUniform M) R)).Δ (Sum.inl (Sum.inr (Sum.inl s))) =
      ((frameU In M).P⁻¹ * (M.W.w .S * M.r)) •
        (Replacements.newMeas (D := frameU In M) R (.inr (.inl s)) -
          recM (frameU In M).F (true, ⟨.S, s⟩)) :=
  Replacements.toAtom_Δ_match (D := frameU In M) R (factsU In M) s

omit [Fintype B] in
/-- The fold changes of a middle block (individual-square root). -/
theorem blockAtom_individual_fold (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleIndividualInputs blockOf b) (R : SpecInputs hW In (.middleIndividual M))
    (j : Fin 2) :
    (BlockInputs.toAtom hW In (.middleIndividual M)
      (SpecInputs.toBlockInputs hW In (.middleIndividual M) R)).Δ (Sum.inl (Sum.inl j)) =
      ((frameI In M).P⁻¹ * (M.W.w .D * M.r)) •
        (Replacements.newMeas (D := frameI In M) R (.inl j) -
          recM (frameI In M).F (true, ⟨.D, foldPat j⟩)) :=
  Replacements.toAtom_Δ_fold (D := frameI In M) R (factsI In M) j

omit [Fintype B] in
/-- The matching changes of a middle block (individual-square root). -/
theorem blockAtom_individual_match (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleIndividualInputs blockOf b) (R : SpecInputs hW In (.middleIndividual M))
    (s : Fin 2) :
    (BlockInputs.toAtom hW In (.middleIndividual M)
      (SpecInputs.toBlockInputs hW In (.middleIndividual M) R)).Δ
        (Sum.inl (Sum.inr (Sum.inl s))) =
      ((frameI In M).P⁻¹ * (M.W.w .S * M.r)) •
        (Replacements.newMeas (D := frameI In M) R (.inr (.inl s)) -
          recM (frameI In M).F (true, ⟨.S, s⟩)) :=
  Replacements.toAtom_Δ_match (D := frameI In M) R (factsI In M) s

omit [Fintype B] in
/-- **The comparison law of a middle block is `ν_𝔅`** (uniform root): the atom's components sum to
`Replacements.nu`, i.e. `λ_𝔅` with the changed records replaced and the deleted ones removed. -/
theorem blockAtom_uniform_law (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    (M : MiddleUniformInputs blockOf b) (R : SpecInputs hW In (.middleUniform M)) :
    let A := BlockInputs.toAtom hW In (.middleUniform M)
      (SpecInputs.toBlockInputs hW In (.middleUniform M) R)
    ∑ i, (A.c i * A.w i) • signedIntegral (A.law i).weight =
      Replacements.nu (D := frameU In M) R :=
  Replacements.toAtom_law (D := frameU In M) R (factsU In M)

/-! ## B2's `ComparisonInputs` -/

variable (blockOf) in
/-- **B2's `ComparisonInputs` with the middle-block atoms constructed**: B2's clique and tail
inputs, and `SpecInputs` at every class-three block (W8/B2's `UpperAtomInputs` on an upper block,
`Replacements` on a middle block). -/
noncomputable def comparisonInputsOf (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf)
    (clique : ∀ q : PrefixCoord, DeletionInputs ((v2Reference blockOf hW spec hC).μ₀ (.inl q))
      (paperPrefixAccepted blockOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : B, SpecInputs hW In (spec b))
    (tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
      TailAtomInputs q (tailNe hW h4)
        (signedIntegral ((v2Reference blockOf hW spec hC).μp q).weight))
    (St At : ℝ)
    (tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St)
    (tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At) :
    ComparisonInputs blockOf hW spec hC In where
  clique := clique
  block b := SpecInputs.toBlockInputs hW In (spec b) (blk b)
  tail := tail
  St := St
  At := At
  tail_S := tail_S
  tail_A := tail_A

end Sarkozy.MiddleComparison
