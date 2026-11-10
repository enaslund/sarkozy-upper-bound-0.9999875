module

public import Sarkozy.MiddleRefinement.Frame
public import Sarkozy.MiddleComparison.PaperData
public import Sarkozy.GramBracketPaper.Paper
public import Sarkozy.ComparisonLawPaper.Prices
public import Sarkozy.MainFinal.MiddlePrices

@[expose] public section

/-!
# The refinement at a middle block of the paper, by specification (MRG)

`paper/sections/24_matching_mean.tex`, `prop:record:matching`(i), `prop:signed-sides`.

The objects of the paper's construction at a class-three block `𝔅` with specification `S` are:
A1's first stage `specStage hW In S` (its `λ = ρ + δ_E`), A2's Gram data `specGram hW In S hP hμ`
(its `Ñ = Ñ₀ + δ_E`), and B7's comparison atom `atomOf S SD`
(`BlockInputs.toAtom ∘ SpecInputs.toBlockInputs ∘ SpecData.toSpecInputs`, with records
`T = Chg ⊕ Del` and changes `Δ = R.delta` on a middle block). This file identifies them with V3's
frame `D` and B7's replacements `R` of the block, and builds the refinement from
`Frame.lean`:

* **`midFrame_bracket`**: at V3's frame (any root), `Ñ₀ + δ_E = D.Nbr` (A2's `middleGram`,
  `middleStage_delta`) and `ρ + δ_E = D.lam` (`middleStage_lam`), so `refined_bracket_signed`
  is the refined bracket in A1/A2's terms;
* **`BlockRefinement S SD hP hμ`**: the refinement data at the atom in these terms (the replaced
  records, the added positive diagonals, the refined bracket);
* **`SpecSides dL dR S SD`** (`prop:signed-sides`(i),(ii) at the block; `True` on an upper block),
  **`SpecGate d S`** (`k_s = w_D d - v_D ≥ 0`, the side gate of `prop:signed-sides`(ii));
* **`blockRefinementOf`**: on a middle block, `repl = replSet` (B7's folds `F₁, F₂` and matchings
  `E₀, E₁` in `T = Chg ⊕ Del`), the paper's signed sides on the folds and the (CP4) envelopes on
  the matchings; **`blockRefinementOf_uniform`** (and `_individual`, `_coherent`): `repl = replSet`
  and the atom's changes are B7's `R.delta` (`rfl`);
* **`block_charge_le`**: the price that `prop:record:matching`(ii) charges at the block (the
  unreplaced records and one side) is at most the price polynomial without the folds plus
  `(k_L + k_R) r² sel`; **`blockRefinementOf_LR`**: both sides cost the same.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRefinement

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.GramBracketPaper
open Sarkozy.Labellings Sarkozy.FiveType Sarkozy.CancellationSteps

/-! ## At V3's frame of a middle block (any root) -/

section MidFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (bmin : ℝ) (h : ClassThreeBlock pr)
  (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
  {d : ℝ} (hd : 0 ≤ d) (hs : BlockSharp pr hne h d)

/-- **The refined bracket in A1/A2's terms** (`prop:record:matching`(i) at a middle block): A2's
`Ñ = Ñ₀ + δ_E` and A1's `λ = ρ + δ_E` of the block are V3's `D.Nbr` and `D.lam`, so
`refined_bracket_signed` gives `(Ñ + K_L   λ + ∑_{repl} Δ ; ·   Ñ + K_R) ⪰_ι 0`. -/
theorem midFrame_bracket
    (hμ : reservedCut.Positive (signedIntegral (middleBlockReference pr hne root W hr).weight))
    (hb7 : 7 ≤ bmin) (hbp : ∀ i, bmin ≤ (pr i : ℝ))
    (hcap : MiddleLayerCaps (middleBlockFieldLaws pr hne root) I.k r)
    (hdom : ∀ t, I.k t * W.w t ≤ W.v t) (hP : W.Protects I)
    {acc : BlockLabel pr → BlockLabel pr → Prop} {E : Type} {Q : Queries E}
    (R : Replacements (middleFrame pr hne root W I hr bmin h) acc Q) (hfh : 0 ≤ I.f₁ + I.h₁)
    {dL dR : ℝ} (G : SignedSideGrams (middleFrame pr hne root W I hr bmin h) R dL dR) :
    reservedCut.Bracket
      ((middleGram pr hne root W I hr bmin h hrows₁ hd hs hμ hb7 hbp hcap hdom hP).N₀ +
          ∑ i, ((middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ' i -
            (middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ i) +
        ∑ i, sideCoefL (middleFrame pr hne root W I hr bmin h) R dL dR i •
          sideRec (middleFrame pr hne root W I hr bmin h) i)
      ((middleStage pr hne root W I hr bmin h hrows₁ hd hs).ρ +
          ∑ i, ((middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ' i -
            (middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ i) +
        ∑ t ∈ replSet, R.delta t)
      ((middleGram pr hne root W I hr bmin h hrows₁ hd hs hμ hb7 hbp hcap hdom hP).N₀ +
          ∑ i, ((middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ' i -
            (middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ i) +
        ∑ i, sideCoefR (middleFrame pr hne root W I hr bmin h) R dL dR i •
          sideRec (middleFrame pr hne root W I hr bmin h) i) := by
  have e1 : (middleGram pr hne root W I hr bmin h hrows₁ hd hs hμ hb7 hbp hcap hdom hP).N₀ +
      ∑ i, ((middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ' i -
        (middleStage pr hne root W I hr bmin h hrows₁ hd hs).κ i) =
      (middleFrame pr hne root W I hr bmin h).Nbr := by
    show (middleFrame pr hne root W I hr bmin h).Nbr0 + _ = _
    rw [middleStage_delta, ← FrameData.Nbr_eq_Nbr0_add_deltaE]
  rw [e1, middleStage_lam]
  exact refined_bracket_signed _ R hcap hdom hfh
    (middleFrame_matchingReserved pr hne root W I hr h hb7 hbp) (by show (3 : ℝ) < bmin; linarith)
    G

end MidFrame

/-! ## By specification -/

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
variable (hW : Target.Weil) (In : FirstStageInputs blockOf)

/-- **B7's comparison atom of a class-three block** from its `SpecData`. -/
noncomputable abbrev atomOf {b : B} (S : PaperBlockSpec blockOf b) (SD : SpecData hW In S) :
    AtomComparison (specLam hW In S)
      (prefixAccepted paperM0 (paperAtomMap blockOf) paperPP paperEP (.inr b))
      MainAnchor.paperQueries :=
  BlockInputs.toAtom hW In S (SpecInputs.toBlockInputs hW In S (SpecData.toSpecInputs hW In S SD))

/-- **The refinement data at the atom of a class-three block** (`prop:record:matching`(i)), in
the terms of A1 (`specStage`), A2 (`specGram`) and B7 (`atomOf`): the replaced records, the added
positive reserved diagonals with nonnegative coefficients, and the refined bracket. -/
structure BlockRefinement {b : B} (S : PaperBlockSpec blockOf b) (SD : SpecData hW In S)
    (hP : specProtects S) (hμ : reservedCut.Positive (signedIntegral (S.toAtom hW).law.weight))
    where
  repl : Finset (atomOf hW In S SD).T
  IK : Type
  [IKFintype : Fintype IK]
  kL : IK → ℝ
  kR : IK → ℝ
  kL_nonneg : ∀ i, 0 ≤ kL i
  kR_nonneg : ∀ i, 0 ≤ kR i
  κK : IK → SlotMeasure (BlockRes paperM0 (paperAtomMap blockOf) (.inr b))
  κK_pos : ∀ i, IsPositiveRecord (κK i)
  κK_diag : ∀ i, TheoremC.IsDiagonalAt reservedCut (κK i)
  /-- The refined bracket at the atom. -/
  bracket : reservedCut.Bracket
    ((specGram hW In S hP hμ).N₀ + ∑ i, ((specStage hW In S).κ' i - (specStage hW In S).κ i) +
      ∑ i, kL i • κK i)
    ((specStage hW In S).ρ + ∑ i, ((specStage hW In S).κ' i - (specStage hW In S).κ i) +
      ∑ t ∈ repl, (atomOf hW In S SD).Δ t)
    ((specGram hW In S hP hμ).N₀ + ∑ i, ((specStage hW In S).κ' i - (specStage hW In S).κ i) +
      ∑ i, kR i • κK i)

attribute [instance] BlockRefinement.IKFintype

/-- **The signed-side Grams of a middle block** (`prop:signed-sides`(i),(ii); `SignedSideGrams` at
V3's frame and B7's replacements of the block). `True` on an upper block. *Hypothesis.* -/
def SpecSides {b : B} (dL dR : ℝ) : (S : PaperBlockSpec blockOf b) → SpecData hW In S → Prop
  | .upper _, _ => True
  | .middleUniform M, SD => SignedSideGrams (frameU In M) SD.down.toReplacements dL dR
  | .middleIndividual M, SD => SignedSideGrams (frameI In M) SD.down.toReplacements dL dR
  | .middleCoherent M, SD => SignedSideGrams (frameC In M) SD.down.toReplacements dL dR

/-- **The side gate** `k_s = w_D d_s - v_D ≥ 0` of a middle block (`prop:signed-sides`(ii),
`cert:record:matching`). `True` on an upper block. -/
def SpecGate {b : B} (d : ℝ) : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => 0 ≤ M.W.w .D * d - M.W.v .D
  | .middleIndividual M => 0 ≤ M.W.w .D * d - M.W.v .D
  | .middleCoherent M => 0 ≤ M.W.w .D * d - M.W.v .D

/-- The sign `f₁ + h₁ ≥ 0` of a middle specification (`True` on an upper block). -/
def SpecSign {b : B} : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => 0 ≤ M.I.f₁ + M.I.h₁
  | .middleIndividual M => 0 ≤ M.I.f₁ + M.I.h₁
  | .middleCoherent M => 0 ≤ M.I.f₁ + M.I.h₁

/-- **The refinement of a middle block with the paper's signed sides** (`prop:record:matching`(i),
`prop:signed-sides`): `repl = replSet` (the folds and the matchings), the fold companions with the
side coefficients `P⁻¹ r² k_s` and the matching envelopes with their (CP4) prices. On an upper
block there is nothing to build (`specUpper S = false` excludes it). -/
noncomputable def blockRefinementOf {b : B} (dL dR : ℝ) :
    (S : PaperBlockSpec blockOf b) → (SD : SpecData hW In S) → (hP : specProtects S) →
      (hμ : reservedCut.Positive (signedIntegral (S.toAtom hW).law.weight)) →
      specUpper S = false → SpecSign S → SpecGate dL S → SpecGate dR S →
      SpecSides hW In dL dR S SD →
      BlockRefinement hW In S SD hP hμ
  | .upper _, _, _, _, hu, _, _, _, _ => absurd hu (by simp [specUpper])
  | .middleUniform M, SD, hP, hμ, _, hfh, gL, gR, G =>
    { repl := replSet
      IK := SideIdx
      kL := sideCoefL (frameU In M) SD.down.toReplacements dL dR
      kR := sideCoefR (frameU In M) SD.down.toReplacements dL dR
      kL_nonneg := sideCoefL_nonneg _ _ gL gR
      kR_nonneg := sideCoefR_nonneg _ _ gL gR
      κK := sideRec (frameU In M)
      κK_pos := sideRec_pos (factsU In M)
      κK_diag := sideRec_diag (factsU In M)
      bracket := midFrame_bracket _ M.hne _ M.W M.I M.hr (In.bmin b) _ M.hrows₁ _ _ hμ
        (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP _ hfh G }
  | .middleIndividual M, SD, hP, hμ, _, hfh, gL, gR, G =>
    { repl := replSet
      IK := SideIdx
      kL := sideCoefL (frameI In M) SD.down.toReplacements dL dR
      kR := sideCoefR (frameI In M) SD.down.toReplacements dL dR
      kL_nonneg := sideCoefL_nonneg _ _ gL gR
      kR_nonneg := sideCoefR_nonneg _ _ gL gR
      κK := sideRec (frameI In M)
      κK_pos := sideRec_pos (factsI In M)
      κK_diag := sideRec_diag (factsI In M)
      bracket := midFrame_bracket _ M.hne _ M.W M.I M.hr (In.bmin b) _ M.hrows₁ _ _ hμ
        (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP _ hfh G }
  | .middleCoherent M, SD, hP, hμ, _, hfh, gL, gR, G =>
    { repl := replSet
      IK := SideIdx
      kL := sideCoefL (frameC In M) SD.down.toReplacements dL dR
      kR := sideCoefR (frameC In M) SD.down.toReplacements dL dR
      kL_nonneg := sideCoefL_nonneg _ _ gL gR
      kR_nonneg := sideCoefR_nonneg _ _ gL gR
      κK := sideRec (frameC In M)
      κK_pos := sideRec_pos (factsC In M)
      κK_diag := sideRec_diag (factsC In M)
      bracket := midFrame_bracket _ M.hne _ M.W M.I M.hr (In.bmin b) _ M.hrows₁ _ _ hμ
        (seven_le_bmin In b) (In.hbp b) M.hcap M.hW.2.2.2.2.2.2.2.2 hP _ hfh G }

omit [Fintype B] in
/-- **The identification on a middle block (uniform root)**: the replaced records are B7's
`replSet` (the folds `.inl (.inl j)` and matchings `.inl (.inr (.inl s))` of `T = Chg ⊕ Del`),
and the atom's changes are B7's `R.delta`. -/
theorem blockRefinementOf_uniform {b : B} (dL dR : ℝ) (M : MiddleUniformInputs blockOf b)
    (SD : SpecData hW In (.middleUniform M)) (hP : specProtects (PaperBlockSpec.middleUniform M))
    (hμ : reservedCut.Positive
      (signedIntegral ((PaperBlockSpec.middleUniform M).toAtom hW).law.weight))
    (hu : specUpper (PaperBlockSpec.middleUniform M) = false)
    (hfh : SpecSign (PaperBlockSpec.middleUniform M))
    (gL : SpecGate dL (PaperBlockSpec.middleUniform M))
    (gR : SpecGate dR (PaperBlockSpec.middleUniform M))
    (G : SpecSides hW In dL dR (.middleUniform M) SD) :
    (blockRefinementOf hW In dL dR (.middleUniform M) SD hP hμ hu hfh gL gR G).repl = replSet ∧
      (atomOf hW In (.middleUniform M) SD).Δ = SD.down.toReplacements.delta :=
  ⟨rfl, rfl⟩

omit [Fintype B] in
/-- The identification on a middle block (individual-square root). -/
theorem blockRefinementOf_individual {b : B} (dL dR : ℝ) (M : MiddleIndividualInputs blockOf b)
    (SD : SpecData hW In (.middleIndividual M))
    (hP : specProtects (PaperBlockSpec.middleIndividual M))
    (hμ : reservedCut.Positive
      (signedIntegral ((PaperBlockSpec.middleIndividual M).toAtom hW).law.weight))
    (hu : specUpper (PaperBlockSpec.middleIndividual M) = false)
    (hfh : SpecSign (PaperBlockSpec.middleIndividual M))
    (gL : SpecGate dL (PaperBlockSpec.middleIndividual M))
    (gR : SpecGate dR (PaperBlockSpec.middleIndividual M))
    (G : SpecSides hW In dL dR (.middleIndividual M) SD) :
    (blockRefinementOf hW In dL dR (.middleIndividual M) SD hP hμ hu hfh gL gR G).repl =
        replSet ∧
      (atomOf hW In (.middleIndividual M) SD).Δ = SD.down.toReplacements.delta :=
  ⟨rfl, rfl⟩

omit [Fintype B] in
/-- The identification on a middle block (coherent root). -/
theorem blockRefinementOf_coherent {b : B} (dL dR : ℝ) (M : MiddleCoherentInputs blockOf b)
    (SD : SpecData hW In (.middleCoherent M)) (hP : specProtects (PaperBlockSpec.middleCoherent M))
    (hμ : reservedCut.Positive
      (signedIntegral ((PaperBlockSpec.middleCoherent M).toAtom hW).law.weight))
    (hu : specUpper (PaperBlockSpec.middleCoherent M) = false)
    (hfh : SpecSign (PaperBlockSpec.middleCoherent M))
    (gL : SpecGate dL (PaperBlockSpec.middleCoherent M))
    (gR : SpecGate dR (PaperBlockSpec.middleCoherent M))
    (G : SpecSides hW In dL dR (.middleCoherent M) SD) :
    (blockRefinementOf hW In dL dR (.middleCoherent M) SD hP hμ hu hfh gL gR G).repl = replSet ∧
      (atomOf hW In (.middleCoherent M) SD).Δ = SD.down.toReplacements.delta :=
  ⟨rfl, rfl⟩

/-! ## The price charged at a middle block -/

open Sarkozy.MainFinal (MiddleConsts SpecShape SpecNorm specMidBound midPoly)

/-- The middle constants with the fold constants removed: `(s_F, a_F, ℓ_t) = 0`, `s_E`, `a_E` kept
(the price polynomial of the records other than the folds). -/
def noFoldConsts (κ : MiddleConsts) : MiddleConsts := ⟨0, 0, 0, κ.sE, κ.aE⟩

/-- **The price of the fold sides of a middle block**, `(k_L + k_R) r² sel` with
`k_s = w_D d_s - v_D` (`prop:signed-sides`(ii),(iii); `0` on an upper block). -/
noncomputable def specFoldBound {b : B} (dL dR sel : ℝ) : PaperBlockSpec blockOf b → ℝ
  | .upper _ => 0
  | .middleUniform M => (M.W.w .D * dL - M.W.v .D + (M.W.w .D * dR - M.W.v .D)) * M.r ^ 2 * sel
  | .middleIndividual M =>
      (M.W.w .D * dL - M.W.v .D + (M.W.w .D * dR - M.W.v .D)) * M.r ^ 2 * sel
  | .middleCoherent M =>
      (M.W.w .D * dL - M.W.v .D + (M.W.w .D * dR - M.W.v .D)) * M.r ^ 2 * sel

theorem foldSide_le {X : Type} [Fintype X] [DecidableEq X] (D : FrameData X) {dL dR sel : ℝ}
    (hL : 0 ≤ kSide D dL) (hR : 0 ≤ kSide D dR) (hsel : 0 ≤ sel) :
    D.P⁻¹ * D.r ^ 2 * (kSide D dL + kSide D dR) * sel ≤
      (kSide D dL + kSide D dR) * D.r ^ 2 * sel := by
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have hPi : D.P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP1
  have hk : 0 ≤ (kSide D dL + kSide D dR) * D.r ^ 2 * sel :=
    mul_nonneg (mul_nonneg (add_nonneg hL hR) (pow_nonneg D.r_nonneg 2)) hsel
  nlinarith

omit [Fintype B] in
/-- **The price charged at a middle block by `prop:record:matching`(ii)**: the records outside
`repl` and the left side cost at most the price polynomial of the records other than the folds
(`noFold_le`, from the norm sizes of the matchings, merges and constants) plus the fold sides
`(k_L + k_R) r² sel`. -/
theorem block_charge_le (κ : MiddleConsts) {X : ℕ} {bl sel : ℝ} (hX : 4 ≤ X)
    (hb : (X : ℝ) ≤ bl) (hsel : 0 ≤ sel) {b : B} (dL dR : ℝ) :
    ∀ (S : PaperBlockSpec blockOf b) (SD : SpecData hW In S) (hP : specProtects S)
      (hμ : reservedCut.Positive (signedIntegral (S.toAtom hW).law.weight))
      (hu : specUpper S = false) (hfh : SpecSign S) (gL : SpecGate dL S) (gR : SpecGate dR S)
      (G : SpecSides hW In dL dR S SD), SpecShape bl S → SpecNorm hW In κ bl S SD →
      ∑ t ∈ univ \ (blockRefinementOf hW In dL dR S SD hP hμ hu hfh gL gR G).repl,
          ((atomOf hW In S SD).πt t .sym + (atomOf hW In S SD).πt t .skew) * sel +
        ∑ i, (blockRefinementOf hW In dL dR S SD hP hμ hu hfh gL gR G).kL i *
          mass ((blockRefinementOf hW In dL dR S SD hP hμ hu hfh gL gR G).κK i) * sel ≤
      specMidBound (noFoldConsts κ) X bl sel S + specFoldBound dL dR sel S
  | .upper _, _, _, _, hu, _, _, _, _, _, _ => absurd hu (by simp [specUpper])
  | .middleUniform M, SD, _, _, _, _, gL, gR, _, ⟨hr, hfh⟩, ⟨_, _, hEs, hEa, hM, hCs, hCa⟩ => by
    have e := others_add_sideL SD.down.toReplacements (factsU In M) dL dR sel
    have h1 := noFold_le (frameU In M) SD.down.toReplacements (factsU In M) hX hb hr hsel hfh
      hEs hEa hM hCs hCa
    have h2 := foldSide_le (frameU In M) gL gR hsel
    refine le_of_eq_of_le e ?_
    exact add_le_add h1 h2
  | .middleIndividual M, SD, _, _, _, _, gL, gR, _, ⟨hr, hfh⟩, ⟨_, _, hEs, hEa, hM, hCs, hCa⟩ =>
    by
    have e := others_add_sideL SD.down.toReplacements (factsI In M) dL dR sel
    have h1 := noFold_le (frameI In M) SD.down.toReplacements (factsI In M) hX hb hr hsel hfh
      hEs hEa hM hCs hCa
    have h2 := foldSide_le (frameI In M) gL gR hsel
    refine le_of_eq_of_le e ?_
    exact add_le_add h1 h2
  | .middleCoherent M, SD, _, _, _, _, gL, gR, _, ⟨hr, hfh⟩, ⟨_, _, hEs, hEa, hM, hCs, hCa⟩ => by
    have e := others_add_sideL SD.down.toReplacements (factsC In M) dL dR sel
    have h1 := noFold_le (frameC In M) SD.down.toReplacements (factsC In M) hX hb hr hsel hfh
      hEs hEa hM hCs hCa
    have h2 := foldSide_le (frameC In M) gL gR hsel
    refine le_of_eq_of_le e ?_
    exact add_le_add h1 h2

omit [Fintype B] in
/-- **The two sides cost the same** (the exchange of `lem:record:asymmetric-gram`(c)). -/
theorem blockRefinementOf_LR {b : B} (dL dR sel : ℝ) :
    ∀ (S : PaperBlockSpec blockOf b) (SD : SpecData hW In S) (hP : specProtects S)
      (hμ : reservedCut.Positive (signedIntegral (S.toAtom hW).law.weight))
      (hu : specUpper S = false) (hfh : SpecSign S) (gL : SpecGate dL S) (gR : SpecGate dR S)
      (G : SpecSides hW In dL dR S SD),
      ∑ i, (blockRefinementOf hW In dL dR S SD hP hμ hu hfh gL gR G).kL i *
          mass ((blockRefinementOf hW In dL dR S SD hP hμ hu hfh gL gR G).κK i) * sel =
        ∑ i, (blockRefinementOf hW In dL dR S SD hP hμ hu hfh gL gR G).kR i *
          mass ((blockRefinementOf hW In dL dR S SD hP hμ hu hfh gL gR G).κK i) * sel
  | .upper _, _, _, _, hu, _, _, _, _ => absurd hu (by simp [specUpper])
  | .middleUniform M, SD, _, _, _, _, _, _, _ =>
    sideL_eq_sideR SD.down.toReplacements (factsU In M) dL dR sel
  | .middleIndividual M, SD, _, _, _, _, _, _, _ =>
    sideL_eq_sideR SD.down.toReplacements (factsI In M) dL dR sel
  | .middleCoherent M, SD, _, _, _, _, _, _, _ =>
    sideL_eq_sideR SD.down.toReplacements (factsC In M) dL dR sel

end Sarkozy.MiddleRefinement
