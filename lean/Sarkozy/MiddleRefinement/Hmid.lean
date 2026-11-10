module

public import Sarkozy.MiddleRefinement.Paper

@[expose] public section

/-!
# `hmid` reduced to the per-record norm bounds and one finite sum (MRG)

`paper/sections/24_matching_mean.tex`, `prop:record:matching`(ii), `prop:signed-sides`(iii),
`def:closing-quantities`(5); `paper/sections/21_middle_records.tex`,
`lem:middle-comparison-prices`.

With `Env.MR = midRefinementOf` (`Paper.lean`), the field `hmid` of the F1 statement,
`midOthers(L) + max(∑ KL, ∑ KR) + τ ≤ T^{ledger}` at every scale `L`, is proved from
* the paper's norm bounds of the middle blocks (`SA.hN`'s `SpecNormBounds`, of which only the
  matching, merge and constant rows are used here), and
* the chosen sides `d_L(i), d_R(i)` per piece with their block Grams (`PieceSides`), and
* **one finite numerical inequality** (`hnum`):
  `middlePart κ⁰ + ∑_i (k_L(i) + k_R(i)) c'₂(i) + τ ≤ T^{ledger}`, where `κ⁰` is `κ` with the fold
  constants `s_F, a_F, ℓ_t` set to `0` (HS's `middlePart`: the price polynomial of every middle
  record except the folds, at N2's charges `f1c2`, `f1c3`), and `k_s(i) = w_{D,i} d_s(i) - v_{D,i}`.

Steps (all proved):
* `pieceSide`, **`PieceSides`** (per-piece sides, the block Grams `SpecSides`, the gates),
  `PieceSides.toSideInputs`;
* **`block_le`**: at a middle block in piece `i`, the price of the unreplaced records plus the
  left side is at most `midBound κ⁰ b + (k_L(i) + k_R(i)) r_𝔅² q_𝔅^{2a}` (`block_charge_le`,
  `paperSpec_facts`, `paperSpec_fold`);
* `sum_foldSite`: grouping the fold sides by piece (`∑_i (k_L + k_R)(i) b₂(i)`);
* **`hmid_of_pieces`**: the field, for every `L`.

Since RP (9 November 2026) the front prices the middle records at their bounds at
`κ′ = paperKappa` (`MainFinalF1c.SignedSpec.toSpecDataAt`), so `block_le` and `hmid_of_pieces`
take `hκP : κ′ ≤ κ` (`KappaLe.refl` at the only instance, `κ = paperKappa`).

**Remark** (the sum, not the max). Both sides carry `k_L + k_R` (the fold `F₁` has `(d_L, d_R)`,
`F₂` the interchange, `lem:record:asymmetric-gram`(c)), so `∑ KL = ∑ KR` and Lean's `max` is the
paper's `T_K` charge `∑_i (k_{L,i} + k_{R,i}) Ī_{2,i}`. FA1 §1.2's estimated room of 0.0785 from
"max instead of sum" does not exist.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRefinement

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.CancellationSteps Sarkozy.BlockSpecPaper Sarkozy.MainTarget
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.MainFinal (hCF MiddleConsts SpecShape SpecNorm specMidBound midPoly midK2 midK3 midK4
  midK5 pieceScale pieceScale_nonneg)
open Sarkozy.MainFinal2 (MidRefinement AtomRefinement)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3 f1_charge_le)
open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk midAtom midBound sum_midBound
  blockCharge_shift SpecNormBounds specNorm_of_bounds)
open Sarkozy.MainFinalF1c (ComparisonPartsTC midOthersK1)
open Sarkozy.NumericalFields (KappaNonneg midK_signs)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- The side coefficient `k_s(i) = w_{D,i} d_s(i) - v_{D,i}` of piece `i`. -/
noncomputable def kPiece (d : Fin 33 → ℝ) (i : Fin 33) : ℝ :=
  (allpWeights i).w .D * d i - (allpWeights i).v .D

/-- The side of a block: the side of its piece (`0` on a band). -/
noncomputable def pieceSide (d : Fin 33 → ℝ) (b : Blk) : ℝ :=
  match blockSite b with
  | .inl i => d i
  | .inr _ => 0

theorem pieceSide_eq (d : Fin 33 → ℝ) {b : Blk} {i : Fin 33} (hs : blockSite b = .inl i) :
    pieceSide d b = d i := by
  unfold pieceSide
  rw [hs]

/-! ## The paper's specification at a block of piece `i` -/

variable (hW A) in
theorem middleSpec_fold (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (dL dR sel : ℝ) :
    ∀ o hu, specFoldBound dL dR sel (middleSpec hW A b i hs o hu) =
      (kPiece (fun _ => dL) i + kPiece (fun _ => dR) i) * BlockSpecPaper.blockScale b ^ 2 * sel
  | none, _ => by simp only [middleSpec, specFoldBound, kPiece]
  | some _, _ => by simp only [middleSpec, specFoldBound, kPiece]

variable (hW A) in
theorem siteSpec_fold (b : Blk) (i : Fin 33) (dL dR sel : ℝ) :
    ∀ s (hs : blockSite b = s), s = .inl i →
      specFoldBound dL dR sel (siteSpec hW A b s hs) =
        (kPiece (fun _ => dL) i + kPiece (fun _ => dR) i) * BlockSpecPaper.blockScale b ^ 2 * sel
  | .inl j, hs, h => by
    obtain rfl : j = i := Sum.inl.inj h
    exact middleSpec_fold hW A b j hs dL dR sel _ rfl
  | .inr _, _, h => absurd h (by simp)

variable (hW A) in
/-- **The fold sides of a block of piece `i`**: `specFoldBound = (k_L(i) + k_R(i)) r_𝔅² sel`. -/
theorem paperSpec_fold (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (dL dR sel : ℝ) :
    specFoldBound dL dR sel (specF hW A b) =
      (kPiece (fun _ => dL) i + kPiece (fun _ => dR) i) * BlockSpecPaper.blockScale b ^ 2 * sel :=
  siteSpec_fold hW A b i dL dR sel _ rfl hs

variable (hW A) in
theorem middleSpec_gate (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (d : ℝ)
    (h : 0 ≤ kPiece (fun _ => d) i) : ∀ o hu, SpecGate d (middleSpec hW A b i hs o hu)
  | none, _ => h
  | some _, _ => h

variable (hW A) in
theorem siteSpec_gate (b : Blk) (i : Fin 33) (d : ℝ) (h : 0 ≤ kPiece (fun _ => d) i) :
    ∀ s (hs : blockSite b = s), s = .inl i → SpecGate d (siteSpec hW A b s hs)
  | .inl j, hs, hj => by
    obtain rfl : j = i := Sum.inl.inj hj
    exact middleSpec_gate hW A b j hs d h _ rfl
  | .inr _, _, hj => absurd hj (by simp)

variable (hW A) in
/-- **The side gate of a block of piece `i`** is the gate `k_s(i) ≥ 0` of its piece. -/
theorem paperSpec_gate (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (d : ℝ)
    (h : 0 ≤ kPiece (fun _ => d) i) : SpecGate d (specF hW A b) :=
  siteSpec_gate hW A b i d h _ rfl hs

theorem site_of_mid (b : Blk) (hu : specUpper (specF hW A b) = false) :
    ∃ i, blockSite b = .inl i := by
  rcases hs : blockSite b with i | k
  · exact ⟨i, rfl⟩
  · have := MainFinalF1.paperSpec_upper hW A b k hs
    rw [hu] at this
    exact absurd this (by decide)

/-! ## The inputs per piece -/

/-- **The paper's sides per piece** (`prop:signed-sides`(ii)): the chosen sides `d_L(i), d_R(i)`,
the gates `k_s(i) ≥ 0` (finite checks of the recorded weights, `cert:record:matching`), and the
block Grams of every middle block of piece `i` with these sides (`SpecSides`,
`prop:signed-sides`(i),(ii); *hypothesis*). -/
structure PieceSides (C : ComparisonParts hW hMR hFour A) (dL dR : Fin 33 → ℝ) : Prop where
  gram : ∀ b i, blockSite b = .inl i →
    SpecSides hW (paperIn f1Cell) (dL i) (dR i) (specF hW A b) (C.blk b)
  gateL : ∀ i, 0 ≤ kPiece dL i
  gateR : ∀ i, 0 ≤ kPiece dR i

/-- The block-level inputs of `midRefinementOf` from the per-piece sides. -/
noncomputable def PieceSides.toSideInputs {C : ComparisonParts hW hMR hFour A} {dL dR : Fin 33 → ℝ}
    (P : PieceSides C dL dR) : SideInputs C where
  dL := pieceSide dL
  dR := pieceSide dR
  gram b hu := by
    obtain ⟨i, hs⟩ := site_of_mid b hu
    rw [pieceSide_eq dL hs, pieceSide_eq dR hs]
    exact P.gram b i hs
  gateL b hu := by
    obtain ⟨i, hs⟩ := site_of_mid b hu
    rw [pieceSide_eq dL hs]
    exact paperSpec_gate hW A b i hs _ (P.gateL i)
  gateR b hu := by
    obtain ⟨i, hs⟩ := site_of_mid b hu
    rw [pieceSide_eq dR hs]
    exact paperSpec_gate hW A b i hs _ (P.gateR i)

/-! ## The charge of a block, and the sums -/

/-- The fold-side bound of a block: `(k_L(i) + k_R(i)) r_𝔅² q_𝔅^{2a}` on piece `i`, `0` on a
band. -/
noncomputable def foldSite (dL dR : Fin 33 → ℝ) (b : Blk) : ℝ :=
  match blockSite b with
  | .inl i => (kPiece dL i + kPiece dR i) * BlockSpecPaper.blockScale b ^ 2 *
      paperSelAt (paperAtomMap bOf) targetDecay (.inr b)
  | .inr _ => 0

theorem sel_nonneg (b : Blk) : 0 ≤ paperSelAt (paperAtomMap bOf) targetDecay (.inr b) :=
  le_trans zero_le_one (one_le_paperSelAt (paperAtomMap bOf) targetDecay_nonneg _)

/-- **The charge of a middle block** (`prop:record:matching`(ii) at the block): the unreplaced
records and the left side cost at most `midBound κ⁰ b + foldSite b` (with the pricing constants
`κ′ = paperKappa` at most `κ`, `hκP`). -/
theorem block_le (C : ComparisonPartsTC hW hMR hFour A) {dL dR : Fin 33 → ℝ}
    (P : PieceSides C.toK1 dL dR) (κ : Fin 33 → MiddleConsts)
    (hN : ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b))
    (hκP : ∀ i, MainFinalF1c.KappaLe (HsumProof.paperKappa i) (κ i)) (L : ℕ) (b : Blk)
    (hu : specUpper (specF hW A b) = false) :
    ∑ t ∈ univ \ (midRefinementOf C.toK1 P.toSideInputs).toPrefix.repl L (.inl (.inr b)),
        (C.toK1.CL.π L (.inl (.inr b)) t .sym + C.toK1.CL.π L (.inl (.inr b)) t .skew) +
      (midRefinementOf C.toK1 P.toSideInputs).toPrefix.KL (.inr b) ≤
      midBound (fun i => noFoldConsts (κ i)) b + foldSite dL dR b := by
  obtain ⟨i, hs⟩ := site_of_mid (hW := hW) (A := A) b hu
  rw [others_eq C.toK1 P.toSideInputs L b hu, KL_eq C.toK1 P.toSideInputs b hu]
  obtain ⟨-, hsh, hmid⟩ := MainFinalF1.paperSpec_facts hW A b i hs (noFoldConsts (κ i))
    (pieceStart i) (paperSelAt (paperAtomMap bOf) targetDecay (.inr b))
  have hX : 4 ≤ pieceStart i := le_trans (by norm_num [PartV.Q3]) (pieceStart_ge_Q3 i)
  have hb : (pieceStart i : ℝ) ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact_mod_cast h
  have hNorm := MainFinalF1c.specNormAt_of_bounds hW (paperIn f1Cell) (MainFinalF1c.blockKappa b)
    (κ i) (blockLeast b) (by rw [MainFinalF1c.blockKappa_eq hs]; exact hκP i) (specF hW A b)
    (C.blk b) (hN b i hs)
  have h := block_charge_le hW (paperIn f1Cell) (κ i) hX hb (sel_nonneg b)
    (P.toSideInputs.dL b) (P.toSideInputs.dR b) (specF hW A b) (C.toK1.blk b)
    ((paperGi hW A).protects b) (hμF hW hMR hFour A b) hu (specSign_of_mid b hu)
    (P.toSideInputs.gateL b hu) (P.toSideInputs.gateR b hu) (P.toSideInputs.gram b hu) hsh hNorm
  have hm : specMidBound (noFoldConsts (κ i)) (pieceStart i) (blockLeast b)
      (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) (specF hW A b) =
      midBound (fun i => noFoldConsts (κ i)) b := by
    rw [hmid]
    unfold midBound
    rw [hs]
    rfl
  have hf : specFoldBound (P.toSideInputs.dL b) (P.toSideInputs.dR b)
      (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) (specF hW A b) = foldSite dL dR b := by
    rw [paperSpec_fold hW A b i hs]
    show (kPiece (fun _ => pieceSide dL b) i + kPiece (fun _ => pieceSide dR b) i) * _ * _ = _
    rw [pieceSide_eq dL hs, pieceSide_eq dR hs]
    unfold foldSite
    rw [hs]
    rfl
  rw [hm, hf] at h
  exact h

/-- **Grouping the fold sides by piece**: `∑_𝔅 foldSite 𝔅 = ∑_i (k_L(i) + k_R(i)) b₂(i)`. -/
theorem sum_foldSite (dL dR : Fin 33 → ℝ) :
    ∑ b, foldSite dL dR b = ∑ i : Fin 33, (kPiece dL i + kPiece dR i) *
      blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 2 i := by
  have hb : ∀ b : Blk, foldSite dL dR b = ∑ i : Fin 33,
      if blockSite b = .inl i then (kPiece dL i + kPiece dR i) * BlockSpecPaper.blockScale b ^ 2 *
        paperSelAt (paperAtomMap bOf) targetDecay (.inr b) else 0 := by
    intro b
    unfold foldSite
    rcases h : blockSite b with i | k
    · simp only [Sum.inl.injEq]
      rw [Finset.sum_ite_eq]
      simp
    · simp
  simp_rw [hb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  unfold blockCharge
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem foldSite_upper (dL dR : Fin 33 → ℝ) (b : Blk) (hb : specUpper (specF hW A b) = true) :
    foldSite dL dR b = 0 := by
  unfold foldSite
  rcases h : blockSite b with i | k
  · have := (MainFinalF1.paperSpec_facts hW A b i h ⟨0, 0, 0, 0, 0⟩ 0 0).1
    rw [hb] at this
    exact absurd this (by decide)
  · rfl

/-- The fold sides cost at most `∑_i (k_L(i) + k_R(i)) c'₂(i)` (N2's charges, `thm:bmor`). -/
theorem sum_foldSite_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) {dL dR : Fin 33 → ℝ}
    (hL : ∀ i, 0 ≤ kPiece dL i) (hR : ∀ i, 0 ≤ kPiece dR i) :
    ∑ b, foldSite dL dR b ≤ ∑ i : Fin 33, (kPiece dL i + kPiece dR i) * f1c2 i := by
  rw [sum_foldSite]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (f1_charge_le hB hRR i).1 (add_nonneg (hL i) (hR i))

/-- The middle bound at `κ⁰` costs at most HS's `middlePart κ⁰` (N2's charges, `thm:bmor`). -/
theorem sum_midBound_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (κ : Fin 33 → MiddleConsts) (hκ : ∀ i, KappaNonneg (κ i)) :
    ∑ b, midBound (fun i => noFoldConsts (κ i)) b ≤
      HsumProof.middlePart (fun i => noFoldConsts (κ i)) := by
  rw [sum_midBound]
  unfold HsumProof.middlePart
  have hκ0 : ∀ i, KappaNonneg (noFoldConsts (κ i)) := fun i =>
    ⟨le_rfl, le_rfl, le_rfl, (hκ i).2.2.2.1, (hκ i).2.2.2.2⟩
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨k2, k3, k4, k5⟩ := midK_signs _ hκ0 i
  have h₂ := (f1_charge_le hB hRR i).1
  have h₃ := (f1_charge_le hB hRR i).2
  have h₄ := (blockCharge_shift i 3 1).trans
    (mul_le_mul_of_nonneg_left h₃ (pow_nonneg (pieceScale_nonneg i) 1))
  have h₅ := (blockCharge_shift i 3 2).trans
    (mul_le_mul_of_nonneg_left h₃ (pow_nonneg (pieceScale_nonneg i) 2))
  have := mul_le_mul_of_nonneg_left h₂ k2
  have := mul_le_mul_of_nonneg_left h₃ k3
  have := mul_le_mul_of_nonneg_left h₄ k4
  have := mul_le_mul_of_nonneg_left h₅ k5
  simp only [pow_one] at *
  nlinarith

/-! ## `hmid` -/

theorem KL_inl (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (q : PrefixCoord) :
    (midRefinementOf C SI).toPrefix.KL (.inl q) = 0 := by
  show (if midAtom hW A (.inl q) = true then (midRefinementOf C SI).KL (.inl q) else 0) = 0
  simp [midAtom]

theorem KR_inl (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (q : PrefixCoord) :
    (midRefinementOf C SI).toPrefix.KR (.inl q) = 0 := by
  show (if midAtom hW A (.inl q) = true then (midRefinementOf C SI).KR (.inl q) else 0) = 0
  simp [midAtom]

theorem KL_upper (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (b : Blk)
    (hu : specUpper (specF hW A b) = true) : (midRefinementOf C SI).toPrefix.KL (.inr b) = 0 := by
  show (if midAtom hW A (.inr b) = true then (midRefinementOf C SI).KL (.inr b) else 0) = 0
  simp [midAtom, hu]

theorem KR_upper (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) (b : Blk)
    (hu : specUpper (specF hW A b) = true) : (midRefinementOf C SI).toPrefix.KR (.inr b) = 0 := by
  show (if midAtom hW A (.inr b) = true then (midRefinementOf C SI).KR (.inr b) else 0) = 0
  simp [midAtom, hu]

/-- **`∑ KL = ∑ KR`**: the two sides of `midRefinementOf` cost the same at every block. -/
theorem sum_KL_eq_KR (C : ComparisonParts hW hMR hFour A) (SI : SideInputs C) :
    ∑ β, (midRefinementOf C SI).toPrefix.KR β = ∑ β, (midRefinementOf C SI).toPrefix.KL β := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [KL_inl, KR_inl, sum_const_zero, zero_add]
  refine sum_congr rfl fun b _ => ?_
  by_cases hu : specUpper (specF hW A b) = false
  · rw [KL_eq C SI b hu, KR_eq C SI b hu]
    exact (blockRefinementOf_LR hW (paperIn f1Cell) (SI.dL b) (SI.dR b) _ (specF hW A b) (C.blk b)
      _ _ hu _ _ _ _).symm
  · have hu' : specUpper (specF hW A b) = true := by simpa using hu
    rw [KL_upper C SI b hu', KR_upper C SI b hu']

/-- **`hmid` of the F1 statement, reduced** (`prop:record:matching`(ii), `prop:signed-sides`(iii),
`def:closing-quantities`(5)): with `Env.MR = midRefinementOf` at the per-piece sides `d_L, d_R`,
for every scale `L`,
`midOthers(L) + max(∑ KL, ∑ KR) + τ ≤ T^{ledger}`,
from the norm bounds `hN` (`SA.hN`'s form; the matching, merge and constant rows are used) with
`κ′ = paperKappa ≤ κ` (`hκP`, RP), the signs of `κ`, `thm:bmor` and `ThetaSmallRR` (N2's
charges), and the finite inequality
`hnum : middlePart κ⁰ + ∑_i (k_L(i) + k_R(i)) c'₂(i) + τ ≤ T^{ledger}`. -/
theorem hmid_of_pieces (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (C : ComparisonPartsTC hW hMR hFour A) {dL dR : Fin 33 → ℝ} (P : PieceSides C.toK1 dL dR)
    (κ : Fin 33 → MiddleConsts) (hκ : ∀ i, KappaNonneg (κ i))
    (hN : ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b))
    (hκP : ∀ i, MainFinalF1c.KappaLe (HsumProof.paperKappa i) (κ i)) {τ : ℝ}
    (hnum : HsumProof.middlePart (fun i => noFoldConsts (κ i)) +
      ∑ i : Fin 33, (kPiece dL i + kPiece dR i) * f1c2 i + τ ≤ targetLedger.T) (L : ℕ) :
    midOthersK1 C.toK1 (midRefinementOf C.toK1 P.toSideInputs) L +
      max (∑ β, (midRefinementOf C.toK1 P.toSideInputs).toPrefix.KL β)
        (∑ β, (midRefinementOf C.toK1 P.toSideInputs).toPrefix.KR β) + τ ≤ targetLedger.T := by
  rw [sum_KL_eq_KR, max_self, Fintype.sum_sum_type]
  simp only [KL_inl, sum_const_zero, zero_add]
  have hsplit : ∑ b, (midRefinementOf C.toK1 P.toSideInputs).toPrefix.KL (.inr b) =
      ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = false),
        (midRefinementOf C.toK1 P.toSideInputs).toPrefix.KL (.inr b) := by
    refine (Finset.sum_filter_of_ne fun b _ hne => ?_).symm
    by_contra h
    exact hne (KL_upper _ _ b (by simpa using h))
  unfold midOthersK1
  rw [hsplit]
  have hblk := Finset.sum_le_sum fun b (hb : b ∈ univ.filter
      (fun b => specUpper (specF hW A b) = false)) =>
    block_le C P κ hN hκP L b (Finset.mem_filter.mp hb).2
  have h2 : ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = false),
      (midBound (fun i => noFoldConsts (κ i)) b + foldSite dL dR b) =
      ∑ b, (midBound (fun i => noFoldConsts (κ i)) b + foldSite dL dR b) := by
    refine Finset.sum_filter_of_ne fun b _ hne => ?_
    by_contra h
    have hu : specUpper (specF hW A b) = true := by simpa using h
    exact hne (by rw [MainFinalF1.midBound_upper _ b hu, foldSite_upper dL dR b hu, add_zero])
  rw [sum_add_distrib, h2] at hblk
  have h5 : ∑ b, (midBound (fun i => noFoldConsts (κ i)) b + foldSite dL dR b) =
      ∑ b, midBound (fun i => noFoldConsts (κ i)) b + ∑ b, foldSite dL dR b := sum_add_distrib
  have h3 := sum_midBound_le hB hRR κ hκ
  have h4 := sum_foldSite_le hB hRR P.gateL P.gateR
  linarith

end Sarkozy.MiddleRefinement
