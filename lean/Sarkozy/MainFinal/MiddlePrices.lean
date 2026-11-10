module

public import Sarkozy.MainFinal.Main
public import Sarkozy.MiddleComparison.Prices

@[expose] public section

/-!
# The middle part of `hSA` at the paper's blocks (`lem:middle-comparison-prices`)

`paper/sections/21_middle_records.tex`, `lem:middle-comparison-prices`.

B2's `SAExplicit_of_bands` takes, for every middle block, a bound `s_𝔅 + a_𝔅 ≤ M_𝔅` (its
hypothesis `hm`). B7's `Replacements.price_sum_le` gives such a bound for one constructed middle
atom from the paper's per-record norm sizes. Here the two are joined at the paper's blocks:

* `NormSizes`: the per-record norm sizes of `lem:middle-comparison-prices` for the twelve changes
  of a middle block (`prop:signed-bounds`(a),(b),(e) with the constants `s_F, a_F, ℓ_t` of
  `eq:signed-constants`; `lem:record:exact-marginal-e`(ii) with `s_E, a_E`; the table of
  `lem:merge-repair`; `lem:record:accepting-c2`), at the least prime `b` of the block;
* `specPrice_le` (any block specification): the price of the constructed middle atom is at most
  `midPoly W I κ X b · sel`, the price polynomial of `lem:middle-comparison-prices` at
  `r = b^{-1/2}`;
* `paper_blockPrice_le`: for a block of piece `i` of the paper's partition,
  `s_𝔅 + a_𝔅 ≤ midPoly(allpWeights i, allpInputs i, κ i, X_i, b_𝔅) · q_𝔅^{2a_T}`; the shape
  conditions (`r = b^{-1/2}`, `f₁ + h₁ ≥ 0`, `X_i ≤ b_𝔅`) are proved from B1's construction;
* `sum_midBound`: the middle bounds grouped by piece,
  `∑_𝔅 M_𝔅 = ∑_i ∑_{d=2}^{5} K_d(i) b_d(i)` with B1's block charges `b_d(i)` and the coefficients
  `K_d(i)` of `lem:middle-comparison-prices`;
* `SAExplicit_paper`: B2's `SAExplicit` for the combined data from the clique bound, B2's upper
  band inputs, the norm sizes of every middle block and one numerical inequality in the per-piece
  charges.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MainFinal

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec paperAtomMap)
open Sarkozy.MiddleRecords (coefS2 coefS3 coefS4 coefS5 coefA2 coefA3 coefA4 gS gA rXof
  MergeRepairBounds)
open Sarkozy.MiddleComparison (SpecData SpecInputs ReplacementData)
open Sarkozy.ComparisonLawPaper (BlockInputs specUpper SAExplicit)

/-- **The constants of the middle comparison prices at a piece** (`lem:middle-comparison-prices`):
`s_F, a_F, ℓ_t` of `eq:signed-constants` (`prop:signed-bounds`) and `s_E, a_E` of
`lem:record:exact-marginal-e`(ii), evaluated at the piece start. Data. -/
structure MiddleConsts where
  sF : ℝ
  aF : ℝ
  ℓ : ℝ
  sE : ℝ
  aE : ℝ

/-- **The per-record norm sizes of the twelve changes of a middle block**
(`lem:middle-comparison-prices`, proof): the folds by `prop:signed-bounds`(a),(b),(e), the
matchings by `lem:record:exact-marginal-e`(ii), the merges by the table of `lem:merge-repair`, the
constants by `lem:record:accepting-c2`; `b` is the least prime and `r` the scale. *Hypothesis*
(analytic; the sizes of the norms `N` of B7's `ReplacementData`). -/
def NormSizes (N : MiddleComparison.Chg → ChangeType → ℝ) (κ : MiddleConsts) (b r : ℝ) : Prop :=
  (∀ i, N (.inl i) .sym ≤ κ.sF * (1 / Real.sqrt b) ^ 2) ∧
  (∀ i, N (.inl i) .skew ≤ κ.ℓ * (1 / Real.sqrt b) + κ.aF * (1 / Real.sqrt b) ^ 2) ∧
  (∀ i, N (.inr (.inl i)) .sym ≤ κ.sE * (1 / Real.sqrt b)) ∧
  (∀ i, N (.inr (.inl i)) .skew ≤ κ.aE * (1 / Real.sqrt b)) ∧
  MergeRepairBounds b (fun j => N (.inr (.inr (.inl j))) .sym)
    (fun j => N (.inr (.inr (.inl j))) .skew) ∧
  (∀ k, N (.inr (.inr (.inr k))) .sym ≤ r ^ 2 / (1 - 1 / b) ^ 2) ∧
  (∀ k, N (.inr (.inr (.inr k))) .skew ≤ r / (1 - 1 / b))

/-- **The price polynomial of a middle block** (`lem:middle-comparison-prices`):
`(S₂r² + S₃r³ + S₄r⁴ + S₅r⁵) + (A₂r² + A₃r³ + A₄r⁴)` at `r = b^{-1/2}`, with W6's coefficients
evaluated at the piece start `X` (`q_X = 1/X`, `r_X = 1/⌊√X⌋`). -/
noncomputable def midPoly (W : MiddleWeights) (I : MiddleInputs) (κ : MiddleConsts) (X : ℕ)
    (b : ℝ) : ℝ :=
  (coefS2 W κ.sE * (1 / Real.sqrt b) ^ 2 + coefS3 W I κ.sF * (1 / Real.sqrt b) ^ 3 +
      coefS4 W (gS (1 / (X : ℝ))) * (1 / Real.sqrt b) ^ 4 +
      coefS5 W (1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 5) +
    (coefA2 W κ.ℓ κ.aE * (1 / Real.sqrt b) ^ 2 +
      coefA3 W κ.aF (gA (1 / (X : ℝ)) (rXof X)) * (1 / Real.sqrt b) ^ 3 +
      coefA4 W (1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 4)

/-! ## Any block specification -/

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} (hW : Target.Weil)
  (In : FirstStageInputs blockOf)

/-- The comparison price `s_𝔅 + a_𝔅` of a class-three block with specification `S` and inputs
`R` (B7's atom through B2's `BlockInputs`). -/
noncomputable def specPrice {b : B} (S : PaperBlockSpec blockOf b) (R : SpecData hW In S)
    (sel : ℝ) : ℝ :=
  (BlockInputs.toAtom hW In S (SpecInputs.toBlockInputs hW In S
      (SpecData.toSpecInputs hW In S R))).sprice sel +
    (BlockInputs.toAtom hW In S (SpecInputs.toBlockInputs hW In S
      (SpecData.toSpecInputs hW In S R))).aprice sel

/-- The norm sizes of the inputs of a middle block (`True` on an upper block). -/
def SpecNorm {b : B} (κ : MiddleConsts) (bl : ℝ) :
    (S : PaperBlockSpec blockOf b) → SpecData hW In S → Prop
  | .upper _, _ => True
  | .middleUniform M, R => NormSizes R.down.N κ bl M.r
  | .middleIndividual M, R => NormSizes R.down.N κ bl M.r
  | .middleCoherent M, R => NormSizes R.down.N κ bl M.r

variable {hW In}

/-- The shape of a middle specification: `r = b^{-1/2}` and `f₁ + h₁ ≥ 0`. -/
def SpecShape {b : B} (bl : ℝ) : PaperBlockSpec blockOf b → Prop
  | .upper _ => True
  | .middleUniform M => M.r = 1 / Real.sqrt bl ∧ 0 ≤ M.I.f₁ + M.I.h₁
  | .middleIndividual M => M.r = 1 / Real.sqrt bl ∧ 0 ≤ M.I.f₁ + M.I.h₁
  | .middleCoherent M => M.r = 1 / Real.sqrt bl ∧ 0 ≤ M.I.f₁ + M.I.h₁

/-- The price bound of a middle specification (`0` on an upper block). -/
noncomputable def specMidBound {b : B} (κ : MiddleConsts) (X : ℕ) (bl sel : ℝ) :
    PaperBlockSpec blockOf b → ℝ
  | .upper _ => 0
  | .middleUniform M => midPoly M.W M.I κ X bl * sel
  | .middleIndividual M => midPoly M.W M.I κ X bl * sel
  | .middleCoherent M => midPoly M.W M.I κ X bl * sel

omit [Fintype B] in
variable (hW In) in
/-- **`lem:middle-comparison-prices` for one middle block, any root**: B7's `price_sum_le` at the
constructed atom, from the norm sizes and the shape. -/
theorem specPrice_le {b : B} (κ : MiddleConsts) {X : ℕ} {bl sel : ℝ} (hX : 4 ≤ X)
    (hb : (X : ℝ) ≤ bl) (hsel : 0 ≤ sel) :
    ∀ (S : PaperBlockSpec blockOf b) (R : SpecData hW In S), specUpper S = false →
      SpecShape bl S → SpecNorm hW In κ bl S R → specPrice hW In S R sel ≤
        specMidBound κ X bl sel S
  | .upper _, _, h, _, _ => absurd h (by simp [specUpper])
  | .middleUniform M, R, _, ⟨hr, hfh⟩, ⟨hFs, hFa, hEs, hEa, hM, hCs, hCa⟩ =>
    (ReplacementData.toReplacements R.down).price_sum_le (MiddleComparison.factsU In M) hX hb hr
      hsel hfh hFs hFa hEs hEa hM hCs hCa
  | .middleIndividual M, R, _, ⟨hr, hfh⟩, ⟨hFs, hFa, hEs, hEa, hM, hCs, hCa⟩ =>
    (ReplacementData.toReplacements R.down).price_sum_le (MiddleComparison.factsI In M) hX hb hr
      hsel hfh hFs hFa hEs hEa hM hCs hCa
  | .middleCoherent M, R, _, ⟨hr, hfh⟩, ⟨hFs, hFa, hEs, hEa, hM, hCs, hCa⟩ =>
    (ReplacementData.toReplacements R.down).price_sum_le (MiddleComparison.factsC In M) hX hb hr
      hsel hfh hFs hFa hEs hEa hM hCs hCa

end Generic

/-! ## The paper's blocks -/

section Paper

open Sarkozy.PaperNumbers (paperCell)

/-- The coefficient `K₂ = S₂ + A₂` of `r²` in `midPoly`. -/
noncomputable def midK2 (κ : Fin 33 → MiddleConsts) (i : Fin 33) : ℝ :=
  coefS2 (allpWeights i) (κ i).sE + coefA2 (allpWeights i) (κ i).ℓ (κ i).aE

/-- The coefficient `K₃ = S₃ + A₃` of `r³` in `midPoly`. -/
noncomputable def midK3 (κ : Fin 33 → MiddleConsts) (i : Fin 33) : ℝ :=
  coefS3 (allpWeights i) (allpInputs i) (κ i).sF +
    coefA3 (allpWeights i) (κ i).aF (gA (1 / (pieceStart i : ℝ)) (rXof (pieceStart i)))

/-- The coefficient `K₄ = S₄ + A₄` of `r⁴` in `midPoly`. -/
noncomputable def midK4 (i : Fin 33) : ℝ :=
  coefS4 (allpWeights i) (gS (1 / (pieceStart i : ℝ))) +
    coefA4 (allpWeights i) (1 / (pieceStart i : ℝ))

/-- The coefficient `K₅ = S₅` of `r⁵` in `midPoly`. -/
noncomputable def midK5 (i : Fin 33) : ℝ := coefS5 (allpWeights i) (1 / (pieceStart i : ℝ))

/-- `r_𝔅 = b_𝔅^{-1/2} = 1/√b_𝔅`. -/
theorem blockScale_eq_inv_sqrt (b : Blk) :
    BlockSpecPaper.blockScale b = 1 / Real.sqrt (blockLeast b : ℝ) := by
  unfold BlockSpecPaper.blockScale
  rw [BlockAdapter.rpow_neg_half_eq, one_div]

theorem midPoly_eq (κ : Fin 33 → MiddleConsts) (i : Fin 33) (b : Blk) :
    midPoly (allpWeights i) (allpInputs i) (κ i) (pieceStart i) (blockLeast b) =
      midK2 κ i * BlockSpecPaper.blockScale b ^ 2 + midK3 κ i * BlockSpecPaper.blockScale b ^ 3 +
        midK4 i * BlockSpecPaper.blockScale b ^ 4 + midK5 i * BlockSpecPaper.blockScale b ^ 5 := by
  rw [blockScale_eq_inv_sqrt]
  unfold midPoly midK2 midK3 midK4 midK5
  ring

variable (hW : Target.Weil) (A : PaperAnalyticInputs paperCell)

theorem middleSpec_facts (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (κ : MiddleConsts)
    (X : ℕ) (sel : ℝ) : ∀ o hu,
      specUpper (middleSpec hW A b i hs o hu) = false ∧
      SpecShape (blockLeast b : ℝ) (middleSpec hW A b i hs o hu) ∧
      specMidBound κ X (blockLeast b) sel (middleSpec hW A b i hs o hu) =
        midPoly (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel
  | none, _ => ⟨rfl, ⟨blockScale_eq_inv_sqrt b,
      add_nonneg (allpInputs_nonneg i).2.2.1 (allpInputs_nonneg i).2.2.2.2.1⟩, rfl⟩
  | some _, _ => ⟨rfl, ⟨blockScale_eq_inv_sqrt b,
      add_nonneg (allpInputs_nonneg i).2.2.1 (allpInputs_nonneg i).2.2.2.2.1⟩, rfl⟩

theorem siteSpec_facts (b : Blk) (i : Fin 33) (κ : MiddleConsts) (X : ℕ) (sel : ℝ) :
    ∀ s (hs : blockSite b = s), s = .inl i →
      specUpper (siteSpec hW A b s hs) = false ∧
      SpecShape (blockLeast b : ℝ) (siteSpec hW A b s hs) ∧
      specMidBound κ X (blockLeast b) sel (siteSpec hW A b s hs) =
        midPoly (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel
  | .inl j, hs, h => by
    obtain rfl : j = i := Sum.inl.inj h
    exact middleSpec_facts hW A b j hs κ X sel _ rfl
  | .inr _, _, h => absurd h (by simp)

/-- **A block of piece `i` has a middle specification** with B1's shape (`r = b^{-1/2}`,
`f₁ + h₁ ≥ 0` on ALLp) and the price bound `midPoly(allpWeights i, allpInputs i, …)`. -/
theorem paperSpec_facts (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (κ : MiddleConsts)
    (X : ℕ) (sel : ℝ) :
    specUpper (specF hW A b) = false ∧ SpecShape (blockLeast b : ℝ) (specF hW A b) ∧
      specMidBound κ X (blockLeast b) sel (specF hW A b) =
        midPoly (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel :=
  siteSpec_facts hW A b i κ X sel _ rfl hs

theorem siteSpec_upper (b : Blk) (k : Fin 310) :
    ∀ s (hs : blockSite b = s), s = .inr k → specUpper (siteSpec hW A b s hs) = true
  | .inr _, _, _ => rfl
  | .inl _, _, h => absurd h (by simp)

/-- A block of a band has an upper specification. -/
theorem paperSpec_upper (b : Blk) (k : Fin 310) (hs : blockSite b = .inr k) :
    specUpper (specF hW A b) = true :=
  siteSpec_upper hW A b k _ rfl hs

/-- The middle price bound at a site: `midPoly(…) · x` at piece `i`, `0` at a band. -/
noncomputable def siteMid (κ : Fin 33 → MiddleConsts) (b : Blk) (x : ℝ) : Site → ℝ
  | .inl i => midPoly (allpWeights i) (allpInputs i) (κ i) (pieceStart i) (blockLeast b) * x
  | .inr _ => 0

/-- **The middle price bound `M_𝔅` of a block** (`lem:middle-comparison-prices`) at
`x = q_𝔅^{2a_T}`; `0` on an upper block. -/
noncomputable def midBound (κ : Fin 33 → MiddleConsts) (b : Blk) : ℝ :=
  siteMid κ b (paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) (blockSite b)

/-- **The per-block norm sizes of the combined data**: `NormSizes` at every middle block of
piece `i`, with the piece's constants `κ i` and the block's least prime. *Hypothesis*
(analytic). -/
def ComparisonParts.MiddleNorms {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts) : Prop :=
  ∀ b i, blockSite b = .inl i →
    SpecNorm hW (paperIn paperCell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)

variable {hW A}

/-- **`lem:middle-comparison-prices` at a block of the paper's partition**:
`s_𝔅 + a_𝔅 ≤ midPoly(allpWeights i, allpInputs i, κ i, X_i, b_𝔅) q_𝔅^{2a_T}` from the norm sizes
of the block (B7's `price_sum_le`; the shape, `X_i ≤ b_𝔅` and `X_i ≥ 4` proved). -/
theorem ComparisonParts.blockPrice_le {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts) (b : Blk) (i : Fin 33)
    (hs : blockSite b = .inl i)
    (hN : SpecNorm hW (paperIn paperCell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)) :
    C.Ci.blockPrice b ≤ midPoly (allpWeights i) (allpInputs i) (κ i) (pieceStart i)
      (blockLeast b) * paperSelAt (paperAtomMap bOf) targetDecay (.inr b) := by
  obtain ⟨hu, hsh, hmid⟩ := paperSpec_facts hW A b i hs (κ i) (pieceStart i)
    (paperSelAt (paperAtomMap bOf) targetDecay (.inr b))
  have hX : 4 ≤ pieceStart i := le_trans (by norm_num [PartV.Q3]) (pieceStart_ge_Q3 i)
  have hb : (pieceStart i : ℝ) ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact_mod_cast h
  have hsel : 0 ≤ paperSelAt (paperAtomMap bOf) targetDecay (.inr b) :=
    le_trans zero_le_one (one_le_paperSelAt (paperAtomMap bOf) targetDecay_nonneg _)
  have h := specPrice_le hW (paperIn paperCell) (κ i) hX hb hsel (specF hW A b) (C.blk b) hu hsh hN
  rw [hmid] at h
  exact h

/-- **The middle blocks' prices** (`hm` of B2's `SAExplicit_of_ranges`): every class-three block
that is not upper has `s_𝔅 + a_𝔅 ≤ M_𝔅`. -/
theorem ComparisonParts.middle_le {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts) (hN : C.MiddleNorms hW A κ)
    (b : Blk) (hb : ¬ specUpper (specF hW A b) = true) : C.Ci.blockPrice b ≤ midBound κ b := by
  unfold midBound
  rcases h : blockSite b with i | k
  · exact C.blockPrice_le κ b i h (hN b i h)
  · exact absurd (paperSpec_upper hW A b k h) hb

/-- The middle bound vanishes on the upper blocks. -/
theorem midBound_upper (κ : Fin 33 → MiddleConsts) (b : Blk)
    (hb : specUpper (specF hW A b) = true) : midBound κ b = 0 := by
  unfold midBound
  rcases h : blockSite b with i | k
  · exact absurd hb (by rw [(paperSpec_facts hW A b i h (κ i) 0 0).1]; simp)
  · rfl

/-- **Grouping by piece** (`lem:record:block-charge`): `∑_𝔅 M_𝔅 = ∑_i ∑_{d=2}^{5} K_d(i) b_d(i)`
with B1's block charges `b_d(i) = ∑_{𝔅 ⊆ piece i} r_𝔅^d q_𝔅^{2a_T}`. -/
theorem sum_midBound (κ : Fin 33 → MiddleConsts) :
    ∑ b, midBound κ b = ∑ i : Fin 33,
      (midK2 κ i * blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 2 i +
        midK3 κ i * blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 3 i +
        midK4 i * blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 4 i +
        midK5 i *
          blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 5 i) := by
  set f : Blk → ℝ := fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b) with hf
  have hb : ∀ b : Blk, midBound κ b = ∑ i : Fin 33,
      if blockSite b = .inl i then
        (midK2 κ i * BlockSpecPaper.blockScale b ^ 2 + midK3 κ i * BlockSpecPaper.blockScale b ^ 3 +
          midK4 i * BlockSpecPaper.blockScale b ^ 4 + midK5 i * BlockSpecPaper.blockScale b ^ 5) *
            f b else 0 := by
    intro b
    unfold midBound
    rcases h : blockSite b with i | k
    · simp only [siteMid, Sum.inl.injEq]
      rw [Finset.sum_ite_eq, midPoly_eq]
      simp [hf]
    · simp [siteMid]
  simp_rw [hb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  unfold blockCharge
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **`hSA` in explicit form for the combined data** (`def:closing-quantities`, `def:cp4`(b),
`lem:middle-comparison-prices`, `lem:record:block-charge`): B2's `SAExplicit` from
* the square-clique bound `∑_p λ^ex_p(1) q_p^{2a} ≤ H` (`lem:frontier:iidenergy`(iii));
* the upper blocks `∑_{𝔅 upper}(s_𝔅 + a_𝔅) ≤ U` (B2's `upper_blocks_le_of_bands` from W8's band
  chain);
* the norm sizes of every middle block (`MiddleNorms`; analytic) with the piece constants `κ`;
* per-piece charge bounds `b_d(i) ≤ c_d(i)`, `d = 2, …, 5` (for `d = 2, 3` N1's certificates give
  `c_d = chargeC2, chargeC3`; `blockCharge_le_pieceBound` covers `d = 4`), the signs of the
  coefficients `K_d(i)`;
* the numerical inequality
  `H + U + ∑_i ∑_d K_d(i) c_d(i) + S_tail + A_tail ≤ S^{ledger} + A^{ledger}`.
The middle blocks' part (`hm` of `SAExplicit_of_ranges`) is **proved** from these. -/
theorem ComparisonParts.SAExplicit_paper {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) {H U : ℝ} (hq : ∑ q, C.Ci.cliquePrice q ≤ H)
    (hu : ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b ≤ U)
    (κ : Fin 33 → MiddleConsts) (hN : C.MiddleNorms hW A κ) {c₂ c₃ c₄ c₅ : Fin 33 → ℝ}
    (h₂ : ∀ i, blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 2 i ≤
      c₂ i)
    (h₃ : ∀ i, blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 3 i ≤
      c₃ i)
    (h₄ : ∀ i, blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 4 i ≤
      c₄ i)
    (h₅ : ∀ i, blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) 5 i ≤
      c₅ i)
    (hK : ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i)
    (hsum : H + U + ∑ i : Fin 33, (midK2 κ i * c₂ i + midK3 κ i * c₃ i + midK4 i * c₄ i +
      midK5 i * c₅ i) + (C.St + C.At) ≤ targetLedger.S + targetLedger.A) :
    SAExplicit C.Ci := by
  refine ComparisonLawPaper.SAExplicit_of_ranges C.Ci hq hu ?_ le_rfl hsum
  calc ∑ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true), C.Ci.blockPrice b
      ≤ ∑ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true), midBound κ b :=
        Finset.sum_le_sum fun b hb => C.middle_le κ hN b (Finset.mem_filter.mp hb).2
    _ = ∑ b, midBound κ b := by
        refine Finset.sum_filter_of_ne fun b _ hne => ?_
        intro hup
        exact hne (midBound_upper κ b hup)
    _ = _ := sum_midBound κ
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
        obtain ⟨k2, k3, k4, k5⟩ := hK i
        have := mul_le_mul_of_nonneg_left (h₂ i) k2
        have := mul_le_mul_of_nonneg_left (h₃ i) k3
        have := mul_le_mul_of_nonneg_left (h₄ i) k4
        have := mul_le_mul_of_nonneg_left (h₅ i) k5
        linarith

/-- `1/√X_i`, the largest scale of a block of piece `i`. -/
noncomputable def pieceScale (i : Fin 33) : ℝ := 1 / Real.sqrt (pieceStart i : ℝ)

theorem pieceScale_nonneg (i : Fin 33) : 0 ≤ pieceScale i := by
  unfold pieceScale
  positivity

/-- `r_𝔅 ≤ X_i^{-1/2}` on a block of piece `i`. -/
theorem blockScale_le_pieceScale (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) :
    BlockSpecPaper.blockScale b ≤ pieceScale i := by
  rw [blockScale_eq_inv_sqrt]
  unfold pieceScale
  have hX : (0 : ℝ) < pieceStart i := by
    have := pieceStart_ge_Q3 i
    have h0 : 0 < PartV.Q3 := by norm_num [PartV.Q3]
    exact_mod_cast lt_of_lt_of_le h0 this
  have hb : (pieceStart i : ℝ) ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact_mod_cast h
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt hb)

/-- **The higher charges from the lower ones**: `b_{d+k}(i) ≤ X_i^{-k/2} b_d(i)`. -/
theorem blockCharge_shift (i : Fin 33) (d k : ℕ) :
    blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) (d + k) i ≤
      pieceScale i ^ k *
        blockCharge (fun b => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) d i := by
  unfold blockCharge
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  have hs := (Finset.mem_filter.mp hb).2
  have hr0 : 0 ≤ BlockSpecPaper.blockScale b := (BlockSpecPaper.blockScale_pos b).le
  have hrk : BlockSpecPaper.blockScale b ^ k ≤ pieceScale i ^ k :=
    pow_le_pow_left₀ hr0 (blockScale_le_pieceScale b i hs) k
  have hf : 0 ≤ paperSelAt (paperAtomMap bOf) targetDecay (.inr b) :=
    le_trans zero_le_one (one_le_paperSelAt (paperAtomMap bOf) targetDecay_nonneg _)
  have hrd : 0 ≤ BlockSpecPaper.blockScale b ^ d := pow_nonneg hr0 d
  calc BlockSpecPaper.blockScale b ^ (d + k) * paperSelAt (paperAtomMap bOf) targetDecay (.inr b)
      = BlockSpecPaper.blockScale b ^ k * (BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) := by ring
    _ ≤ pieceScale i ^ k * (BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) :=
        mul_le_mul_of_nonneg_right hrk (mul_nonneg hrd hf)

/-- **`hSA` in explicit form with the middle charges from N1's 66 certificates**
(`SAExplicit_paper` with `c₂ = chargeC2`, `c₃ = chargeC3` from `NumericalCertificates` and H2
(`thm:bmor`), and `c₄ = X_i^{-1/2} c₃`, `c₅ = X_i^{-1} c₃` by `blockCharge_shift`). Remaining:
the clique bound `H`, the upper bound `U`, the middle norm sizes, the signs of `K_d(i)` and the
numerical inequality. -/
theorem ComparisonParts.SAExplicit_N1 (hBMOR : Target.BMOR) (NC : NumericalCertificates)
    {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) {H U : ℝ} (hq : ∑ q, C.Ci.cliquePrice q ≤ H)
    (hu : ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b ≤ U)
    (κ : Fin 33 → MiddleConsts) (hN : C.MiddleNorms hW A κ)
    (hK : ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i)
    (hsum : H + U + ∑ i : Fin 33, (midK2 κ i * (PaperNumbers.chargeC2 i : ℝ) +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        (PaperNumbers.chargeC3 i : ℝ)) + (C.St + C.At) ≤ targetLedger.S + targetLedger.A) :
    SAExplicit C.Ci := by
  have h₃ := NC.hb₃ hBMOR
  refine C.SAExplicit_paper hq hu κ hN (c₂ := fun i => (PaperNumbers.chargeC2 i : ℝ))
    (c₃ := fun i => (PaperNumbers.chargeC3 i : ℝ))
    (c₄ := fun i => pieceScale i ^ 1 * (PaperNumbers.chargeC3 i : ℝ))
    (c₅ := fun i => pieceScale i ^ 2 * (PaperNumbers.chargeC3 i : ℝ)) (NC.hb₂ hBMOR) h₃
    (fun i => (blockCharge_shift i 3 1).trans
      (mul_le_mul_of_nonneg_left (h₃ i) (pow_nonneg (pieceScale_nonneg i) 1)))
    (fun i => (blockCharge_shift i 3 2).trans
      (mul_le_mul_of_nonneg_left (h₃ i) (pow_nonneg (pieceScale_nonneg i) 2))) hK ?_
  refine le_trans (le_of_eq ?_) hsum
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Paper

end Sarkozy.MainFinal
