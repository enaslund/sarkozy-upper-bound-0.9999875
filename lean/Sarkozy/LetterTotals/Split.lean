module

public import Sarkozy.MainFinalF1.Env
public import Sarkozy.NumericalFields.Signs

@[expose] public section

/-!
# The symmetric and the skew totals apart (HX)

HX, 8 November 2026. `def:closing-quantities`, `def:cp4`(b); `lem:middle-comparison-prices`;
`prop:record:upper`(ii); `lem:record:block-charge`; `lem:frontier:iidenergy`(iii);
`lem:tail-prices`(iv).

The chain that proves `hSA` (K1's `SAExplicit_fullF1`, B2's `SAExplicit_of_ranges`) bounds the
**sum** `S + A` of the formal totals: B7's `price_sum_le` and B2's `upper_blocks_le_of_bands` add
the symmetric and the skew bound of each block before summing. The per-block bounds themselves are
separate (B7's `Replacements.prices_le`, K1's `specUpper_prices_le`). Here the same chain is run
twice, once per change type, at any `MainFinalF1.ComparisonParts C`:

* `midPolyS`, `midPolyA`: the symmetric and skew halves of K1's `midPoly`
  (`(S₂ r² + S₃ r³ + S₄ r⁴ + S₅ r⁵)` and `(A₂ r² + A₃ r³ + A₄ r⁴)`, `midPoly_split`);
  `specParts_le`: B7's `prices_le` at any block specification;
* `blockParts_le`: at a block of piece `i`, `s_𝔅 ≤ midPolyS(…) q_𝔅^{2a}` and
  `a_𝔅 ≤ midPolyA(…) q_𝔅^{2a}`;
* `middle_sprice_le`, `middle_aprice_le`: the middle blocks grouped by piece, with the charges of
  N2 (`f1_charge_le`, `blockCharge_shift`): `∑ s_𝔅 ≤ middleS κ`, `∑ a_𝔅 ≤ middleA κ`;
* `upper_parts_le`: the upper blocks by bands (`band_sum_le` per change type, `thm:bmor`):
  `∑ s_𝔅 ≤ upperS`, `∑ a_𝔅 ≤ upperA`;
* **`symTotal_le`**, **`skewTotal_le`**: at every scale,
  `∑_𝔟 s_𝔟 ≤ H + upperS + middleS κ + S_tail` and `∑_𝔟 a_𝔟 ≤ H + upperA + middleA κ + A_tail`
  (the clique atoms enter both with their whole price `≤ H`);
* `upperS_add_upperA` (`= Uup`), `middleS_add_middleA` (`=` the middle term of `hsum`): the two
  bounds add up to the terms of `hSA`'s numerical inequality, so this is a split of the proved
  chain, not a new estimate.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.LetterTotals

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec paperAtomMap PaperAtom PrefixCoord)
open Sarkozy.MiddleRecords (coefS2 coefS3 coefS4 coefS5 coefA2 coefA3 coefA4 gS gA rXof)
open Sarkozy.UpperComparison (upperFate upperLedger polyEval upperDegrees band_sum_le)
open Sarkozy.MiddleComparison (SpecData SpecInputs ReplacementData)
open Sarkozy.ComparisonLawPaper (BlockInputs specUpper upperBand blockSel)
open Sarkozy.MainFinal (MiddleConsts SpecNorm SpecShape specUpper_prices_le pieceScale
  pieceScale_nonneg specCoefS specCoefA specR)
open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk bandIdx paperSpec_facts
  paperSpec_upper_facts blockSite_of_upper blockScale_eq_inv_sqrt blockCharge_shift
  upperBand_le_bandBound)
open Sarkozy.NumericalFields (KappaNonneg qX_mem gS_nonneg gA_nonneg bandBound)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3 f1_charge_le)
open Sarkozy.EnvPrefix (Uup)

/-! ## The two halves of the middle price polynomial -/

/-- The symmetric half `S₂ r² + S₃ r³ + S₄ r⁴ + S₅ r⁵` of K1's `midPoly` (`r = b^{-1/2}`). -/
noncomputable def midPolyS (W : MiddleWeights) (I : MiddleInputs) (κ : MiddleConsts) (X : ℕ)
    (b : ℝ) : ℝ :=
  coefS2 W κ.sE * (1 / Real.sqrt b) ^ 2 + coefS3 W I κ.sF * (1 / Real.sqrt b) ^ 3 +
    coefS4 W (gS (1 / (X : ℝ))) * (1 / Real.sqrt b) ^ 4 +
    coefS5 W (1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 5

/-- The skew half `A₂ r² + A₃ r³ + A₄ r⁴` of K1's `midPoly`. -/
noncomputable def midPolyA (W : MiddleWeights) (κ : MiddleConsts) (X : ℕ) (b : ℝ) : ℝ :=
  coefA2 W κ.ℓ κ.aE * (1 / Real.sqrt b) ^ 2 +
    coefA3 W κ.aF (gA (1 / (X : ℝ)) (rXof X)) * (1 / Real.sqrt b) ^ 3 +
    coefA4 W (1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 4

/-- K1's `midPoly` is the sum of the two halves. -/
theorem midPoly_split (W : MiddleWeights) (I : MiddleInputs) (κ : MiddleConsts) (X : ℕ) (b : ℝ) :
    MainFinal.midPoly W I κ X b = midPolyS W I κ X b + midPolyA W κ X b := rfl

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} (hW : Target.Weil)
  (In : FirstStageInputs blockOf)

/-- The symmetric middle bound of a specification (`0` on an upper block). -/
noncomputable def specMidS {b : B} (κ : MiddleConsts) (X : ℕ) (bl sel : ℝ) :
    PaperBlockSpec blockOf b → ℝ
  | .upper _ => 0
  | .middleUniform M => midPolyS M.W M.I κ X bl * sel
  | .middleIndividual M => midPolyS M.W M.I κ X bl * sel
  | .middleCoherent M => midPolyS M.W M.I κ X bl * sel

/-- The skew middle bound of a specification (`0` on an upper block). -/
noncomputable def specMidA {b : B} (κ : MiddleConsts) (X : ℕ) (bl sel : ℝ) :
    PaperBlockSpec blockOf b → ℝ
  | .upper _ => 0
  | .middleUniform M => midPolyA M.W κ X bl * sel
  | .middleIndividual M => midPolyA M.W κ X bl * sel
  | .middleCoherent M => midPolyA M.W κ X bl * sel

omit [Fintype B] in
/-- **`lem:middle-comparison-prices` for one middle block, per change type**: B7's
`Replacements.prices_le` at the constructed atom (K1's `specPrice_le` before the two bounds are
added). -/
theorem specParts_le {b : B} (κ : MiddleConsts) {X : ℕ} {bl sel : ℝ} (hX : 4 ≤ X)
    (hb : (X : ℝ) ≤ bl) (hsel : 0 ≤ sel) :
    ∀ (S : PaperBlockSpec blockOf b) (R : SpecData hW In S), specUpper S = false →
      SpecShape bl S → SpecNorm hW In κ bl S R →
      (BlockInputs.toAtom hW In S (SpecInputs.toBlockInputs hW In S
          (SpecData.toSpecInputs hW In S R))).sprice sel ≤ specMidS κ X bl sel S ∧
        (BlockInputs.toAtom hW In S (SpecInputs.toBlockInputs hW In S
          (SpecData.toSpecInputs hW In S R))).aprice sel ≤ specMidA κ X bl sel S
  | .upper _, _, h, _, _ => absurd h (by simp [specUpper])
  | .middleUniform M, R, _, ⟨hr, hfh⟩, ⟨hFs, hFa, hEs, hEa, hM, hCs, hCa⟩ =>
    (ReplacementData.toReplacements R.down).prices_le (MiddleComparison.factsU In M) hX hb hr
      hsel hfh hFs hFa hEs hEa hM hCs hCa
  | .middleIndividual M, R, _, ⟨hr, hfh⟩, ⟨hFs, hFa, hEs, hEa, hM, hCs, hCa⟩ =>
    (ReplacementData.toReplacements R.down).prices_le (MiddleComparison.factsI In M) hX hb hr
      hsel hfh hFs hFa hEs hEa hM hCs hCa
  | .middleCoherent M, R, _, ⟨hr, hfh⟩, ⟨hFs, hFa, hEs, hEa, hM, hCs, hCa⟩ =>
    (ReplacementData.toReplacements R.down).prices_le (MiddleComparison.factsC In M) hX hb hr
      hsel hfh hFs hFa hEs hEa hM hCs hCa

end Generic

/-! ## The paper's blocks -/

section Paper

variable (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)

theorem middleSpec_split (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (κ : MiddleConsts)
    (X : ℕ) (sel : ℝ) : ∀ o hu,
      specMidS κ X (blockLeast b) sel (middleSpec hW A b i hs o hu) =
          midPolyS (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel ∧
        specMidA κ X (blockLeast b) sel (middleSpec hW A b i hs o hu) =
          midPolyA (allpWeights i) κ X (blockLeast b) * sel
  | none, _ => ⟨rfl, rfl⟩
  | some _, _ => ⟨rfl, rfl⟩

theorem siteSpec_split (b : Blk) (i : Fin 33) (κ : MiddleConsts) (X : ℕ) (sel : ℝ) :
    ∀ s (hs : blockSite b = s), s = .inl i →
      specMidS κ X (blockLeast b) sel (siteSpec hW A b s hs) =
          midPolyS (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel ∧
        specMidA κ X (blockLeast b) sel (siteSpec hW A b s hs) =
          midPolyA (allpWeights i) κ X (blockLeast b) * sel
  | .inl j, hs, h => by
    obtain rfl : j = i := Sum.inl.inj h
    exact middleSpec_split hW A b j hs κ X sel _ rfl
  | .inr _, _, h => absurd h (by simp)

/-- At a block of piece `i`, the two middle bounds are the halves of the piece's polynomial. -/
theorem paperSpec_split (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (κ : MiddleConsts)
    (X : ℕ) (sel : ℝ) :
    specMidS κ X (blockLeast b) sel (specF hW A b) =
        midPolyS (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel ∧
      specMidA κ X (blockLeast b) sel (specF hW A b) =
        midPolyA (allpWeights i) κ X (blockLeast b) * sel :=
  siteSpec_split hW A b i κ X sel _ rfl hs

variable {hW A} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **`lem:middle-comparison-prices` at a block of piece `i`, per change type**:
`s_𝔅 ≤ midPolyS(…) q_𝔅^{2a_T}` and `a_𝔅 ≤ midPolyA(…) q_𝔅^{2a_T}` (K1's `blockPrice_le` before the
two bounds are added). -/
theorem blockParts_le (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts) (b : Blk)
    (i : Fin 33) (hs : blockSite b = .inl i)
    (hN : SpecNorm hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)) :
    (C.Ci.blockAtom b).sprice (blockSel bOf b) ≤
        midPolyS (allpWeights i) (allpInputs i) (κ i) (pieceStart i) (blockLeast b) *
          blockSel bOf b ∧
      (C.Ci.blockAtom b).aprice (blockSel bOf b) ≤
        midPolyA (allpWeights i) (κ i) (pieceStart i) (blockLeast b) * blockSel bOf b := by
  obtain ⟨hu, hsh, -⟩ := paperSpec_facts hW A b i hs (κ i) (pieceStart i) (blockSel bOf b)
  have hX : 4 ≤ pieceStart i := le_trans (by norm_num [PartV.Q3]) (pieceStart_ge_Q3 i)
  have hb : (pieceStart i : ℝ) ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact_mod_cast h
  have hsel : 0 ≤ blockSel bOf b :=
    le_trans zero_le_one (one_le_paperSelAt (paperAtomMap bOf) targetDecay_nonneg _)
  have h := specParts_le hW (paperIn f1Cell) (κ i) hX hb hsel (specF hW A b) (C.blk b) hu hsh hN
  obtain ⟨eS, eA⟩ := paperSpec_split hW A b i hs (κ i) (pieceStart i) (blockSel bOf b)
  rw [eS, eA] at h
  exact h

/-! ## The middle blocks, grouped by piece -/

/-- `S₂(i) = 2 w_S s_E`. -/
noncomputable def midS2 (κ : Fin 33 → MiddleConsts) (i : Fin 33) : ℝ :=
  coefS2 (allpWeights i) (κ i).sE
/-- `S₃(i) = 2 w_D s_F + 6 v_R + 2 v_D (f₁ + h₁)`. -/
noncomputable def midS3 (κ : Fin 33 → MiddleConsts) (i : Fin 33) : ℝ :=
  coefS3 (allpWeights i) (allpInputs i) (κ i).sF
/-- `S₄(i) = 2 v_C + w_R g_S`. -/
noncomputable def midS4 (i : Fin 33) : ℝ := coefS4 (allpWeights i) (gS (1 / (pieceStart i : ℝ)))
/-- `S₅(i) = 2 w_C/(1 − q_X)²`. -/
noncomputable def midS5 (i : Fin 33) : ℝ := coefS5 (allpWeights i) (1 / (pieceStart i : ℝ))
/-- `A₂(i) = 2 w_D ℓ_t + 2 w_S a_E`. -/
noncomputable def midA2 (κ : Fin 33 → MiddleConsts) (i : Fin 33) : ℝ :=
  coefA2 (allpWeights i) (κ i).ℓ (κ i).aE
/-- `A₃(i) = 2 w_D a_F + w_R g_A`. -/
noncomputable def midA3 (κ : Fin 33 → MiddleConsts) (i : Fin 33) : ℝ :=
  coefA3 (allpWeights i) (κ i).aF (gA (1 / (pieceStart i : ℝ)) (rXof (pieceStart i)))
/-- `A₄(i) = 2 w_C/(1 − q_X)`. -/
noncomputable def midA4 (i : Fin 33) : ℝ := coefA4 (allpWeights i) (1 / (pieceStart i : ℝ))

/-- The signs of the split coefficients, for nonnegative constants (E2's `midK2_nonneg` …
`midK5_nonneg`, before the halves are added). -/
theorem mid_split_signs (κ : Fin 33 → MiddleConsts) (i : Fin 33) (h : KappaNonneg (κ i)) :
    (0 ≤ midS2 κ i ∧ 0 ≤ midS3 κ i ∧ 0 ≤ midS4 i ∧ 0 ≤ midS5 i) ∧
      (0 ≤ midA2 κ i ∧ 0 ≤ midA3 κ i ∧ 0 ≤ midA4 i) := by
  obtain ⟨hsF, haF, hℓ, hsE, haE⟩ := h
  have hq := qX_mem i
  have a3 : 0 < 1 - 1 / (pieceStart i : ℝ) := by linarith [hq.2]
  have hwS := (allpWeights i).w_nonneg .S
  have hwD := (allpWeights i).w_nonneg .D
  have hwR := (allpWeights i).w_nonneg .R
  have hwC := (allpWeights i).w_nonneg .C
  have hvR := (allpWeights i).v_nonneg .R
  have hvD := (allpWeights i).v_nonneg .D
  have hvC := (allpWeights i).v_nonneg .C
  have hf := (allpInputs_nonneg i).2.2.1
  have hh := (allpInputs_nonneg i).2.2.2.2.1
  have hgS := gS_nonneg i
  have hgA := gA_nonneg i
  unfold midS2 midS3 midS4 midS5 midA2 midA3 midA4 coefS2 coefS3 coefS4 coefS5 coefA2 coefA3
    coefA4
  refine ⟨⟨by positivity, by positivity, by positivity, by positivity⟩,
    ⟨by positivity, by positivity, by positivity⟩⟩

theorem midPolyS_eq (κ : Fin 33 → MiddleConsts) (i : Fin 33) (b : Blk) :
    midPolyS (allpWeights i) (allpInputs i) (κ i) (pieceStart i) (blockLeast b) =
      midS2 κ i * BlockSpecPaper.blockScale b ^ 2 + midS3 κ i * BlockSpecPaper.blockScale b ^ 3 +
        midS4 i * BlockSpecPaper.blockScale b ^ 4 + midS5 i * BlockSpecPaper.blockScale b ^ 5 := by
  rw [blockScale_eq_inv_sqrt]
  rfl

theorem midPolyA_eq (κ : Fin 33 → MiddleConsts) (i : Fin 33) (b : Blk) :
    midPolyA (allpWeights i) (κ i) (pieceStart i) (blockLeast b) =
      midA2 κ i * BlockSpecPaper.blockScale b ^ 2 + midA3 κ i * BlockSpecPaper.blockScale b ^ 3 +
        midA4 i * BlockSpecPaper.blockScale b ^ 4 := by
  rw [blockScale_eq_inv_sqrt]
  rfl

/-- The charge `b_d(i) = ∑_{𝔅 ⊆ piece i} r_𝔅^d q_𝔅^{2a_T}`. -/
noncomputable abbrev chg (d : ℕ) (i : Fin 33) : ℝ :=
  blockCharge (fun b : Blk => paperSelAt (paperAtomMap bOf) targetDecay (.inr b)) d i

/-- **Grouping a per-block polynomial bound by piece** (`lem:record:block-charge`): if every
middle block of piece `i` has `f_𝔅 ≤ (∑_{d ∈ D} k_d(i) r_𝔅^d) q_𝔅^{2a_T}`, then
`∑_{𝔅 middle} f_𝔅 ≤ ∑_i ∑_{d ∈ D} k_d(i) b_d(i)`. -/
theorem middle_sum_le (f : Blk → ℝ) (Ds : Finset ℕ) (k : ℕ → Fin 33 → ℝ)
    (hf : ∀ b i, blockSite b = .inl i →
      f b ≤ (∑ d ∈ Ds, k d i * BlockSpecPaper.blockScale b ^ d) * blockSel bOf b)
    (hup : ∀ b, specUpper (specF hW A b) = false → ∃ i, blockSite b = .inl i) :
    ∑ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true), f b ≤
      ∑ i : Fin 33, ∑ d ∈ Ds, k d i * chg d i := by
  have hsub : univ.filter (fun b => ¬ specUpper (specF hW A b) = true) ⊆
      univ.filter (fun b : Blk => ∃ i, blockSite b = .inl i) := by
    intro b hb
    rw [mem_filter] at hb ⊢
    exact ⟨mem_univ _, hup b (by simpa using hb.2)⟩
  have hmaps : ∀ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true),
      (match blockSite b with | .inl i => i | .inr _ => 0) ∈ (univ : Finset (Fin 33)) :=
    fun _ _ => mem_univ _
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun i _ => ?_
  calc ∑ b ∈ (univ.filter fun b => ¬ specUpper (specF hW A b) = true).filter
          (fun b => (match blockSite b with | .inl i => i | .inr _ => 0) = i), f b
      ≤ ∑ b ∈ (univ.filter fun b => ¬ specUpper (specF hW A b) = true).filter
          (fun b => (match blockSite b with | .inl i => i | .inr _ => 0) = i),
          (∑ d ∈ Ds, k d i * BlockSpecPaper.blockScale b ^ d) * blockSel bOf b := by
        refine sum_le_sum fun b hb => ?_
        rw [mem_filter, mem_filter] at hb
        obtain ⟨j, hj⟩ := hup b (by simpa using hb.1.2)
        have hji : j = i := by
          have := hb.2
          rw [hj] at this
          exact this
        rw [hji] at hj
        exact hf b i hj
    _ ≤ ∑ b ∈ univ.filter (fun b : Blk => blockSite b = .inl i),
          (∑ d ∈ Ds, k d i * BlockSpecPaper.blockScale b ^ d) * blockSel bOf b := by
        refine le_of_eq (sum_congr ?_ fun _ _ => rfl)
        ext b
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨j, hj⟩ := hup b (by simpa using h1)
          rw [hj] at h2 ⊢
          simp only at h2
          rw [h2]
        · intro h
          refine ⟨?_, by rw [h]⟩
          rw [(paperSpec_facts hW A b i h ⟨0, 0, 0, 0, 0⟩ 0 0).1]
          decide
    _ = ∑ d ∈ Ds, k d i * chg d i := by
        unfold chg blockCharge
        simp_rw [sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun d _ => sum_congr rfl fun b _ => ?_
        ring

/-- A block whose specification is not upper lies in a piece. -/
theorem site_of_not_upper (b : Blk) (hb : specUpper (specF hW A b) = false) :
    ∃ i, blockSite b = .inl i := by
  rcases h : blockSite b with i | k
  · exact ⟨i, rfl⟩
  · exact absurd (MainFinalF1.paperSpec_upper hW A b k h) (by rw [hb]; decide)

/-- The symmetric coefficient `S_d(i)` by degree. -/
noncomputable def kS (κ : Fin 33 → MiddleConsts) : ℕ → Fin 33 → ℝ
  | 2, i => midS2 κ i
  | 3, i => midS3 κ i
  | 4, i => midS4 i
  | _, i => midS5 i

/-- The skew coefficient `A_d(i)` by degree. -/
noncomputable def kA (κ : Fin 33 → MiddleConsts) : ℕ → Fin 33 → ℝ
  | 2, i => midA2 κ i
  | 3, i => midA3 κ i
  | _, i => midA4 i

/-- **The middle blocks' symmetric prices** (`lem:middle-comparison-prices`,
`lem:record:block-charge`): `∑_{𝔅 middle} s_𝔅 ≤ ∑_i ∑_{d=2}^5 S_d(i) b_d(i)`. -/
theorem middle_sprice_charges (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts)
    (hN : C.MiddleNorms hW A κ) :
    ∑ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true),
        (C.Ci.blockAtom b).sprice (blockSel bOf b) ≤
      ∑ i : Fin 33, (midS2 κ i * chg 2 i + midS3 κ i * chg 3 i + midS4 i * chg 4 i +
        midS5 i * chg 5 i) := by
  have hD : ∀ (g : ℕ → ℝ), ∑ d ∈ ({2, 3, 4, 5} : Finset ℕ), g d = g 2 + g 3 + g 4 + g 5 := by
    intro g
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    ring
  refine (middle_sum_le (hW := hW) (A := A) _ {2, 3, 4, 5} (kS κ) (fun b i hs => ?_)
    (site_of_not_upper (hW := hW) (A := A))).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
  · refine ((blockParts_le C κ b i hs (hN b i hs)).1).trans (le_of_eq ?_)
    rw [midPolyS_eq, hD]
    rfl
  · rw [hD]
    rfl

/-- **The middle blocks' skew prices**: `∑_{𝔅 middle} a_𝔅 ≤ ∑_i ∑_{d=2}^4 A_d(i) b_d(i)`. -/
theorem middle_aprice_charges (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts)
    (hN : C.MiddleNorms hW A κ) :
    ∑ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true),
        (C.Ci.blockAtom b).aprice (blockSel bOf b) ≤
      ∑ i : Fin 33, (midA2 κ i * chg 2 i + midA3 κ i * chg 3 i + midA4 i * chg 4 i) := by
  have hD : ∀ (g : ℕ → ℝ), ∑ d ∈ ({2, 3, 4} : Finset ℕ), g d = g 2 + g 3 + g 4 := by
    intro g
    rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
    ring
  refine (middle_sum_le (hW := hW) (A := A) _ {2, 3, 4} (kA κ) (fun b i hs => ?_)
    (site_of_not_upper (hW := hW) (A := A))).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
  · refine ((blockParts_le C κ b i hs (hN b i hs)).2).trans (le_of_eq ?_)
    rw [midPolyA_eq, hD]
    rfl
  · rw [hD]
    rfl

/-- **The symmetric middle total** at N2's charges `f1c2`, `f1c3` (with `b₄ ≤ X_i^{-1/2} b₃`,
`b₅ ≤ X_i^{-1} b₃`). -/
noncomputable def middleS (κ : Fin 33 → MiddleConsts) : ℝ :=
  ∑ i : Fin 33, (midS2 κ i * f1c2 i +
    (midS3 κ i + midS4 i * pieceScale i + midS5 i * pieceScale i ^ 2) * f1c3 i)

/-- **The skew middle total** at N2's charges. -/
noncomputable def middleA (κ : Fin 33 → MiddleConsts) : ℝ :=
  ∑ i : Fin 33, (midA2 κ i * f1c2 i + (midA3 κ i + midA4 i * pieceScale i) * f1c3 i)

/-- The two middle totals add up to the middle term of `hSA`'s numerical inequality. -/
theorem middleS_add_middleA (κ : Fin 33 → MiddleConsts) :
    middleS κ + middleA κ = ∑ i : Fin 33, (MainFinal.midK2 κ i * f1c2 i +
      (MainFinal.midK3 κ i + MainFinal.midK4 i * pieceScale i +
        MainFinal.midK5 i * pieceScale i ^ 2) * f1c3 i) := by
  unfold middleS middleA
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  unfold midS2 midS3 midS4 midS5 midA2 midA3 midA4 MainFinal.midK2 MainFinal.midK3
    MainFinal.midK4 MainFinal.midK5
  ring

/-- The charges `b₂ ≤ f1c2`, `b₃ ≤ f1c3`, `b₄ ≤ X_i^{-1/2} f1c3`, `b₅ ≤ X_i^{-1} f1c3`
(`thm:bmor`, `ThetaSmallRR`; N2's `f1_charge_le`, K1's `blockCharge_shift`). -/
theorem chg_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) (i : Fin 33) :
    chg 2 i ≤ f1c2 i ∧ chg 3 i ≤ f1c3 i ∧ chg 4 i ≤ pieceScale i * f1c3 i ∧
      chg 5 i ≤ pieceScale i ^ 2 * f1c3 i := by
  have h₂ := (f1_charge_le hB hRR i).1
  have h₃ := (f1_charge_le hB hRR i).2
  refine ⟨h₂, h₃, ?_, ?_⟩
  · have := (blockCharge_shift i 3 1).trans
      (mul_le_mul_of_nonneg_left h₃ (pow_nonneg (pieceScale_nonneg i) 1))
    simpa using this
  · exact (blockCharge_shift i 3 2).trans
      (mul_le_mul_of_nonneg_left h₃ (pow_nonneg (pieceScale_nonneg i) 2))

/-- **`∑_{𝔅 middle} s_𝔅 ≤ middleS κ`**. -/
theorem middle_sprice_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts)
    (hκ : ∀ i, KappaNonneg (κ i)) (hN : C.MiddleNorms hW A κ) :
    ∑ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true),
        (C.Ci.blockAtom b).sprice (blockSel bOf b) ≤ middleS κ := by
  refine (middle_sprice_charges C κ hN).trans (sum_le_sum fun i _ => ?_)
  obtain ⟨⟨s2, s3, s4, s5⟩, -⟩ := mid_split_signs κ i (hκ i)
  obtain ⟨c2, c3, c4, c5⟩ := chg_le hB hRR i
  have := mul_le_mul_of_nonneg_left c2 s2
  have := mul_le_mul_of_nonneg_left c3 s3
  have := mul_le_mul_of_nonneg_left c4 s4
  have := mul_le_mul_of_nonneg_left c5 s5
  nlinarith

/-- **`∑_{𝔅 middle} a_𝔅 ≤ middleA κ`**. -/
theorem middle_aprice_le (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts)
    (hκ : ∀ i, KappaNonneg (κ i)) (hN : C.MiddleNorms hW A κ) :
    ∑ b ∈ univ.filter (fun b => ¬ specUpper (specF hW A b) = true),
        (C.Ci.blockAtom b).aprice (blockSel bOf b) ≤ middleA κ := by
  refine (middle_aprice_charges C κ hN).trans (sum_le_sum fun i _ => ?_)
  obtain ⟨-, ⟨a2, a3, a4⟩⟩ := mid_split_signs κ i (hκ i)
  obtain ⟨c2, c3, c4, -⟩ := chg_le hB hRR i
  have := mul_le_mul_of_nonneg_left c2 a2
  have := mul_le_mul_of_nonneg_left c3 a3
  have := mul_le_mul_of_nonneg_left c4 a4
  nlinarith

end Paper

end Sarkozy.LetterTotals
