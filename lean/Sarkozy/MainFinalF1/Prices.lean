module

public import Sarkozy.MainFinalF1.Structure
public import Sarkozy.AnalyticCells.F1Main

@[expose] public section

/-!
# K1's middle and upper prices at `f1Cell` (F1P)

The paper-partition sections of K1's `MainFinal/MiddlePrices.lean` and `MainFinal/UpperPrices.lean`
with `paperCell` replaced by N2's `f1Cell` (`lem:middle-comparison-prices`,
`lem:record:block-charge`, `prop:record:upper`(ii), `def:closing-quantities`, `def:cp4`(b)). The
partition-independent definitions (`MiddleConsts`, `midPoly`, `SpecNorm`, `specPrice_le`, `midK2`–
`midK5`, `pieceScale`, `SpecUpperRec`, `specUpper_prices_le`, …) are K1's.

**Partition-dependent change.** K1's `SAExplicit_N1`/`SAExplicit_full` take N1's 66 numerical
certificates `NumericalCertificates` (the charges `b_d(i) ≤ c_d(i)` at `c = chargeC2, chargeC3`,
which at `paperCell` rest on `HistogramClaim`). At `f1Cell` the charges are **proved** from
`BMOR` and `ThetaSmallRR` (N2's `f1_charge_le`, `b_d(i) ≤ f1c2 i, f1c3 i`), so `SAExplicit_F1`,
`SAExplicit_fullF1` take `BMOR`, `ThetaSmallRR`, and the final numerical inequality is stated at
N2's numbers `f1c2`, `f1c3` in place of `chargeC2`, `chargeC3`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec paperAtomMap)
open Sarkozy.MiddleRecords (coefS2 coefS3 coefS4 coefS5 coefA2 coefA3 coefA4 gS gA rXof)
open Sarkozy.UpperComparison (upperFate upperLedger polyEval upperDegrees)
open Sarkozy.MiddleComparison (SpecData SpecInputs ReplacementData)
open Sarkozy.ComparisonLawPaper (BlockInputs specUpper SAExplicit upperBand blockSel)
open Sarkozy.MainFinal (MiddleConsts NormSizes specPrice SpecNorm SpecShape specMidBound
  specPrice_le midK2 midK3 midK4 midK5 pieceScale pieceScale_nonneg SpecUpperRec specCoefS specCoefA
  specR specUpper_prices_le)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3 f1_charge_le)

/-! ## Middle prices (K1's `MiddlePrices.lean`, paper section) -/

section Middle

/-- `r_𝔅 = b_𝔅^{-1/2} = 1/√b_𝔅`. -/
theorem blockScale_eq_inv_sqrt (b : Blk) :
    BlockSpecPaper.blockScale b = 1 / Real.sqrt (blockLeast b : ℝ) := by
  unfold BlockSpecPaper.blockScale
  rw [BlockAdapter.rpow_neg_half_eq, one_div]

theorem midPoly_eq (κ : Fin 33 → MiddleConsts) (i : Fin 33) (b : Blk) :
    MainFinal.midPoly (allpWeights i) (allpInputs i) (κ i) (pieceStart i) (blockLeast b) =
      midK2 κ i * BlockSpecPaper.blockScale b ^ 2 + midK3 κ i * BlockSpecPaper.blockScale b ^ 3 +
        midK4 i * BlockSpecPaper.blockScale b ^ 4 + midK5 i * BlockSpecPaper.blockScale b ^ 5 := by
  rw [blockScale_eq_inv_sqrt]
  unfold MainFinal.midPoly midK2 midK3 midK4 midK5
  ring

variable (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)

theorem middleSpec_facts (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) (κ : MiddleConsts)
    (X : ℕ) (sel : ℝ) : ∀ o hu,
      specUpper (middleSpec hW A b i hs o hu) = false ∧
      SpecShape (blockLeast b : ℝ) (middleSpec hW A b i hs o hu) ∧
      specMidBound κ X (blockLeast b) sel (middleSpec hW A b i hs o hu) =
        MainFinal.midPoly (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel
  | none, _ => ⟨rfl, ⟨blockScale_eq_inv_sqrt b,
      add_nonneg (allpInputs_nonneg i).2.2.1 (allpInputs_nonneg i).2.2.2.2.1⟩, rfl⟩
  | some _, _ => ⟨rfl, ⟨blockScale_eq_inv_sqrt b,
      add_nonneg (allpInputs_nonneg i).2.2.1 (allpInputs_nonneg i).2.2.2.2.1⟩, rfl⟩

theorem siteSpec_facts (b : Blk) (i : Fin 33) (κ : MiddleConsts) (X : ℕ) (sel : ℝ) :
    ∀ s (hs : blockSite b = s), s = .inl i →
      specUpper (siteSpec hW A b s hs) = false ∧
      SpecShape (blockLeast b : ℝ) (siteSpec hW A b s hs) ∧
      specMidBound κ X (blockLeast b) sel (siteSpec hW A b s hs) =
        MainFinal.midPoly (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel
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
        MainFinal.midPoly (allpWeights i) (allpInputs i) κ X (blockLeast b) * sel :=
  siteSpec_facts hW A b i κ X sel _ rfl hs

theorem siteSpec_upper (b : Blk) (k : Fin 310) :
    ∀ s (hs : blockSite b = s), s = .inr k → specUpper (siteSpec hW A b s hs) = true
  | .inr _, _, _ => rfl
  | .inl _, _, h => absurd h (by simp)

/-- A block of a band has an upper specification. -/
theorem paperSpec_upper (b : Blk) (k : Fin 310) (hs : blockSite b = .inr k) :
    specUpper (specF hW A b) = true :=
  siteSpec_upper hW A b k _ rfl hs

/-- The middle price bound at a site: `MainFinal.midPoly(…) · x` at piece `i`, `0` at a band. -/
noncomputable def siteMid (κ : Fin 33 → MiddleConsts) (b : Blk) (x : ℝ) : Site → ℝ
  | .inl i =>
      MainFinal.midPoly (allpWeights i) (allpInputs i) (κ i) (pieceStart i) (blockLeast b) * x
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
    SpecNorm hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)

variable {hW A}

/-- **`lem:middle-comparison-prices` at a block of the paper's partition**:
`s_𝔅 + a_𝔅 ≤ midPoly(allpWeights i, allpInputs i, κ i, X_i, b_𝔅) q_𝔅^{2a_T}` from the norm sizes
of the block (B7's `price_sum_le`; the shape, `X_i ≤ b_𝔅` and `X_i ≥ 4` proved). -/
theorem ComparisonParts.blockPrice_le {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (κ : Fin 33 → MiddleConsts) (b : Blk) (i : Fin 33)
    (hs : blockSite b = .inl i)
    (hN : SpecNorm hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)) :
    C.Ci.blockPrice b ≤ MainFinal.midPoly (allpWeights i) (allpInputs i) (κ i) (pieceStart i)
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
  have h := specPrice_le hW (paperIn f1Cell) (κ i) hX hb hsel (specF hW A b) (C.blk b) hu hsh hN
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


/-- **`hSA` in explicit form with the middle charges proved at `f1Cell`** (K1's `SAExplicit_N1`
with N2's `f1_charge_le` in place of N1's certificates: `c₂ = f1c2`, `c₃ = f1c3` from `thm:bmor`
(H2) and `ThetaSmallRR` (H2″), and `c₄ = X_i^{-1/2} c₃`, `c₅ = X_i^{-1} c₃` by
`blockCharge_shift`). Remaining: the clique bound `H`, the upper bound `U`, the middle norm sizes,
the signs of `K_d(i)` and the numerical inequality at N2's numbers. -/
theorem ComparisonParts.SAExplicit_F1 (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) {H U : ℝ} (hq : ∑ q, C.Ci.cliquePrice q ≤ H)
    (hu : ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b ≤ U)
    (κ : Fin 33 → MiddleConsts) (hN : C.MiddleNorms hW A κ)
    (hK : ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i)
    (hsum : H + U + ∑ i : Fin 33, (midK2 κ i * f1c2 i +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
        (C.St + C.At) ≤ targetLedger.S + targetLedger.A) :
    SAExplicit C.Ci := by
  have h₂ := fun i => (f1_charge_le hBMOR hRR i).1
  have h₃ := fun i => (f1_charge_le hBMOR hRR i).2
  refine C.SAExplicit_paper hq hu κ hN (c₂ := f1c2) (c₃ := f1c3)
    (c₄ := fun i => pieceScale i ^ 1 * f1c3 i)
    (c₅ := fun i => pieceScale i ^ 2 * f1c3 i) h₂ h₃
    (fun i => (blockCharge_shift i 3 1).trans
      (mul_le_mul_of_nonneg_left (h₃ i) (pow_nonneg (pieceScale_nonneg i) 1)))
    (fun i => (blockCharge_shift i 3 2).trans
      (mul_le_mul_of_nonneg_left (h₃ i) (pow_nonneg (pieceScale_nonneg i) 2))) hK ?_
  refine le_trans (le_of_eq ?_) hsum
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Middle

/-! ## Upper prices (K1's `UpperPrices.lean`, paper section) -/

section Upper

/-- The band of a block (`0` for a block of a middle piece, which is never used). -/
noncomputable def bandIdx (b : Blk) : Fin 310 :=
  match blockSite b with
  | .inr k => k
  | .inl _ => 0

variable (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)

theorem siteSpec_upper_facts (b : Blk) (k : Fin 310) (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i)
    (hCa : ∀ i, 0 ≤ Ca i) : ∀ s (hs : blockSite b = s), s = .inr k →
      specCoefS Cs Ca hCs hCa (siteSpec hW A b s hs) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefS ∧
      specCoefA Cs Ca hCs hCa (siteSpec hW A b s hs) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefA ∧
      specR (siteSpec hW A b s hs) = BlockSpecPaper.blockScale b
  | .inr j, _, h => by
    obtain rfl : j = k := Sum.inr.inj h
    exact ⟨rfl, rfl, rfl⟩
  | .inl _, _, h => absurd h (by simp)

theorem paperSpec_upper_facts (b : Blk) (k : Fin 310) (hs : blockSite b = .inr k)
    (Cs Ca : UpIdx → ℝ) (hCs : ∀ i, 0 ≤ Cs i) (hCa : ∀ i, 0 ≤ Ca i) :
    specCoefS Cs Ca hCs hCa (specF hW A b) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefS ∧
      specCoefA Cs Ca hCs hCa (specF hW A b) =
        (upperLedger (UpperRecords.bandWeights k) Cs Ca hCs hCa).coefA ∧
      specR (specF hW A b) = BlockSpecPaper.blockScale b :=
  siteSpec_upper_facts hW A b k Cs Ca hCs hCa _ rfl hs

/-- **The per-record bounds of every upper block of the combined data**, with per-band record
coefficients `Cs k`, `Ca k`. *Hypothesis* (analytic, `prop:record:upper`(i)). -/
def ComparisonParts.UpperRecs {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (Cs Ca : Fin 310 → UpIdx → ℝ)
    (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i) : Prop :=
  ∀ b k, blockSite b = .inr k →
    SpecUpperRec hW (paperIn f1Cell) (Cs k) (Ca k) (hCs k) (hCa k) (specF hW A b) (C.blk b)

variable {hW A}

/-- A block whose specification is upper lies in a band. -/
theorem blockSite_of_upper (b : Blk) (hb : specUpper (specF hW A b) = true) :
    blockSite b = .inr (bandIdx b) := by
  unfold bandIdx
  rcases h : blockSite b with i | k
  · exact absurd hb (by rw [(paperSpec_facts hW A b i h ⟨0, 0, 0, 0, 0⟩ 0 0).1]; simp)
  · rfl

theorem ComparisonParts.upper_le {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) (Cs Ca : Fin 310 → UpIdx → ℝ)
    (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i) (hR : C.UpperRecs hW A Cs Ca hCs hCa)
    (US UA : Fin 310 → ℕ → ℝ)
    (hUS : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ US β d)
    (hUA : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ UA β d) :
    ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b ≤
      ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefS d * US β d +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefA d * UA β d) := by
  have hsel : ∀ b : Blk, 0 ≤ blockSel bOf b := fun b =>
    le_trans zero_le_one (one_le_paperSelAt (paperAtomMap bOf) targetDecay_nonneg _)
  have hP : ∀ b, specUpper (specF hW A b) = true →
      (C.Ci.blockAtom b).sprice (blockSel bOf b) ≤
          polyEval (upperLedger (UpperRecords.bandWeights (bandIdx b))
            (Cs (bandIdx b)) (Ca (bandIdx b)) (hCs (bandIdx b)) (hCa (bandIdx b))).coefS
            (BlockSpecPaper.blockScale b) * blockSel bOf b ∧
        (C.Ci.blockAtom b).aprice (blockSel bOf b) ≤
          polyEval (upperLedger (UpperRecords.bandWeights (bandIdx b))
            (Cs (bandIdx b)) (Ca (bandIdx b)) (hCs (bandIdx b)) (hCa (bandIdx b))).coefA
            (BlockSpecPaper.blockScale b) * blockSel bOf b := by
    intro b hb
    have hs := blockSite_of_upper b hb
    obtain ⟨eS, eA, eR⟩ := paperSpec_upper_facts hW A b (bandIdx b) hs (Cs (bandIdx b))
      (Ca (bandIdx b)) (hCs (bandIdx b)) (hCa (bandIdx b))
    have h := specUpper_prices_le hW (paperIn f1Cell) (Cs (bandIdx b)) (Ca (bandIdx b))
      (hCs (bandIdx b)) (hCa (bandIdx b)) (hsel b) (specF hW A b) (C.blk b) hb
      (hR b (bandIdx b) hs)
    rw [eS, eA, eR] at h
    exact h
  exact ComparisonLawPaper.upper_blocks_le_of_bands C.Ci bandIdx univ (fun _ _ => mem_univ _)
    BlockSpecPaper.blockScale
    (fun β => (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
      (hCa β)).coefS)
    (fun β => (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
      (hCa β)).coefA) US UA
    (fun β _ d _ => UpperComparison.RecordLedger.coefS_nonneg _ d)
    (fun β _ d _ => UpperComparison.RecordLedger.coefA_nonneg _ d)
    (fun β _ => hUS β) (fun β _ => hUA β) (fun b hb => (hP b hb).1) (fun b hb => (hP b hb).2)


/-- **`hSA` in explicit form, every range reduced, at `f1Cell`** (K1's `SAExplicit_full` with the
middle charges from `SAExplicit_F1`): the clique bound, the upper per-record bounds `UpperRecs` with
band charges `𝒰^s`, `𝒰^a`, the middle norm sizes `MiddleNorms`, the signs of `K_d(i)`, and the
numerical inequality at N2's numbers `f1c2`, `f1c3`. -/
theorem ComparisonParts.SAExplicit_fullF1 (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    (C : ComparisonParts hW hMR hFour A) {H : ℝ} (hq : ∑ q, C.Ci.cliquePrice q ≤ H)
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) (US UA : Fin 310 → ℕ → ℝ)
    (hUS : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ US β d)
    (hUA : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
      blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ UA β d)
    (κ : Fin 33 → MiddleConsts) (hN : C.MiddleNorms hW A κ)
    (hK : ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i)
    (hsum : H + ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefS d * US β d +
          (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefA d * UA β d) +
      ∑ i : Fin 33, (midK2 κ i * f1c2 i +
        (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
          (C.St + C.At) ≤ targetLedger.S + targetLedger.A) :
    SAExplicit C.Ci :=
  C.SAExplicit_F1 hBMOR hRR hq (C.upper_le Cs Ca hCs hCa hR US UA hUS hUA) κ hN hK hsum

end Upper

end Sarkozy.MainFinalF1
