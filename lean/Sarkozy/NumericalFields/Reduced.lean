module

public import Sarkozy.MainFinal2.Obligations
public import Sarkozy.NumericalFields.Signs

@[expose] public section

/-!
# K2's (CP6) inputs without the gates `hK`, `hTK`; `hSA` without the signs `hK` (E2)

**The (CP6) gates (K2's fields 39, 40).** In `EnvelopeParts2` the numbers `T_K` and `T_pre` are
free data, tied by `∑ KL ≤ T_K`, `∑ KR ≤ T_K` (`hK`) and `T_K + T_pre + 11/10⁷⁰ ≤ T^{ledger}`
(`hTK`). The paper *defines* them this way (`24_matching_mean.tex`, "The matching exponent"):
`T_K` is the bound of the side excess over all pieces (`prop:signed-sides`(iii)), and
`T = S_E + A_E + S_oth + A_oth + T_K + S_u + A_u + 10⁻¹²` is the sum. So the two gates are
removed by taking `T_K = max(∑ KL, ∑ KR)` and `T_pre = T^{ledger} − T_K − 11/10⁷⁰`:
`EnvelopePartsE2` has one combined field `hothT`,
`others(L) + max(∑ KL, ∑ KR) + 11/10⁷⁰ ≤ T^{ledger}` at every scale. The reduction is an
**equivalence**: `EnvelopePartsE2.toParts2` and `EnvelopePartsE2.ofParts2`.

**The signs (K2's field 37).** `SAPartsE2` is K2's `SAParts` with `hK` replaced by the side
condition `hκ : ∀ i, KappaNonneg (κ i)` on the data `κ`; `hK` is then proved
(`NumericalFields.midK_signs`). `SAPartsE2.toParts2` and `SAPartsE2.ofParts2` (which needs `hκ`)
map between the two.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.NumericalFields

open Sarkozy.MainFinal Sarkozy.MainFinal2
open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.ComparisonLawPaper (upperBand blockSel)
open Sarkozy.PaperNumbers (paperCell)

/-! ## (CP6), (CP8)(c) without the gates -/

/-- **The open inputs of (CP6) and (CP8)(c) without the two gates** (K2's `EnvelopeParts2` at
`T_K = max(∑ KL, ∑ KR)`, `T_pre = T^{ledger} − T_K − 11/10⁷⁰`; `prop:record:matching`,
`prop:signed-sides`(iii), the definition of `T` in "The matching exponent"). 4 fields. -/
structure EnvelopePartsE2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) (C : ComparisonParts2 hW hMR hFour A) where
  /-- The prefix refinement on the middle blocks (`prop:record:matching`(i), `prop:signed-sides`);
  as in `EnvelopeParts2.MR`. *Open*. -/
  MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn paperCell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true)
  /-- **The records not replaced at the prefix atoms, with the side excess, fit in `T`** at every
  scale (`prop:record:matching`(ii) with `prop:signed-sides`(iii)): their price, plus
  `T_K = max(∑ KL, ∑ KR)`, plus the tail allowance `11/10⁷⁰`, is at most `T^{ledger}`. *Open* (a
  property of `CL` and `MR`; K2's `hothPre`, `hK`, `hTK` in one). -/
  hothT : ∀ L, (∑ β, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl β),
    (C.toK1.CL.π L (.inl β) t .sym + C.toK1.CL.π L (.inl β) t .skew)) +
      max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) + 11 / 10 ^ 70 ≤ targetLedger.T
  /-- The weighted (CP4) bound of the prefix atoms. Data. -/
  σpre : ℝ
  /-- The weighted (CP4) summability at the prefix atoms (`def:cp8`(c)). *Open*; as in
  `EnvelopeParts2.hCLpre`. -/
  hCLpre : ∀ L, ∑ β, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L
      (.inl β) ^ ((1 : ℝ) / 4) *
    (symTotal (C.toK1.CL.π L) (.inl β) + skewTotal (C.toK1.CL.π L) (.inl β)) ≤ σpre

namespace EnvelopePartsE2

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs paperCell} {C : ComparisonParts2 hW hMR hFour A}

/-- `T_K = max(∑ KL, ∑ KR)`. -/
noncomputable def TK (E : EnvelopePartsE2 hW hMR hFour A C) : ℝ :=
  max (∑ β, E.MR.toPrefix.KL β) (∑ β, E.MR.toPrefix.KR β)

/-- **K2's `EnvelopeParts2`**, with the gates `hK` (field 39) and `hTK` (field 40) proved at
`T_K = max(∑ KL, ∑ KR)` and `T_pre = T^{ledger} − T_K − 11/10⁷⁰`. -/
noncomputable def toParts2 (E : EnvelopePartsE2 hW hMR hFour A C) :
    EnvelopeParts2 hW hMR hFour A C where
  MR := E.MR
  TK := E.TK
  hK := ⟨le_max_left _ _, le_max_right _ _⟩
  Tpre := targetLedger.T - E.TK - 11 / 10 ^ 70
  hothPre L := by
    have h := E.hothT L
    unfold TK
    linarith
  hTK := le_of_eq (by ring)
  σpre := E.σpre
  hCLpre := E.hCLpre

/-- **The reduction loses nothing**: every `EnvelopeParts2` gives an `EnvelopePartsE2` with the
same refinement (`max(∑ KL, ∑ KR) ≤ T_K` by `hK`, then `hothPre` and `hTK`). -/
noncomputable def ofParts2 (E : EnvelopeParts2 hW hMR hFour A C) :
    EnvelopePartsE2 hW hMR hFour A C where
  MR := E.MR
  hothT L := by
    have h1 := E.hothPre L
    have h2 := max_le E.hK.1 E.hK.2
    have h3 := E.hTK
    linarith
  σpre := E.σpre
  hCLpre := E.hCLpre

theorem ofParts2_MR (E : EnvelopeParts2 hW hMR hFour A C) : (ofParts2 E).MR = E.MR := rfl

theorem toParts2_MR (E : EnvelopePartsE2 hW hMR hFour A C) : E.toParts2.MR = E.MR := rfl

end EnvelopePartsE2

/-! ## `hSA` without the signs -/

/-- **`hSA` in reduced form without the signs `hK`** (K2's `SAParts`, `def:closing-quantities`,
`def:cp4`(b)): the field `hK` (the signs of `K_d(i)`, K2's field 37) is replaced by the side
condition `hκ` on the data `κ`, from which it is proved (`midK_signs`). 16 fields. -/
structure SAPartsE2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) (C : ComparisonParts2 hW hMR hFour A) where
  /-- The clique bound. Data. -/
  H : ℝ
  /-- `∑_p λ^ex_p(1) q_p^{2a} ≤ H` (`lem:frontier:iidenergy`(iii)). *Open* (analytic). -/
  hq : ∑ q, C.toK1.Ci.cliquePrice q ≤ H
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The upper per-record bounds (`prop:record:upper`(ii), W8's ledger). *Open* (analytic). -/
  hR : C.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The band charges `𝒰_{β,d}`, one number for the symmetric and the skew prices. Data. -/
  U : Fin 310 → ℕ → ℝ
  /-- `∑_{𝔅 ∈ band} q_𝔅^{2a} r_𝔅^d ≤ 𝒰_{β,d}` (`def:record:upper-bands`, the band charges of
  `prop:record:upper`(ii)). *Open* (numerical: prime sums over the bands). K2's `hUS` and `hUA`
  are the same statement for two data `US`, `UA`; one field suffices (`SAPartsE2.ofParts2` takes
  `U = min(US, UA)`). -/
  hU : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
    blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ U β d
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)` (`eq:signed-constants`,
  `lem:record:exact-marginal-e`(ii)). Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative. Side condition on the data `κ`. -/
  hκ : ∀ i, KappaNonneg (κ i)
  /-- **The twelve norm bounds of every middle block** (B8's `NormBounds`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn paperCell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)
  /-- **The final numerical inequality** of `hSA`. *Open* (numerical). -/
  hsum : H + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d * U β d +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          U β d) +
    ∑ i : Fin 33, (midK2 κ i * (PaperNumbers.chargeC2 i : ℝ) +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        (PaperNumbers.chargeC3 i : ℝ)) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

namespace SAPartsE2

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs paperCell} {C : ComparisonParts2 hW hMR hFour A}

/-- **K2's `SAParts`**, with the signs `hK` (field 37) proved from `hκ` (`midK_signs`) and
`US = UA = U` (field 36 is field 35). -/
def toParts2 (S : SAPartsE2 hW hMR hFour A C) : SAParts hW hMR hFour A C where
  H := S.H
  hq := S.hq
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  US := S.U
  UA := S.U
  hUS := S.hU
  hUA := S.hU
  κ := S.κ
  hN := S.hN
  hK := midK_signs S.κ S.hκ
  hsum := S.hsum

/-- **Conversely**, `SAParts` with nonnegative constants gives `SAPartsE2`, with the band charge
`U = min(US, UA)` (the coefficients `coefS`, `coefA` are nonnegative). -/
def ofParts2 (S : SAParts hW hMR hFour A C) (hκ : ∀ i, KappaNonneg (S.κ i)) :
    SAPartsE2 hW hMR hFour A C where
  H := S.H
  hq := S.hq
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  U β d := min (S.US β d) (S.UA β d)
  hU β d hd := le_min (S.hUS β d hd) (S.hUA β d hd)
  κ := S.κ
  hκ := hκ
  hN := S.hN
  hsum := by
    have hX : ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (S.Cs β) (S.Ca β) (S.hCs β)
            (S.hCa β)).coefS d * min (S.US β d) (S.UA β d) +
          (upperLedger (UpperRecords.bandWeights β) (S.Cs β) (S.Ca β) (S.hCs β)
            (S.hCa β)).coefA d * min (S.US β d) (S.UA β d)) ≤
        ∑ β, ∑ d ∈ upperDegrees,
        ((upperLedger (UpperRecords.bandWeights β) (S.Cs β) (S.Ca β) (S.hCs β)
            (S.hCa β)).coefS d * S.US β d +
          (upperLedger (UpperRecords.bandWeights β) (S.Cs β) (S.Ca β) (S.hCs β)
            (S.hCa β)).coefA d * S.UA β d) :=
      Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun d _ => add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (RecordLedger.coefS_nonneg _ d))
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (RecordLedger.coefA_nonneg _ d))
    have h := S.hsum
    linarith

end SAPartsE2

end Sarkozy.NumericalFields
