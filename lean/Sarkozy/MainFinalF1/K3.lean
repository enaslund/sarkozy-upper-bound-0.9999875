module

public import Sarkozy.MainFinalF1.K2
public import Sarkozy.MainFinalF1.Bands
public import Sarkozy.MainFinal3.All

@[expose] public section

/-!
# `MainFinal3`'s layer at `f1Cell`: C10's clique, E1's signed estimates, E2's numerical fields (F1P)

The closures of C10, E1, E2 used by `MainFinal3`, at `f1Cell`:

* E1 (`SignedEstimates/Paper.lean`, `Final.lean`): `blockPrime_ge`, **`paperMiddleEstimates`**
  (`lem:signed-components`(b), `lem:old-f-law`(a), proved from H1 with `η_p = 10/p`,
  `e_p = e₀(p)`), `UpperSpec`, `UpperSpec.toSigned`;
* C10 (`CliqueDeletion/MainFinal.lean`): **`cliqueK1`**, `cliqueK1_ω_le`
  (`lem:frontier:iidenergy`(ii),(iii), `lem:frontier:iidlocal`(iv),(v); C10's
  `paperCliqueDeletion` is layout-generic);
* E2 (`NumericalFields/Reduced.lean`, `BandField.lean`): `EnvelopePartsE2` (the gates `hK`, `hTK`
  proved), `SAPartsE2` (the signs `hK` proved from `hκ`), **`SAPartsE3`** (the band charges
  `hUS`, `hUA` proved from `thm:bmor` by `upperBand_le_bandBound` at `f1Cell`, `Bands.lean`);
* `MainFinal3` (`Comparison.lean`, `Main.lean`): `ComparisonParts3`, `SAParts3`,
  `FinalBlockData3` with their maps;
* C10's `MainFinalObligations3J` (`MainFinalJ/Main.lean`) **without `hHist`**.

The final numerical inequalities (`SAPartsE2.hsum`, `SAPartsE3.hsum`, `SAParts3.hsum`) are stated at
N2's numbers `f1c2`, `f1c3` in place of N1's `chargeC2`, `chargeC3`. Everything else is verbatim up
to the cell.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference paperAtomMap PrefixCoord blockPrimes)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted tailNe UpperAtomInputs upperNe
  upperBand blockSel)
open Sarkozy.MainFinal (PrimeCertificates BlockAnalytic hCF MiddleConsts midK2 midK3 midK4 midK5
  pieceScale)
open Sarkozy.MainFinal2 (PrimeCertificates2 tPaper tPaper_nonneg tPaper_le_one MidRefinement
  SharpParts2)
open Sarkozy.SignedEstimates (signedEstimates_zmod e0 e0_nonneg e0_lt_one)
open Sarkozy.CliqueDeletion (paperCliqueDeletion paperCliqueDeletion_ω_le)
open Sarkozy.NumericalFields (KappaNonneg midK_signs bandBound)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3)

/-! ## E1: the signed estimates of the middle blocks -/

section Signed

theorem blockPrime_ge (b : Blk) (i : {j : PaperJ0 // paperAtomMap bOf j = .inr b}) :
    16777216 ≤ blockPrimes bOf b i :=
  le_trans (by norm_num [PartV.Q3]) (blockPrimes_mod_ge b i).2

/-- **The signed estimates of every middle block of the paper** (field 11 of
`MainFinalObligations2`, `lem:signed-components`(b) and `lem:old-f-law`(a)), **proved from H1**,
with the paper's constants `η_p = 10/p` and `e_p = e₀(p) = 2q/((1-3q)(1-4q))` at every prime `p`
of the block, at the paper's `t = 127/500`. -/
noncomputable def paperMiddleEstimates (hW : Target.Weil) (b : Blk)
    (hne : MiddleNonempty (blockPrimes bOf b)) : MiddleEstimates b hne where
  η i := 10 / (blockPrimes bOf b i : ℝ)
  e i := e0 (blockPrimes bOf b i)
  hη i := by positivity
  hη1 i := by
    have h : (16777216 : ℝ) ≤ blockPrimes bOf b i := by exact_mod_cast blockPrime_ge b i
    rw [div_lt_one (by linarith)]
    linarith
  he i := e0_nonneg (by
    have h : (16777216 : ℝ) ≤ blockPrimes bOf b i := by exact_mod_cast blockPrime_ge b i
    linarith)
  he1 i := e0_lt_one (by
    have h : (16777216 : ℝ) ≤ blockPrimes bOf b i := by exact_mod_cast blockPrime_ge b i
    linarith)
  E i c := signedEstimates_zmod hW _ (blockPrimes_mod_ge b i).1 (blockPrime_ge b i) (hne.F2 i)
    tPaper_nonneg tPaper_le_one c


end Signed

/-- **The upper-block part of K2's `SignedSpec`**: B2's `UpperAtomInputs` on an upper block
(`prop:record:upper`(i), open), nothing on a middle block. -/
def UpperSpec (hW : Target.Weil) {b : Blk} : PaperBlockSpec bOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes bOf b) (upperNe hW U) U.W U.r)
  | .middleUniform _ => PUnit
  | .middleIndividual _ => PUnit
  | .middleCoherent _ => PUnit

/-- **K2's `SignedSpec` with the middle blocks proved** (`paperMiddleEstimates`:
`lem:signed-components`(b), `lem:old-f-law`(a) from H1, `η_p = 10/p`, `e_p = e₀(p)`). -/
noncomputable def UpperSpec.toSigned (hW : Target.Weil) {b : Blk} :
    (S : PaperBlockSpec bOf b) → UpperSpec hW S → SignedSpec hW S
  | .upper _, U => U
  | .middleUniform M, _ => ULift.up (paperMiddleEstimates hW b M.hne)
  | .middleIndividual M, _ => ULift.up (paperMiddleEstimates hW b M.hne)
  | .middleCoherent M, _ => ULift.up (paperMiddleEstimates hW b M.hne)


/-! ## C10: the square-clique deletions -/

/-- **K1's field `ComparisonParts.clique`, proved** (`lem:frontier:iidenergy`(ii),
`lem:frontier:iidlocal`(iv),(v); for `p ≥ 2¹⁶` `thm:density:iid-prefix`(a),(c)). -/
noncomputable def cliqueK1 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : BlockSpecPaper.PaperAnalyticInputs AnalyticCells.f1Cell) (q : PrefixCoord) :
    DeletionInputs ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries :=
  paperCliqueDeletion bOf hW (specF hW A) (hCF hW hMR hFour) q

theorem cliqueK1_ω_le (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : BlockSpecPaper.PaperAnalyticInputs AnalyticCells.f1Cell) (q : PrefixCoord) :
    (cliqueK1 hW hMR hFour A q).ω ≤ 12 / 2 ^ PartV.digitPairs :=
  paperCliqueDeletion_ω_le bOf hW (specF hW A) (hCF hW hMR hFour) q

/-! ## E2: the reduced fields -/

/-- **The open inputs of (CP6) and (CP8)(c) without the two gates** (K2's `EnvelopeParts2` at
`T_K = max(∑ KL, ∑ KR)`, `T_pre = T^{ledger} − T_K − 11/10⁷⁰`; `prop:record:matching`,
`prop:signed-sides`(iii), the definition of `T` in "The matching exponent"). 4 fields. -/
structure EnvelopePartsE2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonParts2 hW hMR hFour A) where
  /-- The prefix refinement on the middle blocks (`prop:record:matching`(i), `prop:signed-sides`);
  as in `EnvelopeParts2.MR`. *Open*. -/
  MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn f1Cell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true)
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
  {A : PaperAnalyticInputs f1Cell} {C : ComparisonParts2 hW hMR hFour A}

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
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonParts2 hW hMR hFour A) where
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
    SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)
  /-- **The final numerical inequality** of `hSA`. *Open* (numerical). -/
  hsum : H + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d * U β d +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          U β d) +
    ∑ i : Fin 33, (midK2 κ i * f1c2 i +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        f1c3 i) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

namespace SAPartsE2

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell} {C : ComparisonParts2 hW hMR hFour A}

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

/-- **`hSA` in reduced form without the signs and without the band-charge field** (`SAPartsE2` at
`U = bandBound a_T`, `hU` proved by `upperBand_le_bandBound`). 13 fields. -/
structure SAPartsE3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonParts2 hW hMR hFour A) where
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
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)`. Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative. Side condition on the data `κ`. -/
  hκ : ∀ i, KappaNonneg (κ i)
  /-- **The twelve norm bounds of every middle block** (B8's `NormBounds`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)
  /-- **The final numerical inequality** of `hSA`, at the band charges `bandBound a_T`
  (`def:closing-quantities`). *Open* (numerical: `bandBound` is explicit, but not evaluated). -/
  hsum : H + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
          bandBound targetDecay d β +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          bandBound targetDecay d β) +
    ∑ i : Fin 33, (midK2 κ i * f1c2 i +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        f1c3 i) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

/-- `SAPartsE2` from `SAPartsE3`, with `hU` from `thm:bmor` (`upperBand_le_bandBound`). -/
noncomputable def SAPartsE3.toE2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs f1Cell} {C : ComparisonParts2 hW hMR hFour A}
    (hB : Target.BMOR) (S : SAPartsE3 hW hMR hFour A C) : SAPartsE2 hW hMR hFour A C where
  H := S.H
  hq := S.hq
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  U β d := bandBound targetDecay d β
  hU β d _ := upperBand_le_bandBound hB hW A β d
  κ := S.κ
  hκ := S.hκ
  hN := S.hN
  hsum := S.hsum

/-! ## `MainFinal3`'s comparison layer -/

/-- **The open inputs of (CP4), third round**: K2's `ComparisonParts2` with the square-clique
deletions proved (C10's `cliqueK1`) and the middle-block estimates proved (E1's
`paperMiddleEstimates`). 3 fields: per upper block B2's upper inputs, per tail prime the repairs
and their cap bounds. -/
structure ComparisonParts3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) where
  /-- Upper blocks only (E1's `UpperSpec`): B2's `UpperAtomInputs` (`prop:record:upper`(i);
  *open*); nothing on a middle block (`MiddleEstimates` proved by E1). -/
  blkU : ∀ b : Blk, UpperSpec hW (specF hW A b)
  /-- Tail primes `q ≥ P₄`: a repair of each changed record (`lem:tr:repair`, (F7)). *Open*. -/
  Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
    TailPrices.TailRepairs q (ComparisonLawPaper.tailNe hW h4)
  /-- The repair constants against the paper's caps (`cert:tail-caps`,
  `lem:record:domain`(iii)). *Open*. -/
  hcap : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
    (e : ChangeType), (Rp q h4 t φ h).C e ≤ TailPrices.tailCap (true, ⟨t, φ⟩) * tailR q

/-- **K2's `ComparisonParts2`**, with `clique := cliqueK1` (C10) and the middle
blocks from `paperMiddleEstimates` (E1's `UpperSpec.toSigned`). -/
noncomputable def ComparisonParts3.toK2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    (C : ComparisonParts3 hW hMR hFour A) : ComparisonParts2 hW hMR hFour A where
  clique := cliqueK1 hW hMR hFour A
  blk b := UpperSpec.toSigned hW (specF hW A b) (C.blkU b)
  Rp := C.Rp
  hcap := C.hcap

/-- **The clique bound, proved** (`lem:frontier:iidenergy`(iii),(iv) at `a_T`):
`∑_p λ^ex_p(1) q_p^{2a_T} ≤ 12/2^{534}` (C10). -/
theorem ComparisonParts3.cliquePrice_le {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    (C : ComparisonParts3 hW hMR hFour A) :
    ∑ q, C.toK2.toK1.Ci.cliquePrice q ≤ 12 / 2 ^ 534 := by
  apply CliqueDeletion.ComparisonInputs.cliquePrice_sum_le
  intro q
  show (cliqueK1 hW hMR hFour A q).ω ≤ _
  exact cliqueK1_ω_le hW hMR hFour A q

/-! ## `hSA`: the clique bound entered, E2's reductions -/

/-- **`S + A ≤ S^{ledger} + A^{ledger}` in reduced form, third round**: E2's `SAPartsE3` (K2's
`SAParts` with the band charges `hUS`, `hUA` proved from `thm:bmor` at `𝒰 = bandBound a_T`, and the
signs `hK` proved from the side condition `hκ`) without the clique bound `H`, `hq` (proved:
`H = 12/2^{534}`, `ComparisonParts3.cliquePrice_le`). 9 fields. -/
structure SAParts3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonParts3 hW hMR hFour A) where
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The upper per-record bounds (`prop:record:upper`(ii), W8's ledger). *Open* (analytic). -/
  hR : C.toK2.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)`. Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative (E2). Side condition on the data `κ`. -/
  hκ : ∀ i, KappaNonneg (κ i)
  /-- The twelve norm bounds of every middle block (B8's `NormBounds`), for the paper's records
  (`paperComponents` of `paperMiddleEstimates`, `M_c(10/p, e₀(p))`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.toK2.blk b)
  /-- **The final numerical inequality** of `hSA`, with the clique bound `12/2^{534}`, the band
  charges `bandBound a_T` (E2) and the tail bound `11/10⁷⁰` entered. *Open* (numerical). -/
  hsum : 12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
          bandBound targetDecay d β +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          bandBound targetDecay d β) +
    ∑ i : Fin 33, (midK2 κ i * f1c2 i +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        f1c3 i) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

/-- **E2's `SAPartsE3`**, with `H := 12/2^{534}` and `hq := ComparisonParts3.cliquePrice_le`. -/
noncomputable def SAParts3.toE3 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonParts3 hW hMR hFour A} (S : SAParts3 hW hMR hFour A C) :
    SAPartsE3 hW hMR hFour A C.toK2 where
  H := 12 / 2 ^ 534
  hq := C.cliquePrice_le
  Cs := S.Cs
  Ca := S.Ca
  hCs := S.hCs
  hCa := S.hCa
  hR := S.hR
  κ := S.κ
  hκ := S.hκ
  hN := S.hN
  hsum := S.hsum

/-- **K2's `SAParts`** (E2's `SAPartsE3.toE2` with `thm:bmor`, then `SAPartsE2.toParts2`). -/
noncomputable def SAParts3.toK2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonParts3 hW hMR hFour A} (hB : Target.BMOR) (S : SAParts3 hW hMR hFour A C) :
    SAParts hW hMR hFour A C.toK2 :=
  (S.toE3.toE2 hB).toParts2

/-- **The block data, third round**: K2's `FinalBlockData2` with the (CP4) inputs of
`ComparisonParts3` (no square-clique field, no middle-block estimates). 4 fields. -/
structure FinalBlockData3 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (B8, T2; the square-clique atoms proved by C10, the middle estimates by
  E1). -/
  Cmp : ComparisonParts3 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The (CP6), (CP8)(c) inputs (B3, K1, K2), without the gates `hK`, `hTK` (E2's
  `EnvelopePartsE2`). -/
  Env : EnvelopePartsE2 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
    Cmp.toK2

/-- K2's `FinalBlockData2`. -/
noncomputable def FinalBlockData3.toK2 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (D : FinalBlockData3 hW hMR hFour) :
    FinalBlockData2 hW hMR hFour where
  PC := D.PC
  BA := D.BA
  Cmp := D.Cmp.toK2
  Env := D.Env.toParts2


/-! ## C10's `MainFinal3`-level obligations at `f1Cell`, without `hHist` -/

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **`MainFinal3`'s obligations with the combined gate at `f1Cell`** (C10's
`MainFinalObligations3J` without `hHist`). 4 fields. -/
structure MainFinalObligations3J (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  Dv : FinalBlockData3 hW hMR hFour
  SA : SAParts3 hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  Cls : ClassData.ClassParts2J Dv.toK2.toK1.data
  Sh : SharpParts2 Dv.toK2.toK1.toJoint

/-- K2's layer at `f1Cell` (`MainFinal3`'s `toK2` maps). -/
noncomputable def MainFinalObligations3J.toK2J (hBMOR : Target.BMOR)
    (O : MainFinalObligations3J hW hMR hFour) : MainFinalObligations2J hW hMR hFour where
  Dv := O.Dv.toK2
  SA := O.SA.toK2 hBMOR
  Cls := O.Cls
  Sh := O.Sh

end Sarkozy.MainFinalF1
