module

public import Sarkozy.MainFinal2.Structure
public import Sarkozy.MainFinal2.Refinement

@[expose] public section

/-!
# The combined obligations, second round: (CP4), `hSA`, (CP6), classes, sharp terms (K2)

* `ComparisonParts2` (B8, T2): K1's `ComparisonParts` by `TailPrices.ofTailCapsPaper` with the
  middle blocks from the signed estimates (`SignedSpec.toSpecData`); `St + At ≤ 1.1·10⁻⁶⁹`
  **proved** (`ComparisonParts2.St_At_le`).
* `SAParts` (K1's `SAExplicit_full`, B8's `NormBounds`): `hSA` from the clique bound, the upper
  per-record bounds, the band charges, the twelve norm bounds of every middle block, the signs
  of `K_d(i)` and one numerical inequality, with the tail numbers entered (`11/10⁷⁰`).
* `EnvelopeParts2` (K1's `ofOthers`, B3's prefix refinement through `MidRefinement`): `hrepl`
  **proved** from the other records at the prefix atoms `hothPre`, the tail atoms
  (`tail_price_le`, proved) and the gate `T_K + T_pre + 11/10⁷⁰ ≤ T`; the refinement is trivial
  off the middle blocks (proved); the tail half of (CP8)(c) is proved.
* `FinalBlockData2`, `ClassParts2` (B10), `SharpParts2` (B9).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal2

open Sarkozy.MainFinal
open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap PrefixCoord)
open Sarkozy.EnvelopesPaper (PrefixRefinement)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted SAExplicit tailNe upperBand
  blockSel)
open Sarkozy.ClassBoundsPaper (PolynomialData)
open Sarkozy.ClassInputsPaper (ClassData ClassEnergyData MeanData ClassPartsB10)
open Sarkozy.EnvelopeEnergiesPaper (CoupledFibreMoment paper_pairwise)
open Sarkozy.PaperNumbers (paperCell)

/-! ## (CP4): B8's middle blocks and T2's tail atoms -/

/-- **The open inputs of (CP4)** (`def:cp4`) after B8 and T2: the square-clique deletions, per
class-three block the signed estimates (middle) or B2's upper inputs (upper), and per tail prime
the repairs of the changed records with their cap bounds. 4 fields. -/
structure ComparisonParts2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) where
  /-- Square-clique atoms: the deletion `ν_p = μ_p − ω κ̄` (`lem:frontier:iidenergy`(ii),
  `lem:frontier:iidlocal`(iv),(v)). *Open* (analytic; `DeletionInputs`, 9 sub-fields). -/
  clique : ∀ q : PrefixCoord, DeletionInputs
    ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
    (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries
  /-- Class-three blocks: on an upper block B2's `UpperAtomInputs` (the replacing laws of the 92
  changed records, `prop:record:upper`(i); *open*, 6 sub-fields); on a middle block the signed
  estimates `MiddleEstimates` (`lem:signed-components`(b), `lem:old-f-law`(a); *open*), from which
  B7's `ReplacementData` is constructed (B8's `ofFold`). -/
  blk : ∀ b : Blk, SignedSpec hW (specF hW A b)
  /-- Tail primes `q ≥ P₄`: a repair of each changed record (`lem:tr:repair`, (F7); support,
  acceptance of `𝓔₆`, square-affine invariance, two norm bounds). *Open* (analytic). -/
  Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailPrices.TailRepairs q (tailNe hW h4)
  /-- The repair constants against the paper's caps, `C^ε_ρ ≤ K_ρ q^{-1/2}` (`cert:tail-caps`,
  `lem:record:domain`(iii)). *Open* (analytic: the (F7) coefficient at `q` against its value at
  `2⁵⁴`). -/
  hcap : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
    (e : ChangeType), (Rp q h4 t φ h).C e ≤ TailPrices.tailCap (true, ⟨t, φ⟩) * tailR q

namespace ComparisonParts2

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs paperCell}

/-- **K1's `ComparisonParts`** (T2's `ofTailCapsPaper`; the tail fields `tail_S`, `tail_A`, `St`,
`At` and the cap ledger proved; the middle `ReplacementData` constructed by B8's `ofFold`). -/
noncomputable def toK1 (C : ComparisonParts2 hW hMR hFour A) : ComparisonParts hW hMR hFour A :=
  TailPrices.ofTailCapsPaper C.clique
    (fun b => SignedSpec.toSpecData hW (paperIn paperCell) (specF hW A b) (C.blk b)) C.Rp C.hcap

/-- **The tail numbers** `S_tail + A_tail ≤ 1.1·10⁻⁶⁹` (`lem:tail-prices`(iv); T2). -/
theorem St_At_le (C : ComparisonParts2 hW hMR hFour A) : C.toK1.St + C.toK1.At ≤ 11 / 10 ^ 70 :=
  TailPrices.tailSt_add_tailAt_le

/-- **The tail half of (CP8)(c)** (`lem:tail-prices`(iv), `def:cp8`(c); T2's `tail_hCL_le`):
`∑_j q_j^{1/4}(s_j + a_j) ≤ (k_S + k_A)/2^{124}` at every scale. -/
theorem tail_hCL_le (C : ComparisonParts2 hW hMR hFour A) (L : ℕ) :
    ∑ j : PaperJt L, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L
        (.inr j) ^ ((1 : ℝ) / 4) *
      (symTotal (C.toK1.CL.π L) (.inr j) + skewTotal (C.toK1.CL.π L) (.inr j)) ≤
      (TailPrices.kS + TailPrices.kA) / 2 ^ 124 :=
  TailPrices.tail_hCL_le _ _ _ L

/-- **The tail atoms' price at every scale** (`lem:tail-prices`(iv); T2):
`∑_j (s_j + a_j) ≤ S_tail + A_tail ≤ 1.1·10⁻⁶⁹`. -/
theorem tail_price_le (C : ComparisonParts2 hW hMR hFour A) (L : ℕ) :
    ∑ j : PaperJt L, (symTotal (C.toK1.CL.π L) (.inr j) + skewTotal (C.toK1.CL.π L) (.inr j)) ≤
      11 / 10 ^ 70 := by
  have hS := C.toK1.tail_S L
  have hA := C.toK1.tail_A L
  have e : ∀ j : PaperJt L, symTotal (C.toK1.CL.π L) (.inr j) +
      skewTotal (C.toK1.CL.π L) (.inr j) =
      (C.toK1.tail (paperTail L j) (ComparisonLawPaper.P4_le_paperTail j)).toAtom.sprice
          (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) +
        (C.toK1.tail (paperTail L j) (ComparisonLawPaper.P4_le_paperTail j)).toAtom.aprice
          (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) := fun j => by
    rw [TailPrices.tail_symTotal_eq, TailPrices.tail_skewTotal_eq]
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib]
  have := C.St_At_le
  linarith

end ComparisonParts2

/-! ## `hSA` in reduced form -/

/-- **`S + A ≤ S^{ledger} + A^{ledger}` in reduced form** (`def:closing-quantities`, `def:cp4`(b);
K1's `SAExplicit_full`): the square-clique bound `H`, the upper per-record bounds `hR` with the
band charges `US`, `UA`, the twelve norm bounds of every middle block `hN` at the piece constants
`κ`, the signs `hK`, and one numerical inequality `hsum` (with `S_tail + A_tail` entered as
`11/10⁷⁰`). 16 fields. -/
structure SAParts (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
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
  /-- The band charges. Data. -/
  US : Fin 310 → ℕ → ℝ
  UA : Fin 310 → ℕ → ℝ
  /-- `∑_{𝔅 ∈ band} q_𝔅^{2a} r_𝔅^d ≤ 𝒰^s_{β,d}` (`cert:upper-band-inputs`). *Open*
  (numerical: prime sums over the bands). -/
  hUS : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
    blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ US β d
  hUA : ∀ β, ∀ d ∈ upperDegrees, ∑ b ∈ upperBand (specF hW A) bandIdx β,
    blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤ UA β d
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)` (`eq:signed-constants`,
  `lem:record:exact-marginal-e`(ii)). Data. -/
  κ : Fin 33 → MiddleConsts
  /-- **The twelve norm bounds of every middle block** (B8's `NormBounds`; `prop:signed-bounds`(a),
  (b),(e), `lem:record:exact-marginal-e`(ii), `lem:merge-repair`, `lem:record:accepting-c2`).
  *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn paperCell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)
  /-- The signs of the price coefficients `K_d(i)`. *Open* (numerical). -/
  hK : ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i
  /-- **The final numerical inequality** of `hSA`. *Open* (numerical). -/
  hsum : H + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d * US β d +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          UA β d) +
    ∑ i : Fin 33, (midK2 κ i * (PaperNumbers.chargeC2 i : ℝ) +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        (PaperNumbers.chargeC3 i : ℝ)) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

/-- **K1's `hSA` from the reduced form** (`SAExplicit_full`, with `MiddleNorms` from the twelve
norm bounds by `specNorm_of_bounds`, and the tail numbers by `St_At_le`). -/
theorem SAParts.toSAExplicit {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    {C : ComparisonParts2 hW hMR hFour A} (hBMOR : Target.BMOR) (NC : NumericalCertificates)
    (S : SAParts hW hMR hFour A C) : SAExplicit C.toK1.Ci :=
  C.toK1.SAExplicit_full hBMOR NC S.hq S.Cs S.Ca S.hCs S.hCa S.hR S.US S.UA S.hUS S.hUA S.κ
    (fun b i hs => specNorm_of_bounds hW (paperIn paperCell) (S.κ i) (blockLeast b)
      (specF hW A b) (C.blk b) (S.hN b i hs)) S.hK
    (by have := C.St_At_le; have := S.hsum; linarith)

/-! ## (CP6), (CP8)(c) -/

/-- The prefix atoms refined by `prop:record:matching`(i): the class-three blocks with a middle
specification (no square-clique atom, no upper block). -/
noncomputable def midAtom (hW : Target.Weil) (A : PaperAnalyticInputs paperCell) :
    PartVLaws.PaperAtom Blk → Bool
  | .inl _ => false
  | .inr b => !ComparisonLawPaper.specUpper (specF hW A b)

/-- **The open inputs of (CP6) and (CP8)(c)** with `hrepl` reduced (K1's `ofOthers`,
`prop:record:matching`(ii)), with the tail parts of `hrepl` and of (CP8)(c) proved (T2's
`tail_price_le`, `tail_hCL_le`). 8 fields. -/
structure EnvelopeParts2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs paperCell) (C : ComparisonParts2 hW hMR hFour A) where
  /-- The prefix refinement on the middle blocks (`prop:record:matching`(i),
  `prop:signed-sides`): per middle block and scale, the replaced records, the added positive
  diagonals and the refined bracket, with per-block bounds `KL`, `KR`; at the square-clique atoms
  and the upper blocks nothing is replaced (**proved**: `AtomRefinement.trivial`). *Open*: the
  bracket at a middle block (B8's `refined_bracket` at V3's frame reduces it to two fold and two
  matching brackets; the identification with `gramBracketTarget`, `comparisonLawTarget` is not
  done). -/
  MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn paperCell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true)
  /-- `T_K` (`prop:signed-sides`(iii)). Data. -/
  TK : ℝ
  /-- `∑_β KL β ≤ T_K`, `∑_β KR β ≤ T_K`. *Open* (finite sums of `MR`'s bounds). -/
  hK : ∑ β, MR.toPrefix.KL β ≤ TK ∧ ∑ β, MR.toPrefix.KR β ≤ TK
  /-- The price `T_pre` of the records not replaced at the prefix atoms (the paper's
  `T_oth = S_oth + A_oth + S_u + A_u (+10⁻¹²)` without the tail part). Data. -/
  Tpre : ℝ
  /-- The records not replaced at the prefix atoms cost at most `T_pre` at every scale
  (`prop:record:matching`(ii)): at the square-clique atoms and the upper blocks all records, at a
  middle block those outside `repl`. *Open* (a property of `CL`). The tail atoms (nothing
  replaced) cost at most `1.1·10⁻⁶⁹` (**proved**, `tail_price_le`). -/
  hothPre : ∀ L, ∑ β, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl β),
    (C.toK1.CL.π L (.inl β) t .sym + C.toK1.CL.π L (.inl β) t .skew) ≤ Tpre
  /-- The gate `T_K + T_pre + 11/10⁷⁰ ≤ T^{ledger}`. *Open* (numerical). -/
  hTK : TK + (Tpre + 11 / 10 ^ 70) ≤ targetLedger.T
  /-- The weighted (CP4) bound of the prefix atoms. Data. -/
  σpre : ℝ
  /-- The weighted (CP4) summability at the prefix atoms (`def:cp8`(c)). *Open* (analytic: the
  prices of the square-clique and class-three atoms, weighted by `q^{1/4}`). -/
  hCLpre : ∀ L, ∑ β, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L
      (.inl β) ^ ((1 : ℝ) / 4) *
    (symTotal (C.toK1.CL.π L) (.inl β) + skewTotal (C.toK1.CL.π L) (.inl β)) ≤ σpre

/-- K1's `EnvelopeParts` (`EnvelopeParts.ofOthers`, with `σ_CL = σ_pre + (k_S + k_A)/2^{124}`). -/
noncomputable def EnvelopeParts2.toK1 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs paperCell}
    {C : ComparisonParts2 hW hMR hFour A} (E : EnvelopeParts2 hW hMR hFour A C) :
    EnvelopeParts hW hMR hFour A C.toK1 :=
  EnvelopeParts.ofOthers E.MR.toPrefix E.TK E.hK (E.Tpre + 11 / 10 ^ 70)
    (fun L => by
      rw [Fintype.sum_sum_type]
      refine add_le_add (E.hothPre L) ?_
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) (C.tail_price_le L)
      show ∑ t ∈ univ \ ∅, _ = _
      rw [sdiff_empty, Finset.sum_add_distrib]
      rfl) E.hTK
    (E.σpre + (TailPrices.kS + TailPrices.kA) / 2 ^ 124) fun L => by
      rw [Fintype.sum_sum_type]
      exact add_le_add (E.hCLpre L) (C.tail_hCL_le L)

/-! ## The block data -/

/-- **The block data, second round**: C8's per-prime certificates, B6's block-level inputs, the
(CP4) inputs after B8/T2, the (CP6)/(CP8)(c) inputs with `hrepl` reduced. 4 fields. -/
structure FinalBlockData2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs (B8, T2). -/
  Cmp : ComparisonParts2 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The (CP6), (CP8)(c) inputs (B3, K1). -/
  Env : EnvelopeParts2 hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA) Cmp

/-- K1's `FinalBlockData`. -/
noncomputable def FinalBlockData2.toK1 {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} (D : FinalBlockData2 hW hMR hFour) :
    FinalBlockData hW hMR hFour where
  PC := D.PC.toPC hW hMR hFour
  BA := D.BA
  Cmp := D.Cmp.toK1
  Env := D.Env.toK1

/-! ## The classes (B10) and the sharp terms (B9) -/

/-- **The inputs of the joint bound `JB`, second round** (B10's `ClassPartsB10` with the class
energies through their steps). 5 fields. -/
structure ClassParts2 {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    (D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf)
    paperTail paperPr paperH Chamber) where
  /-- The data of the classes (`def:cp5`, `prop:closing-data`(d), `lem:middle-comparison-prices`,
  `cor:variance:final`(i),(iii)). *Open* (data; 23 sub-fields). -/
  cd : ClassData D.CL
  /-- The class energies by their steps and the upper prices of the diagonals
  (`thm:envelopes`(i), `prop:background-variance`(a), `lem:bracket-energy`). *Open*. -/
  ES : ClassEnergySteps D cd
  /-- The upper data of the class polynomial (B4's `PolynomialData`). *Open* (data with
  numerical gates). -/
  PD : PolynomialData ES.toED.toCI
  /-- (E1) for the selections in no class (`def:robust`), through G1's per-term inputs: the
  subset terms `hsub` and the coupled envelope pieces `hcoup`. *Open* (analytic). -/
  E1 : E1Inputs D
  /-- The joint mean allocation without its upper prices (`prop:record:mean-credit`,
  `cert:four-routes-closing`, `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open*
  (analytic `mean`; numerical `resid`, `alloc`, `hV`). -/
  MD : MeanData ES.toED

/-- **The joint bound `JB` from the class inputs** (B4's `MeanAllocation.jointBound` with B10's
`ED.toCI`, `ED.toCE`, `MD.toMA` and G1's (E1)), given `B ≤ B^{ledger}`; for any block layout. -/
theorem ClassParts2.jointBound {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {D : TheoremCBlock.ComparisonData targetDecay paperM0 (paperAtomMap blockOf) paperTail paperPr
      paperH Chamber} (C : ClassParts2 D) (hB : D.B ≤ targetLedger.B) :
    JointBound D targetLedger.jointConstant :=
  C.MD.toMA.jointBound MainAnchor.card_chamber C.PD (C.E1.toE1 targetDecay_nonneg) hB

/-- B10's `ClassPartsB10`. -/
noncomputable def ClassParts2.toB10 {D : TheoremCBlock.ComparisonData targetDecay paperM0
    (paperAtomMap bOf) paperTail paperPr paperH Chamber} (C : ClassParts2 D) : ClassPartsB10 D where
  cd := C.cd
  ED := C.ES.toED
  PD := C.PD
  E1 := C.E1.toE1 targetDecay_nonneg
  MD := C.MD

/-- **The inputs of `SF`, `fix`, `env` on the upgrade route, second round** (B5's `SharpParts`
with `fixC`, `envC` in B9's mean-bound form). 11 fields. Until 7 November 2026 this was
`SharpParts2`; it is now one of the routes to the generic `SharpParts2` below
(`SharpParts2U.toSharpParts2`). Its `fibre` is upgrade-only (`prop:density:production`). -/
structure SharpParts2U {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- The density endpoint `θ` (the paper's `ϑ = 1.014587`), below the catalog's `12/11`. -/
  θ : ℝ
  hθ : 0 < θ
  hθ' : θ ≤ 12 / 11
  /-- The relative error and the remainder constant of the sharp terms. -/
  ε : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ ε L
  hεt : Tendsto ε atTop (𝓝 0)
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  /-- **Per term of the coupled expansion of `lem:sharp-first`: the fibre-moment input**
  (`prop:density:production`, `lem:record:density-dc`, `lem:record:fibre-scale`). *Open*. -/
  fibre : Param.AtCounterexamples (Param.Params.ofDecay targetDecay) D.data.Y
    (fun L A => ∀ σ : (∀ b, Option (D.data.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ RecordExpansion.countVec (D.data.FS.tag L) σ j →
      ∀ f : (∀ b, EnvelopeInputsBlock.CPiece D.data L b),
      (∀ b, EnvelopeInputsBlock.cpieceCoef D.data L σ j b (f b) ≠ 0) →
        CoupledFibreMoment D.data L A f θ (ε L) c₁)
  /-- `fixC` in B9's mean-bound form (`lem:envelope-energy`, `lem:twointerval`(ii)). *Open*. -/
  fixM : FixMeansInputs (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise
  /-- `envC` in B9's mean-bound form (`lem:envelope-energy`, `lem:hyb:moment`). *Open*. -/
  envM : EnvMeansInputs (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise

/-- K1's `SharpParts` (`fixC := fixM.toCRT`, `envC := envM.toCRT`). -/
noncomputable def SharpParts2U.toK1 {hW : Target.Weil} {D : JointBlockDataTarget bOf hW}
    (S : SharpParts2U D) : SharpParts D where
  θ := S.θ
  hθ := S.hθ
  hθ' := S.hθ'
  ε := S.ε
  hε0 := S.hε0
  hεt := S.hεt
  c₁ := S.c₁
  hc₁ := S.hc₁
  fibre := S.fibre
  fixC := S.fixM.toCRT
  envC := S.envM.toCRT

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} {hW : Target.Weil}
  {D : JointBlockDataTarget blockOf hW}

/-- **G1's `SF`** from the upgrade-route sharp inputs (B5's `SharpFirstCoupledInputs.ofBlocks`
with the proved per-block moments `paperStageMoments_proved`); for any block layout. -/
noncomputable def SharpParts2U.SF (S : SharpParts2U D) :
    EnvelopeInputsBlock.SharpFirstInputs D.data :=
  (EnvelopeEnergiesPaper.SharpFirstCoupledInputs.ofBlocks D S.θ S.hθ
    (EnvelopeEnergiesPaper.paperStageMoments_proved hW D.In S.hθ S.hθ' D.spec)
    S.ε S.hε0 S.hεt S.c₁ S.hc₁ S.fibre).toSharpFirstInputs

end Generic

/-- **The inputs of `SF`, `fix`, `env`** (generic in the route, 7 November 2026): the obligation
`SF` (`lem:sharp-first`, `EnvelopeInputsBlock.SharpFirstInputs`) and B9's mean-bound forms of
`fixC` and `envC`. Routes: the upgrade `SharpParts2U.toSharpParts2` (with `Sh.fibre`) and the
baseline `ThetaOne.SharpPartsBase.toSharpParts2` (`ϑ = 1`, folded energies). -/
structure SharpParts2 {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
    {hW : Target.Weil} (D : JointBlockDataTarget blockOf hW) where
  /-- `SF`: the sharp first-stage terms (`lem:sharp-first`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs D.data
  /-- `fixC` in B9's mean-bound form (`lem:envelope-energy`, `lem:twointerval`(ii)). *Open*. -/
  fixM : FixMeansInputs (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise
  /-- `envC` in B9's mean-bound form (`lem:envelope-energy`, `lem:hyb:moment`). *Open*. -/
  envM : EnvMeansInputs (BlockAnchor.index_coprime_block D.data) D.data paper_pairwise

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B} {hW : Target.Weil}
  {D : JointBlockDataTarget blockOf hW}

/-- The upgrade route to the generic sharp inputs. -/
noncomputable def SharpParts2U.toSharpParts2 (S : SharpParts2U D) : SharpParts2 D where
  SF := S.SF
  fixM := S.fixM
  envM := S.envM

/-- **G1's `fix`** from B9's mean-bound form. -/
noncomputable def SharpParts2.fix (S : SharpParts2 D) :
    EnvelopeInputsBlock.FixedIntervalInputs (BlockAnchor.index_coprime_block D.data) D.data :=
  S.fixM.toCRT.toG1

/-- **G1's `env`** from B9's mean-bound form. -/
noncomputable def SharpParts2.env (S : SharpParts2 D) :
    EnvelopeInputsBlock.EnvelopeEnergyInputs (BlockAnchor.index_coprime_block D.data) D.data :=
  S.envM.toCRT.toG1

end Generic

end Sarkozy.MainFinal2
