module

public import Sarkozy.MainFinalF1.K1
public import Sarkozy.MainFinalF1.Tail

@[expose] public section

/-!
# K2's layer at `f1Cell` (F1P)

K2's `MainFinal2/Structure.lean` (`MiddleEstimates`, `SignedSpec`, `SpecNormBounds`,
`specNorm_of_bounds`) and `MainFinal2/Obligations.lean` (`ComparisonParts2`, `SAParts`, `midAtom`,
`EnvelopeParts2`, `FinalBlockData2` and their `toK1` maps) with `paperCell` replaced by `f1Cell`,
and C10's K2-level `MainFinalObligations2J` (`MainFinalJ/Main.lean`) at `f1Cell` without `hHist`.

**Partition-dependent changes.**
* `SAParts.toSAExplicit` takes `BMOR`, `ThetaSmallRR` in place of N1's `NumericalCertificates` (at
  `paperCell`: `numericalCertificates_of_hist hHist`), through `SAExplicit_fullF1`; the final
  inequality `SAParts.hsum` is stated at N2's numbers `f1c2`, `f1c3` in place of `chargeC2`,
  `chargeC3`.
* `MainFinalObligations2J` has no field `hHist`.

Everything else is K2's, verbatim up to the cell; `PrimeCertificates2`, `BlockAnalytic`, the
refinements `MidRefinement`, the class inputs `ClassParts2J` and the sharp inputs `SharpParts2` are
partition-independent and reused.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap PrefixCoord
  blockPrimes MiddleUniformInputs MiddleIndividualInputs MiddleCoherentInputs)
open Sarkozy.EnvelopesPaper (PrefixRefinement)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted SAExplicit tailNe
  UpperAtomInputs upperNe upperBand blockSel)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.SignedComponents (DefectConstants DefectSpec FoldSpec SignedEstimates NormBounds
  paperComponents)
open Sarkozy.MainFinal (PrimeCertificates BlockAnalytic hCF MiddleConsts SpecNorm midK2 midK3 midK4
  midK5 pieceScale)
open Sarkozy.MainFinal2 (PrimeCertificates2 tPaper tPaper_nonneg tPaper_le_one normSizes_of_bounds
  MidRefinement SharpParts2)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3)

/-! ## K2's `Structure.lean` at `f1Cell` -/


/-- **The estimates of the signed fold components of a middle block** (`lem:signed-components`(b):
rows, columns and `z_{uv}` of `U_{uv}` within `η_p` of `1`, the paper's `η_c = 10q`;
`lem:old-f-law`(a): `|g₀ − 1| ≤ e_p` on `H_F`, the paper's `e₀`), at every prime of the block and
every component, at `t = 127/500`. *Hypothesis* (analytic: Paley counting, `lem:paley-triple`(b)
and H1 for the rows; the formula for `g₀`). `η`, `e` are data with `0 ≤ η, e < 1`. -/
structure MiddleEstimates (b : Blk) (hne : MiddleNonempty (blockPrimes bOf b)) where
  /-- `η_p` (the paper's `10/p`). Data. -/
  η : {j : PaperJ0 // paperAtomMap bOf j = .inr b} → ℝ
  /-- `e_p` (the paper's `e₀(p)`). Data. -/
  e : {j : PaperJ0 // paperAtomMap bOf j = .inr b} → ℝ
  hη : ∀ i, 0 ≤ η i
  hη1 : ∀ i, η i < 1
  he : ∀ i, 0 ≤ e i
  he1 : ∀ i, e i < 1
  /-- The estimates at every prime and component. *Open* (analytic). -/
  E : ∀ i c, SignedEstimates (hne.F2 i) tPaper c (η i) (e i)

/-- **The defect constants `M_c` of a middle block** from the estimates
(`lem:signed-components`(c), proved: `DefectConstants.ofEstimates`). -/
noncomputable def MiddleEstimates.toDC {b : Blk} {hne : MiddleNonempty (blockPrimes bOf b)}
    (M : MiddleEstimates b hne) : DefectConstants b hne tPaper_nonneg tPaper_le_one :=
  SignedComponents.DefectConstants.ofEstimates b hne tPaper_nonneg tPaper_le_one M.η M.e M.hη
    M.hη1 M.he M.he1 M.E

/-- **The (CP4) inputs of a class-three block with B8's reduction**: B2's `UpperAtomInputs` on an
upper block (`prop:record:upper`(i)); the signed estimates on a middle block (any root). -/
def SignedSpec (hW : Target.Weil) {b : Blk} : PaperBlockSpec bOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes bOf b) (upperNe hW U) U.W U.r)
  | .middleUniform M => ULift (MiddleEstimates b M.hne)
  | .middleIndividual M => ULift (MiddleEstimates b M.hne)
  | .middleCoherent M => ULift (MiddleEstimates b M.hne)

/-- B8's `DefectSpec` from the signed estimates. -/
noncomputable def SignedSpec.toDefect (hW : Target.Weil) {b : Blk} :
    (S : PaperBlockSpec bOf b) → SignedSpec hW S → DefectSpec hW tPaper_nonneg tPaper_le_one S
  | .upper _, U => U
  | .middleUniform _, M => ⟨M.down.toDC⟩
  | .middleIndividual _, M => ⟨M.down.toDC⟩
  | .middleCoherent _, M => ⟨M.down.toDC⟩

/-- **B7's `SpecData` of a block from the signed estimates**: on a middle block B8's `ofFold` with
the paper's fold components `paperComponents` at `t = 127/500` (`ReplacementData` constructed). -/
noncomputable def SignedSpec.toSpecData (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (S : PaperBlockSpec bOf b) (E : SignedSpec hW S) : SpecData hW In S :=
  FoldSpec.toSpecData hW In tPaper_nonneg tPaper_le_one S
    (DefectSpec.toFoldSpec hW tPaper_nonneg tPaper_le_one S (SignedSpec.toDefect hW S E))

/-- **The paper's twelve norm bounds of a middle block** for the constructed records
(`prop:signed-bounds`(a),(b),(e), `lem:record:exact-marginal-e`(ii), the table of
`lem:merge-repair`, `lem:record:accepting-c2`; B8's `NormBounds`), at the piece constants `κ` and
the least prime `bl`. `True` on an upper block. -/
def SpecNormBounds (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk} (κ : MiddleConsts)
    (bl : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => NormBounds (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (uniformRoot _ M.hne) M.W M.I M.hr (In.bmin b) (paperComponents E.down.toDC) tPaper bl
      κ.sF κ.aF κ.ℓ κ.sE κ.aE
  | .middleIndividual M, E => NormBounds (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (individualBlockRoot _ M.u M.hne.L2) M.W M.I M.hr (In.bmin b) (paperComponents E.down.toDC)
      tPaper bl κ.sF κ.aF κ.ℓ κ.sE κ.aE
  | .middleCoherent M, E => NormBounds (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (coherentBlockRoot _ M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ κ.sE κ.aE

/-- **K1's `SpecNorm` from the twelve norm bounds** (`normSizes_of_bounds` on every root). -/
theorem specNorm_of_bounds (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) (bl : ℝ) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecNormBounds hW In κ bl S E →
      SpecNorm hW In κ bl S (SignedSpec.toSpecData hW In S E)
  | .upper _, _, _ => trivial
  | .middleUniform _, _, NB => normSizes_of_bounds _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one NB
  | .middleIndividual _, _, NB =>
      normSizes_of_bounds _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one NB
  | .middleCoherent _, _, NB =>
      normSizes_of_bounds _ _ _ _ _ _ _ _ _ tPaper_nonneg tPaper_le_one NB

/-! ## K2's `Obligations.lean` at `f1Cell` -/


/-- **The open inputs of (CP4)** (`def:cp4`) after B8 and T2: the square-clique deletions, per
class-three block the signed estimates (middle) or B2's upper inputs (upper), and per tail prime
the repairs of the changed records with their cap bounds. 4 fields. -/
structure ComparisonParts2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) where
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
  {A : PaperAnalyticInputs f1Cell}

/-- **K1's `ComparisonParts`** (T2's `ofTailCapsPaper`; the tail fields `tail_S`, `tail_A`, `St`,
`At` and the cap ledger proved; the middle `ReplacementData` constructed by B8's `ofFold`). -/
noncomputable def toK1 (C : ComparisonParts2 hW hMR hFour A) : ComparisonParts hW hMR hFour A :=
  ofTailCapsPaper C.clique
    (fun b => SignedSpec.toSpecData hW (paperIn f1Cell) (specF hW A b) (C.blk b)) C.Rp C.hcap

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
  MainFinalF1.tail_hCL_le _ _ _ L

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
    rw [MainFinalF1.tail_symTotal_eq, MainFinalF1.tail_skewTotal_eq]
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
    SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)
  /-- The signs of the price coefficients `K_d(i)`. *Open* (numerical). -/
  hK : ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i
  /-- **The final numerical inequality** of `hSA`. *Open* (numerical). -/
  hsum : H + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d * US β d +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          UA β d) +
    ∑ i : Fin 33, (midK2 κ i * f1c2 i +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        f1c3 i) + 11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A

/-- **K1's `hSA` from the reduced form** (`SAExplicit_full`, with `MiddleNorms` from the twelve
norm bounds by `specNorm_of_bounds`, and the tail numbers by `St_At_le`). -/
theorem SAParts.toSAExplicit {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonParts2 hW hMR hFour A} (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (S : SAParts hW hMR hFour A C) : SAExplicit C.toK1.Ci :=
  C.toK1.SAExplicit_fullF1 hBMOR hRR S.hq S.Cs S.Ca S.hCs S.hCa S.hR S.US S.UA S.hUS S.hUA S.κ
    (fun b i hs => specNorm_of_bounds hW (paperIn f1Cell) (S.κ i) (blockLeast b)
      (specF hW A b) (C.blk b) (S.hN b i hs)) S.hK
    (by have := C.St_At_le; have := S.hsum; linarith)

/-! ## (CP6), (CP8)(c) -/

/-- The prefix atoms refined by `prop:record:matching`(i): the class-three blocks with a middle
specification (no square-clique atom, no upper block). -/
noncomputable def midAtom (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell) :
    PartVLaws.PaperAtom Blk → Bool
  | .inl _ => false
  | .inr b => !ComparisonLawPaper.specUpper (specF hW A b)

/-- **The open inputs of (CP6) and (CP8)(c)** with `hrepl` reduced (K1's `ofOthers`,
`prop:record:matching`(ii)), with the tail parts of `hrepl` and of (CP8)(c) proved (T2's
`tail_price_le`, `tail_hCL_le`). 8 fields. -/
structure EnvelopeParts2 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonParts2 hW hMR hFour A) where
  /-- The prefix refinement on the middle blocks (`prop:record:matching`(i),
  `prop:signed-sides`): per middle block and scale, the replaced records, the added positive
  diagonals and the refined bracket, with per-block bounds `KL`, `KR`; at the square-clique atoms
  and the upper blocks nothing is replaced (**proved**: `AtomRefinement.trivial`). *Open*: the
  bracket at a middle block (B8's `refined_bracket` at V3's frame reduces it to two fold and two
  matching brackets; the identification with `gramBracketTarget`, `comparisonLawTarget` is not
  done). -/
  MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
    (paperIn f1Cell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true)
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
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
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

/-! ## C10's K2-level obligations at `f1Cell`, without `hHist` -/

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **K2's obligations with the combined gate at `f1Cell`** (C10's `MainFinalObligations2J`
without `hHist`). 4 fields. -/
structure MainFinalObligations2J (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) where
  Dv : FinalBlockData2 hW hMR hFour
  SA : SAParts hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  Cls : ClassData.ClassParts2J Dv.toK1.data
  Sh : SharpParts2 Dv.toK1.toJoint

/-- K1's layer at `f1Cell` (K2's `toK1` maps; `hSA` through `SAExplicit_fullF1`). -/
noncomputable def MainFinalObligations2J.toK1J (hBMOR : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (O : MainFinalObligations2J hW hMR hFour) : MainFinalObligationsJ hW hMR hFour where
  Dv := O.Dv.toK1
  hSA := O.SA.toSAExplicit hBMOR hRR
  Cls := O.Cls
  Sh := O.Sh

end Sarkozy.MainFinalF1
