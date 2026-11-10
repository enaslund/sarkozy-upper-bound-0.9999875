module

public import Sarkozy.MainFinal2.Bundles
public import Sarkozy.MainFinal2.MidRplus
public import Sarkozy.MiddleCertificates.All
public import Sarkozy.TailPrices.All

@[expose] public section

/-!
# The combined obligations of the main statement, second round (K2)

`thm:main` at `ε = a_T/71` (`N^{1 − a_T/71}`), joint form, on the paper's construction in the
ALLp configuration. K1's `MainFinal.MainFinalObligations` with every newer reduction plugged in:

* **C8, C9** (`MiddleCertificates/`, `MiddlePrimeInputs/`): the per-prime certificates `h10`,
  `h21` from route A along C9's `R₊` chain (the 198 class-three grid tests of `cert:layer12-grid`,
  `ε_V`, `η_Q`, `Λ_D`, `ρ_row`, `M_⋆`, `z_⋆` **proved**), per prime the rest `MidRplusData`; `h20`
  from W3-form bounds `L20Inputs` (the bridge `K₀ = 2¹⁶ K` **proved**), above `2⁴⁰` through C9's
  rectangle route `L20RectData` — `PrimeCertificates2`.
* **B8** (`SignedComponents/`): B7's `ReplacementData` on every middle block **constructed**
  (`ofFold` at the paper's `t = 127/500`, fold components `P_{uv}` of `lem:signed-components`
  with the paper's repair constant `M_c`), from the estimates `SignedEstimates` of
  `lem:signed-components`(b) and `lem:old-f-law`(a) — `MiddleEstimates`, `SignedSpec`.
  The twelve norm bounds `NormBounds` enter `hSA` (`SpecNormBounds`).
* **T2** (`TailPrices/`): the tail atoms from the repairs at the paper's caps
  (`ofTailCapsPaper`): the accepted part, the deleted records, the envelopes, `tail_S`, `tail_A`,
  `St`, `At` and the cap ledger `cert:tail-caps` **proved**; per tail prime a `TailRepair` of each
  changed record and the cap bounds remain — `ComparisonParts2`.
* **K1's own reductions, now plugged in**: `hSA` through `SAExplicit_full` (`SAParts`), `hrepl`
  through `EnvelopeParts.ofOthers` (`EnvelopeParts2`).
* **N2** (`AnalyticCells/`): the 66 charge bounds from `HistogramClaim` alone (the cells above
  `X_Ch` **proved**).
* **B10** (`ClassInputsPaper/`): `CI.robust` and `MA.upper` **proved**; `CE.energy` through the
  steps (`ClassEnergySteps`) — `ClassParts2`.
* **B9** (`BracketEnergy/`): `fixC`, `envC` in mean-bound form (bracket removed, **proved**) —
  `SharpParts2`.

Every remaining open input is a field whose type is the type its owner uses: B11's steps slot into
`ClassEnergySteps.hsteps` (`StepsFamily`).
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
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference TailInputsCorr paperAtomMap PrefixCoord
  blockPrimes MiddleUniformInputs MiddleIndividualInputs MiddleCoherentInputs)
open Sarkozy.EnvelopesPaper (PrefixRefinement)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted SAExplicit tailNe
  UpperAtomInputs upperNe)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.SignedComponents (DefectConstants DefectSpec FoldSpec SignedEstimates NormBounds
  paperComponents)
open Sarkozy.ClassBoundsPaper (PolynomialData)
open Sarkozy.ClassInputsPaper (ClassData ClassEnergyData MeanData ClassPartsB10)
open Sarkozy.EnvelopeEnergiesPaper (CoupledFibreMoment paper_pairwise)

/-! ## C8: the per-prime certificates -/

/-- **The per-prime cut certificates with C8's and C9's reductions** (`cert:upper-root-caps`,
`lem:front12:reference`(ii), `prop:l20-collisions`, `cert:l20-grid`, `lem:layer12-caps`(b),
`cert:layer12-grid`, `thm:spectral-criterion`(a),(d)). *Hypotheses* (analytic, one statement per
prime of a piece or band). 5 fields. -/
structure PrimeCertificates2 : Prop where
  /-- Upper bands (310): `UpperRootCaps k` (`cert:upper-root-caps`). *Open*. -/
  hUC : ∀ k, BlockAdapter.UpperRootCaps k
  /-- Middle, the 29 uniform pieces below `2⁴⁰`, L20: W3-form bounds
  `-allpG p^{-1/2}‖f‖² ≤ ⟨f, T f⟩ ≤ (1 + allpB/p)‖f‖²` for W3's `T = K₀/Z₀` at every class-three
  prime of the piece (`prop:l20-collisions`, `cert:l20-grid`; C8's bridge `K₀ = 2¹⁶ K` proved).
  *Open* (C8's `l20W3Bounds_of_balanced` with the class data of `N_A` at an anchor `Q ≤ X_i`). -/
  h20lo : ∀ i, allpIndividual i = none → pieceStart i < 2 ^ 40 → MiddleCertificates.L20Inputs i
  /-- Middle, the uniform pieces from `2⁴⁰` (piece 32, `2⁴⁵`), L20: C9's rectangle route with the
  42 classes of `N_A` supplied; per class-three prime the remaining inputs `L20RectData`
  (`𝔪`, `N_ns`, `m_⋆`, `χ⁺_p`, the gates). *Open*. -/
  h20hi : ∀ i, allpIndividual i = none → 2 ^ 40 ≤ pieceStart i → ∀ (p : ℕ) [Fact p.Prime],
    p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i → Nonempty (L20RectData i p)
  /-- Middle, 33 pieces, L10: C9's `R₊` route (`ε_V`, `η_Q`, `Λ_D`, `ρ_row`, `M_⋆`, `z_⋆` proved);
  per class-three prime the remaining inputs `MidRplusData` (the `N_ns` class data, `D_col`, the
  coupling numbers, and `hcbar`, `hηB`, `hB` against C8's bars). *Open*. -/
  h10 : ∀ i (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
    Nonempty (MidRplusData .l10 i p)
  /-- Middle, 31 uniform pieces, L21: the same for the L21 layer cut. *Open*. -/
  h21 : ∀ i, allpIndividual i = none → ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 →
    pieceStart i ≤ p → p < pieceStop i → Nonempty (MidRplusData .l21 i p)

/-- K1's `PrimeCertificates` from C8's and C9's inputs (`middleRootCaps_l20_of_W3` with
`l20Inputs_of_rect` above `2⁴⁰`, `middleRootCaps_l10`, `middleL21Caps_of_inputs` with
`midInputs_of_Rplus`). -/
theorem PrimeCertificates2.toPC (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (P : PrimeCertificates2) : PrimeCertificates where
  hUC := P.hUC
  h20 i hi := MiddleCertificates.middleRootCaps_l20_of_W3 (by
    rcases lt_or_ge (pieceStart i) (2 ^ 40) with h | h
    · exact P.h20lo i hi h
    · exact l20Inputs_of_rect hW hFour h (P.h20hi i hi h))
  h10 i := MiddleCertificates.middleRootCaps_l10 (midInputs_of_Rplus hW hMR (P.h10 i))
  h21 i hi := MiddleCertificates.middleL21Caps_of_inputs (midInputs_of_Rplus hW hMR (P.h21 i hi))

/-! ## B8: the middle blocks from the signed estimates -/

/-- The paper's fold parameter `t = 127/500` (`def:record:mixture`). -/
noncomputable def tPaper : ℝ := 127 / 500

theorem tPaper_nonneg : 0 ≤ tPaper := by norm_num [tPaper]

theorem tPaper_le_one : tPaper ≤ 1 := by norm_num [tPaper]

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

end Sarkozy.MainFinal2
