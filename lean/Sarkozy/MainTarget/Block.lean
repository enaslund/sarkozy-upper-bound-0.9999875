module

public import Sarkozy.EnvelopeInputsBlock.Final
public import Sarkozy.TargetLedger.Closing
public import Sarkozy.MainTarget.IndexLaw

@[expose] public section

/-!
# The block-atom assembly at the target `a_T`: index law certified, envelopes per term

The `a₀` chain K0 (`BlockAnchor.Paper`) → CERT1 (`IndexCert.BlockCert`) → G1
(`EnvelopeInputsBlock.Final`), re-instantiated at the owner's target
`a_T = 212956239/250000000000` (`Target.epsTarget = 3/250000`, the bound `N^{0.999988}`), with the
closing discharged from the target ledger (`TargetLedger.targetLedger`, `Θ < 0.72`)
(since RG's rebase of 7 November 2026 the ledger's exponent `TargetLedger.targetDecay` is
`a_G = 71/10⁵`, its saving `10⁻⁵`, and `Θ < 0.72`; the `a_T` below names that exponent).

**What depends on the exponent, and what is reused.**
* *Reused unchanged* (no exponent): the reference on the block atoms
  (`BlockAnchor.blockPaperReference`), the transfer of `lem:record:density-can`
  (`TheoremCBlock.densityCancellation_paper_block`), the unit `L³⁶` bound of the tail laws
  (`TailUnit.tailLawFamily_unit`), `lem:imp:padic-envelope` (CERT1's `IndexCert.paperIndexBound`),
  G1's per-term bundles (`EnvelopeInputsBlock.EnvelopeBoundInputs` etc., all at a free `a`), and
  K0's Theorem C on the block atoms (free `a`).
* *Re-instantiated at `a_T`*:
  - the prices `def:price`: `paperSelAt blk a_T = q_β^{2a_T}` (`BlockAnchor.blockSel` at `a_T`);
    at `a₀` this is K0's `paperSel` (`paperSelAt_anchor`);
  - the index law's moment `R_I = M_pad(K)` at `a_T` (`MainTarget.paperRIAt`), with
    `IndexMomentBound` proved (`BlockCertDataTarget.indexMomentBound`, G1's computation at `a_T`);
  - the comparison data (CP2)–(CP8) at `a_T` (`BlockCertDataTarget`, CERT1's `BlockCertData` at
    `a_T`);
  - the ledger comparisons, now against `targetLedger` (`BlockFinalObligationsTarget`, G1's
    `BlockFinalObligations` at `a_T`).

**The index moment.** `cert:index-moment` at `a_T` (`M_pad(K) ≤ targetLedger.R_I`) is the
hypothesis `hR` of `main_target_paper_block_cert_of_hR` and `main_target_paper_block_final_of_hR`;
`Sarkozy.MainTarget.IndexMoment` proves it from H2″ (`Target.ThetaSmallRR`), and
`MainTarget.Main` assembles the two.

**Two forms of the obligations**, as at `a₀`:
* `BlockCertObligationsTarget` (CERT1's form): the four envelope hypotheses `hE1`, `hSF`, `hfix`,
  `henv` as propositions;
* `BlockFinalObligationsTarget` (G1's form): the same with the four replaced by G1's per-term
  bundles `E1`, `SF`, `fix`, `env`; `toCertObligations` maps it to CERT1's form.

K0's `BlockPaperObligations` (with `hIdx` in the data and `hR` as a field) is not restated: at
`a_T`, `hIdx` is CERT1's `IndexCert.paperIndexBound` from the start (`targetIndexLaw`), and `hR` is
a hypothesis of the theorems here.

**Field count.** Both structures have 13 fields (`Dp` and 12 others), with `BlockCertDataTarget`
of 11 (`μ₀`, `rp₀`, `inv₀`, `unif₀`, `hV`, `FS`, `GB`, `CL`, `ME`, `MC`, `SM`): 23 open leaves, as
CERT1's and G1's at `a₀`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.MainTarget

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.Comparison (PrimitiveLedger)
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger targetLedger_bounds)
open Sarkozy.CancellationSteps Sarkozy.PaperFrame Sarkozy.FourierArithmetic Sarkozy.Functional
  Sarkozy.IndexSupport Sarkozy.BlockFrame Sarkozy.MainAnchor Sarkozy.BlockAnchor
open Sarkozy.EnvelopeInputsParam (paperMomentFactor)

variable {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : PaperJ0 → Bk)

/-! ## The prices and the standing data at a free exponent -/

/-- **The paper's selection factor of the prefix block `β` at the price exponent `a`**
(`def:price`): `q_β^{2a}`, K0's `blockSel a`. Irreducible, like K0's `paperSel`, so that
elaboration never unfolds the product over the `2^{512}`-range of fixed primes
(`paperSelAt_eq` unfolds it). -/
@[irreducible] noncomputable def paperSelAt (a : ℝ) (β : Bk) : ℝ :=
  blockSel a paperPP paperEP blk β

omit [Fintype Bk] in
theorem paperSelAt_eq (a : ℝ) (β : Bk) : paperSelAt blk a β = blockSel a paperPP paperEP blk β := by
  unfold paperSelAt
  rfl

omit [Fintype Bk] in
theorem one_le_paperSelAt {a : ℝ} (ha : 0 ≤ a) (β : Bk) : 1 ≤ paperSelAt blk a β := by
  rw [paperSelAt_eq]
  exact one_le_blockSel ha one_le_paperPP blk β

omit [Fintype Bk] in
/-- At `a₀` the prices are K0's `paperSel`. -/
theorem paperSelAt_anchor : paperSelAt blk Params.anchorDecay = paperSel blk := by
  funext β
  rw [paperSelAt_eq, paperSel_eq]

/-- **The paper's standing data on the block atoms at the price exponent `a`** (`def:cp0`): K0's
`blockPaperStanding` with the prices `paperSelAt blk a`. -/
noncomputable def blockPaperStandingAt (a : ℝ) (ha : 0 ≤ a)
    (index : IndexLaw paperPr paperH Chamber) :
    TheoremCBlock.StandingData (Bk := Bk) paperM0 paperTail paperPr paperH Chamber where
  pp := paperPP
  ep := paperEP
  pp_prime := paperJ0_prime
  ep_pos := one_le_paperEP
  m₀_eq _ := rfl
  p_prime _ j := paperTail_prime j
  p_inj _ := Subtype.val_injective
  selPre := paperSelAt blk a
  one_le_selPre := one_le_paperSelAt blk ha
  Q := paperQueries
  index := index
  pr_prime := paperPr_prime
  pr_inj := Subtype.val_injective
  h_two := (paper_standing_fields).2.2.2.2.2.1
  modulus_coprime := paper_hcop0

/-- **The paper's index law at `a_T`**: the increments of `def:construction`(a), the depth tails
of `lem:imp:padic-envelope` (proved, `IndexCert.paperIndexBound`) and the moment
`R_I = M_pad(K)` at `a_T`. -/
noncomputable def targetIndexLaw : IndexLaw paperPr paperH Chamber :=
  Sarkozy.PaperData.paperIndexLaw
    (paperIndexEnvelopeAt targetDecay (by norm_num [targetDecay]) IndexCert.paperIndexBound)

theorem targetIndexLaw_R_I : targetIndexLaw.R_I = paperRIAt targetDecay := rfl

/-! ## The open parts of the comparison data at `a_T` -/

/-- **The open parts of the comparison data on the prefix atoms at `a_T`, with the index law
certified** (`def:cp0`–`def:cp8`, `def:construction`). CERT1's `BlockCertData` at the price
exponent `a_T`, priced by `paperSelAt blk a_T`. All *open* (Part V), with CERT1's (K0's) labels:
* `μ₀`, `rp₀`, `inv₀`, `unif₀`: the block laws of the prefix with (R2) at the cuts of `𝔉`, (R3)
  and uniform marginals (`def:construction`(b)); these do not depend on the exponent;
* `hV`: `lem:tail-law`(i), the validity of the tail inputs (spectral; no exponent);
* `FS`, `GB`, `CL`, `ME`, `MC`, `SM`: (CP2)–(CP4), (CP6)–(CP8) at `a_T` on the block atoms. -/
structure BlockCertDataTarget (hW : Target.Weil) where
  μ₀ : ∀ β, FiniteLaw (Slot → BlockRes paperM0 blk β)
  rp₀ : ∀ β, FamilyReflectionPositive (signedIntegral (μ₀ β).weight)
  inv₀ : ∀ β (a : ∀ i, (ZMod (blockModuli paperM0 blk β i))ˣ) (b : BlockRes paperM0 blk β),
    (∀ i, IsSquare ((a i : ZMod (blockModuli paperM0 blk β i)))) →
      ∀ F : (Slot → BlockRes paperM0 blk β) → ℝ,
        (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli paperM0 blk β) a b (z v))) =
          (μ₀ β).expect F
  unif₀ : ∀ β, HasUniformMarginals (μ₀ β)
  hV : PartVLaws.TailInputsValid PartV.P4
  FS : TheoremCBlock.FirstStage targetDecay paperM0 blk paperTail (paperSelAt blk targetDecay)
    (blockPaperReference blk hW μ₀ rp₀ inv₀ unif₀ hV)
  GB : TheoremCBlock.GramBracket targetDecay paperM0 blk paperTail (paperSelAt blk targetDecay) FS
  CL : TheoremCBlock.ComparisonLaw targetDecay paperM0 blk paperTail (paperSelAt blk targetDecay)
    paperPP paperEP paperQueries FS
  ME : TheoremCBlock.MatchingEnvelopes targetDecay paperM0 blk paperTail GB CL
  MC : TheoremCBlock.MeanCredit targetDecay paperM0 blk paperTail ME
  SM : TheoremCBlock.Summability targetDecay paperM0 blk paperTail ME

variable {blk}

/-- The comparison data at `a_T` on the block atoms, assembled from the open parts. -/
noncomputable def BlockCertDataTarget.toData {hW : Target.Weil} (Dp : BlockCertDataTarget blk hW) :
    TheoremCBlock.ComparisonData targetDecay paperM0 blk paperTail paperPr paperH Chamber where
  S := blockPaperStandingAt blk targetDecay targetDecay_nonneg targetIndexLaw
  R := blockPaperReference blk hW Dp.μ₀ Dp.rp₀ Dp.inv₀ Dp.unif₀ Dp.hV
  FS := Dp.FS
  GB := Dp.GB
  CL := Dp.CL
  ME := Dp.ME
  MC := Dp.MC
  SM := Dp.SM

/-- The selection factor of the block `β` in the assembled data is the paper's `q_β^{2a_T}`. -/
theorem BlockCertDataTarget.selPre_eq {hW : Target.Weil} (Dp : BlockCertDataTarget blk hW)
    (β : Bk) : Dp.toData.S.selPre β = blockSel targetDecay paperPP paperEP blk β :=
  paperSelAt_eq blk targetDecay β

/-- **`lem:record:density-can` for the assembled data**: D1's result transferred to the block
atoms (`TheoremCBlock.densityCancellation_paper_block`); it does not involve the exponent. -/
theorem BlockCertDataTarget.densityCancellation {hW : Target.Weil}
    (Dp : BlockCertDataTarget blk hW) :
    TheoremCBlock.DensityCancellation paperM0 blk paperTail paperPr paperH Dp.toData.R.P5
      Dp.toData.S.pp Dp.toData.S.ep :=
  TheoremCBlock.densityCancellation_paper_block blk

/-- **`hunit` for the assembled data**: the tail laws are V1's at the primes `≥ P₄`, with unit
mixed `L³⁶` above a threshold (D1's `TailUnit.tailLawFamily_unit`), as in K0's `hunit`. -/
theorem BlockCertDataTarget.hunit {hW : Target.Weil} (Dp : BlockCertDataTarget blk hW) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q →
      MixedLpBound (Dp.toData.R.μp q) 36 1 := by
  obtain ⟨p₀, hp₀⟩ := TailUnit.tailLawFamily_unit hW
  refine ⟨max p₀ PartV.P4, fun q _ hq hle => ?_⟩
  show MixedLpBound (PartVLaws.tailFamilyFrom PartV.P4 q) 36 1
  rw [PartVLaws.tailFamilyFrom_eq PartV.P4 q hq (le_of_max_le_right hle)]
  exact hp₀ q hq (le_of_max_le_left hle)

/-- **`IndexMomentBound` for the paper's index law at `a_T`** (`lem:hyb:moment`,
`prop:imp:padic-price`): the conductor moment of every query is exactly `R_I = M_pad(K)` at
`a_T`. G1's `paper_indexMomentBound_block` at `a_T`, with no hypothesis. -/
theorem BlockCertDataTarget.indexMomentBound {hW : Target.Weil}
    (Dp : BlockCertDataTarget blk hW) : EnvelopeInputsBlock.IndexMomentBound Dp.toData := by
  intro e
  have hw : EnvelopeInputsBlock.priceExponent targetDecay = targetDecay / 36 := by
    unfold EnvelopeInputsBlock.priceExponent
    ring
  have hL : ∏ q, momentFactor (paperPr q) (paperH q) (Dp.toData.S.index.t e q).tail
      (EnvelopeInputsBlock.priceExponent targetDecay) =
      ∏ q ∈ paperSmallPrimes, paperMomentFactor (targetDecay / 36) q := by
    rw [hw, ← Finset.prod_coe_sort paperSmallPrimes]
    refine Fintype.prod_congr _ _ fun q => ?_
    show momentFactor q.1 (paperH q) (Sarkozy.PaperData.paperDepthTail q) _ = _
    unfold paperMomentFactor paperH Sarkozy.PaperData.paperDepthTail paperPr
    rfl
  show (blockScale : ℝ) ^ EnvelopeInputsBlock.priceExponent targetDecay *
      ∏ q, momentFactor (paperPr q) (paperH q) (Dp.toData.S.index.t e q).tail
        (EnvelopeInputsBlock.priceExponent targetDecay) ≤ paperRIAt targetDecay
  rw [hL, paperRIAt_eq_prod (by norm_num [targetDecay]), hw]

/-! ## The remaining obligations at `a_T`, CERT1's form (envelope hypotheses as propositions) -/

variable (blk) in
/-- **Everything that remains between the tree and the target at `a_T`, for the paper's data on
its prefix atoms, with the index law certified.** CERT1's `BlockCertObligations` (K0's
`BlockPaperObligations` without `hR`) at the price exponent `a_T`, over `BlockCertDataTarget`,
with the ledger `targetLedger`. 13 fields: the open data `Dp` and 12 others, with CERT1's (K0's,
D1's, P1's) labels and statuses, now at `a_T`. `cert:index-moment` (`hR`) is a hypothesis of
`main_target_paper_block_cert_of_hR`, proved from H2″ in `MainTarget.IndexMoment`. -/
structure BlockCertObligationsTarget (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dp : BlockCertDataTarget blk hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a_T`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds targetDecay paperM0 blk paperTail Dp.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dp.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dp.toData.B * monomial (Dp.toData.CL.π L) ω else CB.phi L ω) ≤
      targetLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dp.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)), with the first-stage prices at the paper's block factors
  at `a_T`. *Open* (Part V). -/
  hL₀ : Dp.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dp.toData.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ targetLedger.S + targetLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dp.toData.MC.m
  /-- **(E1), the envelope bound with nonnegative remainders** (`lem:bracket-energy` at `ϑ`, via
  `prop:density:production`). *Open at `a_T`*. -/
  hE1 : Dp.toData.EnvelopeBoundNonneg
  /-- **The sharp first-stage terms** (`lem:sharp-first`, `lem:record:folded-energy`). *Open at
  `a_T`*. -/
  hSF : Dp.toData.SharpFirstTerms
  /-- **The fixed-interval envelope energies** (`lem:envelope-energy`). *Open at `a_T`*. -/
  hfix : Dp.toData.FixedIntervalEnvelopeEnergies (index_coprime_block Dp.toData)
  /-- **The envelope energies** (`lem:envelope-energy`). *Open at `a_T`*. -/
  henv : Dp.toData.EnvelopeEnergies (index_coprime_block Dp.toData)

/-- **The bound `N^{1 − a_T/71}` for the paper's data on its prefix atoms, from CERT1's form of
the obligations at `a_T` and the index moment** (`thm:main` at the target exponent, via
`thm:comparison` and `thm:density:induction` at `a = a_T`). From the literature inputs
(`Target.Weil` is used for the reference, `hunit` and the (R4) mixing), `cert:index-moment` at
`a_T` as the hypothesis `hR`, and `BlockCertObligationsTarget blk`, for any block assignment `blk`
of the fixed primes. The closing `Θ < 1` is the kernel-checked
`TargetLedger.targetLedger_bounds` (`Θ < 0.72`); `lem:record:density-can` is D1's,
transferred. The `a_T` analogue of K0's `main_anchor_paper_block` and CERT1's
`main_anchor_paper_block_cert`. -/
theorem main_target_paper_block_cert_of_hR (hWeil : Target.Weil)
    (_hMovingRoot : Target.MovingRoot)
    (_hFourCycle : Target.FourCycle) (hR : paperRIAt targetDecay ≤ targetLedger.R_I)
    (O : BlockCertObligationsTarget blk hWeil) : Target.SarkozyBound TargetLedger.targetSaving :=
  TargetLedger.ComparisonData.theoremC_classes_reduced_target_of_ledger O.Dp.toData
    (index_coprime_block O.Dp.toData) targetLedger_bounds card_chamber
    O.Dp.toData.B_nonneg O.hB O.hL₀ O.hT O.Dp.toData.S.index.hR_I hR O.hSA O.hm O.CB le_rfl
    O.hΨ O.hE1 O.hCB O.hSF O.Dp.densityCancellation O.hfix O.henv O.Dp.hunit

/-! ## The remaining obligations at `a_T`, G1's form (envelope hypotheses per term) -/

variable (blk) in
/-- **Everything that remains between the tree and the target at `a_T`, for the paper's data on
its prefix atoms, with the index law certified and the envelope hypotheses per term.** G1's
`BlockFinalObligations` at the price exponent `a_T`, over `BlockCertDataTarget`, with the ledger
`targetLedger` (the `a_T` ledger of `TargetLedger.Numerics`). 13 fields: the open data `Dp` and
12 others. Labels and statuses are G1's (K0's, D1's, P1's), now at `a_T`. -/
structure BlockFinalObligationsTarget (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dp : BlockCertDataTarget blk hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a_T`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds targetDecay paperM0 blk paperTail Dp.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dp.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dp.toData.B * monomial (Dp.toData.CL.π L) ω else CB.phi L ω) ≤
      targetLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dp.toData.B ≤ targetLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)), with the first-stage prices at the paper's block factors
  at `a_T`. *Open* (Part V). -/
  hL₀ : Dp.toData.L₀ ≤ targetLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dp.toData.ME.T ≤ targetLedger.T
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ targetLedger.S + targetLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : targetLedger.m₁ + 64 * ((targetLedger.deltaAlpha + targetLedger.deltaMatching +
    targetLedger.deltaOdd + targetLedger.deltaEven) + targetLedger.deltaUpper -
    targetLedger.upperError) ≤ Dp.toData.MC.m
  /-- **(E1), per term** (`lem:bracket-energy`, `lem:density:coupled`): the subset terms and the
  coupled sharp-first terms under the selected envelopes, at `a_T`, on the block atoms. *Open*
  (G1's `E1`). -/
  E1 : EnvelopeInputsBlock.EnvelopeBoundInputs Dp.toData
  /-- **The sharp first-stage terms, per term** (`lem:sharp-first`, `lem:density:coupled`), at
  `a_T`, on the block atoms. *Open* (G1's `SF`). -/
  SF : EnvelopeInputsBlock.SharpFirstInputs Dp.toData
  /-- **The fixed-interval envelope energies, per term** (`lem:envelope-energy`,
  `lem:hyb:moment`), at `a_T`, on the block atoms. *Open* (G1's `fix`). -/
  fix : EnvelopeInputsBlock.FixedIntervalInputs (index_coprime_block Dp.toData) Dp.toData
  /-- **The envelope energies, per term** (`lem:envelope-energy`, `lem:hyb:moment`), at `a_T`, on
  the block atoms. *Open* (G1's `env`). -/
  env : EnvelopeInputsBlock.EnvelopeEnergyInputs (index_coprime_block Dp.toData) Dp.toData

/-- **CERT1's form of the obligations from the per-term inputs**: the four envelope hypotheses at
`a_T` are I1's reductions (G1's bundles), with `0 ≤ a_T` and the paper's `IndexMomentBound` at
`a_T` (`BlockCertDataTarget.indexMomentBound`); the other nine fields are copied. G1's
`BlockFinalObligations.toCertObligations` at `a_T`. -/
noncomputable def BlockFinalObligationsTarget.toCertObligations {hW : Target.Weil}
    (O : BlockFinalObligationsTarget blk hW) : BlockCertObligationsTarget blk hW where
  Dp := O.Dp
  CB := O.CB
  hΨ := O.hΨ
  hCB := O.hCB
  hB := O.hB
  hL₀ := O.hL₀
  hT := O.hT
  hSA := O.hSA
  hm := O.hm
  hE1 := O.E1.envelopeBoundNonneg targetDecay_nonneg
  hSF := O.SF.sharpFirstTerms targetDecay_nonneg
  hfix := O.fix.fixedIntervalEnvelopeEnergies (index_coprime_block O.Dp.toData)
    targetDecay_nonneg O.Dp.indexMomentBound
  henv := O.env.envelopeEnergies (index_coprime_block O.Dp.toData) targetDecay_nonneg
    O.Dp.indexMomentBound

/-- **The bound `N^{1 − a_T/71}` for the paper's data on its prefix atoms, from G1's form of the
obligations at `a_T` and the index moment** (`thm:main` at the target exponent): CERT1's form
(`main_target_paper_block_cert_of_hR`) with `BlockFinalObligationsTarget.toCertObligations`. The
`a_T` analogue of G1's `main_anchor_paper_block_final`, with `hR` as a hypothesis. -/
theorem main_target_paper_block_final_of_hR (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hR : paperRIAt targetDecay ≤ targetLedger.R_I)
    (O : BlockFinalObligationsTarget blk hWeil) : Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_cert_of_hR hWeil hMovingRoot hFourCycle hR
    O.toCertObligations

end Sarkozy.MainTarget
