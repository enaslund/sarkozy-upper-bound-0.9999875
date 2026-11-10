module

public import Sarkozy.MainFinalF1c.Tail
public import Sarkozy.MainFinalF1b.Main
public import Sarkozy.MainFinalF1c.Priced

@[expose] public section

/-!
# The F1 main statement with the tail repairs proved (`main_target_f1_final3e`)

F1b's `main_target_f1_final3d` with K2's fields `Cmp.Rp` and `Cmp.hcap` **removed**: the tail
comparison inputs come from TC's (F7) repairs `TailCorrelations.tailRp hW` (proved from H1, with the
correlation bounds (F2)), and the tail prices are taken at TC's constants (`MainFinalF1c.Tail`)
instead of the paper's caps `cert:tail-caps`. What hard-coded the caps is restated:

* `hcap` (`cert:tail-caps`): gone, since `ComparisonPartsTC` has the single field `blkU`;
* `piRep`, `kA`, `kS`: replaced by `piRepTC`, `kATC = 2¹⁰²`, `kSTC = 2¹⁰³` (`Tail.lean`);
* the literal `11/10⁷⁰` (`S_tail + A_tail`) in `SAParts3.hsum` and in `hmid`: replaced by
  `tailStTC + tailAtTC = 3/2¹⁵¹` (`tailTC_eq`; `< 10⁻⁴⁴`, `tailTC_lt`).

Layers, copied from `MainFinalF1/K3.lean`, `Env.lean`, `K2.lean` and `MainFinalF1b/Main.lean`
with `ComparisonParts3` replaced by `ComparisonPartsTC` and the composite maps written directly
into K1's types (every proof is the original one, up to the tail number):

* **`ComparisonPartsTC`** (1 field: `blkU`), `toK1` (T2's tail chain with `tailRp`; the middle
  records priced at their norm bounds at `κ′ = paperKappa` and the least prime, RP:
  `SignedSpec.toSpecDataAt`, `Priced.lean`; `toK1_prices`: they are the bounds), `cliquePrice_le`
  (C10);
* **`SAPartsTC`** (`SAParts3` with the tail term `tailStTC + tailAtTC`, and, since RP, the side
  condition `hκP : paperKappa ≤ κ` that ties the free constants to the prices; 10 fields) and
  `toSAExplicit` (`SAParts3.toE3`, `toE2`, `toParts2`, `toSAExplicit` composed);
* `midOthersK1`, `hothT_of_midK1` (`midOthers`, `hothT_of_mid` at K1's `ComparisonParts`, the tail
  term a parameter); **`envTC`** (`envOf`, `EnvelopePartsE2.toParts2`, `EnvelopeParts2.toK1`
  composed, with `T_oth = T − T_K`, `σ_CL = σ_pre + (kSTC + kATC)/2¹²⁴`);
* **`FinalBlockData3e`** (`FinalBlockData3b` at `ComparisonPartsTC`; 4 fields) and `toK1`;
* **`MainFinalObligations3e`** (5 fields), `toJB`, **`main_target_f1_final3e`**,
  **`main_goal_f1c`** (at `TargetGoal.epsGoal` via `Target.sarkozyBound_mono`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinalF1c

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg targetLedger)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (PaperBlockSpec v2Reference paperAtomMap PrefixCoord blockPrimes PaperAtom)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted tailNe UpperAtomInputs upperNe
  upperBand blockSel specUpper SAExplicit)
open Sarkozy.MainFinal (PrimeCertificates BlockAnalytic hCF MiddleConsts midK2 midK3 midK4 midK5
  pieceScale)
open Sarkozy.MainFinal2 (PrimeCertificates2 MidRefinement SharpParts2)
open Sarkozy.NumericalFields (KappaNonneg midK_signs bandBound)
open Sarkozy.AnalyticCells (f1Cell f1c2 f1c3)
open Sarkozy.EnvPrefix (Uup)
open Sarkozy.MainFinalF1 (ComparisonParts EnvelopeParts FinalBlockData bOf specF Blk analyticInputs
  UpperSpec SignedSpec SpecNormBounds specNorm_of_bounds cliqueK1 cliqueK1_ω_le midAtom pre_total
  pre_price_clique pre_price_block upper_price_le σpreOf hCLpre_proved upperBand_le_bandBound)
open Sarkozy.MainFinalF1b (ClassPartsE4B MainFinalObligationsJB main_target_f1_finalJB)
open Sarkozy.HsumProof (paperKappa)

/-! ## The comparison inputs -/

/-- **The open inputs of (CP4) with the tail proved**: `MainFinalF1.ComparisonParts3` without `Rp`
and `hcap` (the tail repairs are TC's `tailRp`, proved from H1). 1 field. -/
structure ComparisonPartsTC (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) where
  /-- Upper blocks only (E1's `UpperSpec`): B2's `UpperAtomInputs` (`prop:record:upper`(i);
  *open*); nothing on a middle block (`MiddleEstimates` proved by E1). -/
  blkU : ∀ b : Blk, UpperSpec hW (specF hW A b)

namespace ComparisonPartsTC

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- The signed block inputs (E1's `UpperSpec.toSigned`, as in `ComparisonParts3.toK2`). -/
noncomputable def blk (C : ComparisonPartsTC hW hMR hFour A) (b : Blk) :
    SignedSpec hW (specF hW A b) :=
  UpperSpec.toSigned hW (specF hW A b) (C.blkU b)

/-- **K1's `ComparisonParts`**: the clique deletions of C10 (`cliqueK1`), the block inputs as in
`ComparisonParts3.toK2.toK1` but with the middle records priced at their norm bounds at the
block's constants `blockKappa b` (`κ′ = paperKappa` of its piece) and least prime (RP:
`SignedSpec.toSpecDataAt`; the records are the same), and the tail from TC's repairs
(`ofTailTC`). -/
noncomputable def toK1 (C : ComparisonPartsTC hW hMR hFour A) : ComparisonParts hW hMR hFour A :=
  ofTailTC (cliqueK1 hW hMR hFour A)
    (fun b => SignedSpec.toSpecDataAt hW (paperIn f1Cell) (blockKappa b) (blockLeast b)
      (specF hW A b) (C.blk b))

/-- **The middle prices of `toK1` are the bounds** (RP): given the twelve norm bounds at
`κ′ = paperKappa` (which the front proves, `NormBoundsPaper.hNG`), the prices of every middle block
of piece `i` are exactly `boundN` at `paperKappa i` and its least prime (`specPrices_at`). -/
theorem toK1_prices (C : ComparisonPartsTC hW hMR hFour A)
    (hN : ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b) (C.blk b))
    (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) :
    SpecPrices hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b) (C.toK1.blk b) := by
  change SpecPrices hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
    (SignedSpec.toSpecDataAt hW (paperIn f1Cell) (blockKappa b) (blockLeast b) (specF hW A b)
      (C.blk b))
  rw [blockKappa_eq hs]
  exact specPrices_at hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b) (C.blk b)
    (hN b i hs)

/-- The tail numbers of `toK1`: `S_tail + A_tail = tailStTC + tailAtTC`. -/
theorem St_At (C : ComparisonPartsTC hW hMR hFour A) :
    C.toK1.St + C.toK1.At = tailStTC + tailAtTC := rfl

/-- **The clique bound, proved** (C10; `ComparisonParts3.cliquePrice_le`, same proof). -/
theorem cliquePrice_le (C : ComparisonPartsTC hW hMR hFour A) :
    ∑ q, C.toK1.Ci.cliquePrice q ≤ 12 / 2 ^ 534 := by
  apply CliqueDeletion.ComparisonInputs.cliquePrice_sum_le
  intro q
  show (cliqueK1 hW hMR hFour A q).ω ≤ _
  exact cliqueK1_ω_le hW hMR hFour A q

end ComparisonPartsTC

/-! ## `hSA` -/

/-- **`S + A ≤ S^{ledger} + A^{ledger}` in reduced form**: `MainFinalF1.SAParts3` at
`ComparisonPartsTC`, with the tail bound `tailStTC + tailAtTC` (TC's constants) entered in place
of `11/10⁷⁰`, and the side condition `hκP` (RP). 10 fields. -/
structure SAPartsTC (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : PaperAnalyticInputs f1Cell) (C : ComparisonPartsTC hW hMR hFour A) where
  /-- The per-band record coefficients. Data. -/
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  /-- The upper per-record bounds (`prop:record:upper`(ii), W8's ledger). *Open* (analytic). -/
  hR : C.toK1.UpperRecs hW A Cs Ca hCs hCa
  /-- The per-piece constants `(s_F, a_F, ℓ_t, s_E, a_E)`. Data. -/
  κ : Fin 33 → MiddleConsts
  /-- The constants are nonnegative (E2). Side condition on the data `κ`. -/
  hκ : ∀ i, KappaNonneg (κ i)
  /-- **The constants are at least the pricing constants `κ′ = paperKappa`** (RP): `toK1` prices
  the middle records at their bounds at `κ′`, so the norm sizes at `κ` need `κ′ ≤ κ`. Side
  condition on the data `κ` (`KappaLe.refl` at `κ = paperKappa`). -/
  hκP : ∀ i, KappaLe (paperKappa i) (κ i)
  /-- The twelve norm bounds of every middle block (B8's `NormBounds`). *Open* (analytic). -/
  hN : ∀ b i, blockSite b = .inl i →
    SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b)
  /-- **The final numerical inequality** of `hSA`, with the clique bound `12/2^{534}`, the band
  charges `bandBound a_T` and the tail bound `tailStTC + tailAtTC = 3/2¹⁵¹` entered. *Open*
  (numerical). -/
  hsum : 12 / 2 ^ 534 + ∑ β, ∑ d ∈ upperDegrees,
      ((upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
          bandBound targetDecay d β +
        (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefA d *
          bandBound targetDecay d β) +
    ∑ i : Fin 33, (midK2 κ i * f1c2 i +
      (midK3 κ i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) *
        f1c3 i) + (tailStTC + tailAtTC) ≤ targetLedger.S + targetLedger.A

/-- **K1's `hSA`** (`SAExplicit_fullF1` with the clique bound of C10, the band charges from
`thm:bmor`, the signs from `hκ` and the norm sizes by `specNormAt_of_bounds` with `hκP`; F1P's
`SAParts3.toK2` and K2's `SAParts.toSAExplicit` composed). -/
theorem SAPartsTC.toSAExplicit {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs f1Cell}
    {C : ComparisonPartsTC hW hMR hFour A} (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (S : SAPartsTC hW hMR hFour A C) : SAExplicit C.toK1.Ci :=
  C.toK1.SAExplicit_fullF1 hB hRR C.cliquePrice_le S.Cs S.Ca S.hCs S.hCa S.hR
    (fun β d => bandBound targetDecay d β) (fun β d => bandBound targetDecay d β)
    (fun β d _ => upperBand_le_bandBound hB hW A β d)
    (fun β d _ => upperBand_le_bandBound hB hW A β d) S.κ
    (fun b i hs => specNormAt_of_bounds hW (paperIn f1Cell) (blockKappa b) (S.κ i) (blockLeast b)
      (by rw [blockKappa_eq hs]; exact S.hκP i) (specF hW A b) (C.blk b) (S.hN b i hs))
    (midK_signs S.κ S.hκ)
    (by rw [C.St_At]; exact S.hsum)

/-! ## (CP6), (CP8)(c) -/

section Env

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- The middle part of `hothT` (`MainFinalF1.midOthers` at K1's `ComparisonParts`). -/
noncomputable def midOthersK1 (C : ComparisonParts hW hMR hFour A)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn f1Cell) (paperGi hW A)) C.CL (fun β => midAtom hW A β = true))
    (L : ℕ) : ℝ :=
  ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = false),
    ∑ t ∈ univ \ MR.toPrefix.repl L (.inl (.inr b)),
      (C.CL.π L (.inl (.inr b)) t .sym + C.CL.π L (.inl (.inr b)) t .skew)

/-- **`hothT` from its middle part** (`MainFinalF1.hothT_of_mid` at K1's `ComparisonParts`, with
the tail term `τ` a parameter; same proof). -/
theorem hothT_of_midK1 (hB : Target.BMOR) (C : ComparisonParts hW hMR hFour A)
    (hq : ∑ q, C.Ci.cliquePrice q ≤ 12 / 2 ^ 534)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn f1Cell) (paperGi hW A)) C.CL (fun β => midAtom hW A β = true))
    (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i) (hCa : ∀ k i, 0 ≤ Ca k i)
    (hR : C.UpperRecs hW A Cs Ca hCs hCa) {τ : ℝ}
    (hmid : ∀ L, midOthersK1 C MR L + max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup Cs Ca hCs hCa + τ) ≤ targetLedger.T) (L : ℕ) :
    (∑ β, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl β),
      (C.CL.π L (.inl β) t .sym + C.CL.π L (.inl β) t .skew)) +
        max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) + τ ≤ targetLedger.T := by
  have hfull : ∀ β : PaperAtom Blk, midAtom hW A β = false →
      ∑ t ∈ univ \ MR.toPrefix.repl L (.inl β),
        (C.CL.π L (.inl β) t .sym + C.CL.π L (.inl β) t .skew) =
      (C.Ci.pre β).sprice (paperSelAt (paperAtomMap bOf) targetDecay β) +
        (C.Ci.pre β).aprice (paperSelAt (paperAtomMap bOf) targetDecay β) := by
    intro β hβ
    rw [MidRefinement.toPrefix_repl_off MR L β (by rw [hβ]; decide), sdiff_empty,
      sum_add_distrib]
    exact pre_total C L β
  have hcl : ∑ q : PrefixCoord, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl (.inl q)),
      (C.CL.π L (.inl (.inl q)) t .sym + C.CL.π L (.inl (.inl q)) t .skew) =
      ∑ q, C.Ci.cliquePrice q :=
    sum_congr rfl fun q _ => (hfull (.inl q) rfl).trans (pre_price_clique C q)
  have hsplit : ∑ b : Blk, ∑ t ∈ univ \ MR.toPrefix.repl L (.inl (.inr b)),
      (C.CL.π L (.inl (.inr b)) t .sym + C.CL.π L (.inl (.inr b)) t .skew) =
      ∑ b ∈ univ.filter (fun b => specUpper (specF hW A b) = true), C.Ci.blockPrice b +
        midOthersK1 C MR L := by
    rw [← sum_filter_add_sum_filter_not univ (fun b => specUpper (specF hW A b) = true)]
    refine congrArg₂ (· + ·) (sum_congr rfl fun b hb => ?_) ?_
    · have hu := (mem_filter.mp hb).2
      refine (hfull (.inr b) ?_).trans (pre_price_block C b)
      simp only [midAtom, hu, Bool.not_true]
    · unfold midOthersK1
      refine sum_congr (filter_congr fun b _ => ?_) fun _ _ => rfl
      simp only [Bool.not_eq_true]
  have hup := upper_price_le hB C Cs Ca hCs hCa hR
  rw [Fintype.sum_sum_type, hcl, hsplit]
  have := hmid L
  generalize (12 : ℝ) / 2 ^ 534 = c at hq this
  linarith

/-- **K1's `EnvelopeParts` from the middle part** (F1P's `envOf`, E2's
`EnvelopePartsE2.toParts2` and K2's `EnvelopeParts2.toK1` composed): `T_K = max(∑ KL, ∑ KR)`,
`T_oth = T^{ledger} − T_K`, the tail atoms within `St + At = tailStTC + tailAtTC`
(`tail_price_le_St_At`), `σ_CL = σ_pre + (kSTC + kATC)/2¹²⁴` (`hCLpre_proved`,
`tail_hCL_le_TC`). -/
noncomputable def envTC (hB : Target.BMOR) (C : ComparisonPartsTC hW hMR hFour A)
    (MR : MidRefinement (gramBracketTarget bOf hW (specF hW A) (hCF hW hMR hFour)
      (paperIn f1Cell) (paperGi hW A)) C.toK1.CL (fun β => midAtom hW A β = true))
    (S : SAPartsTC hW hMR hFour A C)
    (hmid : ∀ L, midOthersK1 C.toK1 MR L + max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + (tailStTC + tailAtTC)) ≤ targetLedger.T) :
    EnvelopeParts hW hMR hFour A C.toK1 :=
  EnvelopeParts.ofOthers MR.toPrefix (max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β))
    ⟨le_max_left _ _, le_max_right _ _⟩
    (targetLedger.T - max (∑ β, MR.toPrefix.KL β) (∑ β, MR.toPrefix.KR β))
    (fun L => by
      have h1 := hothT_of_midK1 hB C.toK1 C.cliquePrice_le MR S.Cs S.Ca S.hCs S.hCa S.hR hmid L
      have h2 := tail_price_le_St_At C.toK1 L
      rw [C.St_At] at h2
      have h3 : ∑ j : PaperJt L, ∑ t ∈ univ \ MR.toPrefix.repl L (.inr j),
          (C.toK1.CL.π L (.inr j) t .sym + C.toK1.CL.π L (.inr j) t .skew) =
          ∑ j : PaperJt L, (symTotal (C.toK1.CL.π L) (.inr j) +
            skewTotal (C.toK1.CL.π L) (.inr j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        show ∑ t ∈ univ \ ∅, _ = _
        rw [sdiff_empty, Finset.sum_add_distrib]
        rfl
      rw [Fintype.sum_sum_type, h3]
      linarith)
    (le_of_eq (by ring))
    (σpreOf C.toK1 + (kSTC + kATC) / 2 ^ 124) fun L => by
      rw [Fintype.sum_sum_type]
      exact add_le_add (hCLpre_proved C.toK1 L) (tail_hCL_le_TC _ _ L)

end Env

/-! ## The block data -/

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}

/-- **The block data with the tail proved**: F1P's `FinalBlockData3b` with
`Cmp : ComparisonPartsTC` (no `Rp`, no `hcap`). 4 fields. -/
structure FinalBlockData3e (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    where
  /-- The per-prime cut certificates (C8, C9). -/
  PC : PrimeCertificates2
  /-- The block-level analytic inputs (B6). -/
  BA : BlockAnalytic
  /-- The (CP4) inputs: per upper block B2's inputs; the tail proved (TC). -/
  Cmp : ComparisonPartsTC hW hMR hFour (analyticInputs (PC.toPC hW hMR hFour) BA)
  /-- The prefix refinement on the middle blocks (`prop:record:matching`(i), `prop:signed-sides`;
  K2's `MR`). *Open*. -/
  MR : MidRefinement
    (gramBracketTarget bOf hW (specF hW (analyticInputs (PC.toPC hW hMR hFour) BA))
      (hCF hW hMR hFour) (paperIn f1Cell)
      (paperGi hW (analyticInputs (PC.toPC hW hMR hFour) BA)))
    Cmp.toK1.CL (fun β => midAtom hW (analyticInputs (PC.toPC hW hMR hFour) BA) β = true)

/-- **K1's block data** (`FinalBlockData3b.toMF3`, `FinalBlockData3.toK2`, `FinalBlockData2.toK1`
composed, at `ComparisonPartsTC`). -/
noncomputable def FinalBlockData3e.toK1 (hB : Target.BMOR) (D : FinalBlockData3e hW hMR hFour)
    (S : SAPartsTC hW hMR hFour (analyticInputs (D.PC.toPC hW hMR hFour) D.BA) D.Cmp)
    (hmid : ∀ L, midOthersK1 D.Cmp.toK1 D.MR L +
      max (∑ β, D.MR.toPrefix.KL β) (∑ β, D.MR.toPrefix.KR β) +
      (12 / 2 ^ 534 + Uup S.Cs S.Ca S.hCs S.hCa + (tailStTC + tailAtTC)) ≤ targetLedger.T) :
    FinalBlockData hW hMR hFour where
  PC := D.PC.toPC hW hMR hFour
  BA := D.BA
  Cmp := D.Cmp.toK1
  Env := envTC hB D.Cmp D.MR S hmid

/-! ## The obligations and the main statement -/

/-- **The combined obligations at `f1Cell` with the tail repairs proved**: F1b's
`MainFinalObligations3d` with `Dv.Cmp : ComparisonPartsTC` (no `Rp`, no `hcap`), and the tail
bound `tailStTC + tailAtTC` in `SA.hsum` and `hmid` in place of `11/10⁷⁰`. 5 fields. -/
structure MainFinalObligations3e (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) where
  /-- The block data (at `f1Cell`, the tail proved). -/
  Dv : FinalBlockData3e hW hMR hFour
  /-- `hSA` in reduced form (final inequality at N2's numbers and TC's tail bound). -/
  SA : SAPartsTC hW hMR hFour (analyticInputs (Dv.PC.toPC hW hMR hFour) Dv.BA) Dv.Cmp
  /-- The middle part of `hothT`, with TC's tail bound. *Open*. -/
  hmid : ∀ L, midOthersK1 Dv.Cmp.toK1 Dv.MR L +
    max (∑ β, Dv.MR.toPrefix.KL β) (∑ β, Dv.MR.toPrefix.KR β) +
    (12 / 2 ^ 534 + Uup SA.Cs SA.Ca SA.hCs SA.hCa + (tailStTC + tailAtTC)) ≤ targetLedger.T
  /-- The class inputs (`ClassPartsE4B`, as in `final3d`). -/
  Cls : ClassPartsE4B (Dv.toK1 hB SA hmid).data
  /-- The inputs of `SF`, `fix`, `env` (B5, B9). -/
  Sh : SharpParts2 (Dv.toK1 hB SA hmid).toJoint

/-- K1's layer with both FA2 corrections (F1b's `MainFinalObligationsJB`). -/
noncomputable def MainFinalObligations3e.toJB {hB : Target.BMOR} (hRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3e hW hMR hFour hB) : MainFinalObligationsJB hW hMR hFour where
  Dv := O.Dv.toK1 hB O.SA O.hmid
  hSA := O.SA.toSAExplicit hB hRR
  Cls := O.Cls
  Sh := O.Sh

/-- **The main statement at `ε = a_T/71 ≈ 1.19975·10⁻⁵` at the F1 partition, with the tail repairs
proved** (`thm:main` at `ε = a_T/71`; F1b's `main_target_f1_final3d` without `Cmp.Rp`,
`Cmp.hcap`: `lem:tail-prices`, (F7) and (F2) at every tail prime from H1, TC). Hypotheses as
`MainFinalF1b.main_target_f1_final3d`, with `O : MainFinalObligations3e`. -/
theorem main_target_f1_final3e (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3e hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_f1_finalJB hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    (O.toJB hThetaSmallRR)

/-- **`main_target_f1_final3e` at the owner's goal exponent** `N^{0.99999}`
(`TargetGoal.epsGoal = 10⁻⁵ ≤ epsTarget`, `Target.sarkozyBound_mono`). -/
theorem main_goal_f1c (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (O : MainFinalObligations3e hWeil hMovingRoot hFourCycle hBMOR) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  Target.sarkozyBound_mono TargetGoal.epsGoal_le_targetSaving
    (main_target_f1_final3e hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR O)

end Sarkozy.MainFinalF1c
