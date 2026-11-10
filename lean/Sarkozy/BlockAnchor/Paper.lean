module

public import Sarkozy.BlockAnchor.Prices
public import Sarkozy.TheoremCBlock.Ledger
public import Sarkozy.TheoremCBlock.DensityTransfer
public import Sarkozy.MainAnchor.Paper
public import Sarkozy.LedgerAnchor.Sanity

@[expose] public section





open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.BlockAnchor

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (anchorLedger)
open Sarkozy.CancellationSteps Sarkozy.PaperFrame Sarkozy.FourierArithmetic Sarkozy.Functional
  Sarkozy.IndexSupport Sarkozy.BlockFrame Sarkozy.MainAnchor

/-- The prime powers of the index coordinates are pairwise coprime ((CP0)(d)), for comparison data
on the block atoms (`MainAnchor.index_coprime`). -/
theorem index_coprime_block {a : ℝ}
    {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
    {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
    [∀ L j, NeZero (p L j)]
    {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
    {E : Type} [Fintype E] [DecidableEq E]
    (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) :
    Pairwise (Nat.Coprime on fun q => pr q ^ h q) := by
  intro q q' hqq'
  have hne : pr q ≠ pr q' := fun e => hqq' (D.S.pr_inj e)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (D.S.pr_prime q) (D.S.pr_prime q')).mpr hne)

variable {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : PaperJ0 → Bk)

/-! ## The standing data and the reference of the paper on the block atoms -/

/-- **The paper's standing data on the block atoms** (`def:cp0`): as D1's `paperStanding`, with
the selection factors of the prefix blocks fixed to the paper's `def:price` values `paperSel blk`
(no free parameter). -/
noncomputable def blockPaperStanding (index : IndexLaw paperPr paperH Chamber) :
    TheoremCBlock.StandingData (Bk := Bk) paperM0 paperTail paperPr paperH Chamber where
  pp := paperPP
  ep := paperEP
  pp_prime := paperJ0_prime
  ep_pos := one_le_paperEP
  m₀_eq _ := rfl
  p_prime _ j := paperTail_prime j
  p_inj _ := Subtype.val_injective
  selPre := paperSel blk
  one_le_selPre := one_le_paperSel blk
  Q := paperQueries
  index := index
  pr_prime := paperPr_prime
  pr_inj := Subtype.val_injective
  h_two := (paper_standing_fields).2.2.2.2.2.1
  modulus_coprime := paper_hcop0

/-- **The paper's reference on the block atoms** (`def:cp1`): the block laws `μ₀ β` with (R2), (R3)
and uniform marginals (open, Part V), and V2's tail laws `tailFamilyFrom P₄` with `rpp` (given the
tail inputs), `invp`, `unifp`, `P₅ = 2^{65536}` and V3's mixing (R4), as in D1's
`paperReference`. -/
noncomputable def blockPaperReference (hW : Target.Weil)
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes paperM0 blk β))
    (rp₀ : ∀ β, FamilyReflectionPositive (signedIntegral (μ₀ β).weight))
    (inv₀ : ∀ β (a : ∀ i, (ZMod (blockModuli paperM0 blk β i))ˣ) (b : BlockRes paperM0 blk β),
      (∀ i, IsSquare ((a i : ZMod (blockModuli paperM0 blk β i)))) →
        ∀ F : (Slot → BlockRes paperM0 blk β) → ℝ,
          (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli paperM0 blk β) a b
              (z v))) =
            (μ₀ β).expect F)
    (unif₀ : ∀ β, HasUniformMarginals (μ₀ β)) (hV : PartVLaws.TailInputsValid PartV.P4) :
    TheoremCBlock.Reference paperM0 blk where
  μ₀ := μ₀
  μp q _ := PartVLaws.tailFamilyFrom PartV.P4 q
  rp₀ := rp₀
  rpp q _ hq := PartVLaws.tailFamilyFrom_rpp hW le_rfl hV q hq
  inv₀ := inv₀
  invp q _ a b ha F := PartVLaws.tailFamilyFrom_invp PartV.P4 q a b ha F
  unif₀ := unif₀
  unifp q _ hq := PartVLaws.tailFamilyFrom_unifp PartV.P4 q hq
  P5 := PartV.P5
  mixing := PartVLaws.tailFamilyFrom_mixing CancellationSteps.P4_le_P5
    (PartVRecords.tailLawFamily_mixing hW)

/-! ## The open parts of the data -/

/-- **The open parts of the comparison data for the paper's construction on its prefix atoms**
(`def:cp0`–`def:cp8`, `def:construction`). D1's `MainAnchor.PaperData` without `selPre` and
`one_le_selPre`, with the prefix law given by its block laws. All *open* (Part V):
* `hIdx`: the transition bound of the index law (`lem:imp:padic-envelope`, analytic);
* `μ₀`, `rp₀`, `inv₀`, `unif₀`: the block laws of the prefix (the square-clique laws of the atoms
  `{p}`, the middle and upper block laws, `def:construction`(b)) with (R2) at the cuts of `𝔉`,
  (R3) and uniform marginals. V1 and V2 prove these for each block law given the spectral inputs
  (`PartV.middleBlockReference_*`, `PartVLaws.upperBlock_R1R3`, `Construction/`);
* `hV`: `lem:tail-law`(i), the validity of the tail inputs (spectral);
* `FS`, `GB`, `CL`, `ME`, `MC`, `SM`: (CP2)–(CP4), (CP6)–(CP8) at `a₀` on the block atoms, priced by
  `paperSel blk`. -/
structure BlockPaperData (hW : Target.Weil) where
  hIdx : Sarkozy.PaperData.PaperIndexBound
  μ₀ : ∀ β, FiniteLaw (Slot → BlockRes paperM0 blk β)
  rp₀ : ∀ β, FamilyReflectionPositive (signedIntegral (μ₀ β).weight)
  inv₀ : ∀ β (a : ∀ i, (ZMod (blockModuli paperM0 blk β i))ˣ) (b : BlockRes paperM0 blk β),
    (∀ i, IsSquare ((a i : ZMod (blockModuli paperM0 blk β i)))) →
      ∀ F : (Slot → BlockRes paperM0 blk β) → ℝ,
        (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli paperM0 blk β) a b (z v))) =
          (μ₀ β).expect F
  unif₀ : ∀ β, HasUniformMarginals (μ₀ β)
  hV : PartVLaws.TailInputsValid PartV.P4
  FS : TheoremCBlock.FirstStage Params.anchorDecay paperM0 blk paperTail (paperSel blk)
    (blockPaperReference blk hW μ₀ rp₀ inv₀ unif₀ hV)
  GB : TheoremCBlock.GramBracket Params.anchorDecay paperM0 blk paperTail (paperSel blk) FS
  CL : TheoremCBlock.ComparisonLaw Params.anchorDecay paperM0 blk paperTail (paperSel blk) paperPP
    paperEP paperQueries FS
  ME : TheoremCBlock.MatchingEnvelopes Params.anchorDecay paperM0 blk paperTail GB CL
  MC : TheoremCBlock.MeanCredit Params.anchorDecay paperM0 blk paperTail ME
  SM : TheoremCBlock.Summability Params.anchorDecay paperM0 blk paperTail ME

variable {blk}

/-- The comparison data at `a₀` on the block atoms, assembled from the open parts. -/
noncomputable def BlockPaperData.toData {hW : Target.Weil} (Dp : BlockPaperData blk hW) :
    TheoremCBlock.ComparisonData Params.anchorDecay paperM0 blk paperTail paperPr paperH
      Chamber where
  S := blockPaperStanding blk
    (Sarkozy.PaperData.paperIndexLaw (Sarkozy.PaperData.paperIndexEnvelope Dp.hIdx))
  R := blockPaperReference blk hW Dp.μ₀ Dp.rp₀ Dp.inv₀ Dp.unif₀ Dp.hV
  FS := Dp.FS
  GB := Dp.GB
  CL := Dp.CL
  ME := Dp.ME
  MC := Dp.MC
  SM := Dp.SM

/-- The selection factor of the block `β` in the assembled data is the paper's `q_β^{2a₀}`. -/
theorem BlockPaperData.selPre_eq {hW : Target.Weil} (Dp : BlockPaperData blk hW) (β : Bk) :
    Dp.toData.S.selPre β = paperSel blk β := rfl

/-- **`lem:record:density-can` for the assembled data**: D1's `densityCancellation_paper`,
transferred to the block atoms (`TheoremCBlock.densityCancellation_paper_block`). -/
theorem BlockPaperData.densityCancellation {hW : Target.Weil} (Dp : BlockPaperData blk hW) :
    TheoremCBlock.DensityCancellation paperM0 blk paperTail paperPr paperH Dp.toData.R.P5
      Dp.toData.S.pp Dp.toData.S.ep :=
  TheoremCBlock.densityCancellation_paper_block blk

/-- **`hunit` for the assembled data**: the tail laws are V1's at the primes `≥ P₄`, which have unit
mixed `L³⁶` above a threshold (D1's `TailUnit.tailLawFamily_unit`), as in `MainAnchor`. -/
theorem BlockPaperData.hunit {hW : Target.Weil} (Dp : BlockPaperData blk hW) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q →
      MixedLpBound (Dp.toData.R.μp q) 36 1 := by
  obtain ⟨p₀, hp₀⟩ := TailUnit.tailLawFamily_unit hW
  refine ⟨max p₀ PartV.P4, fun q _ hq hle => ?_⟩
  show MixedLpBound (PartVLaws.tailFamilyFrom PartV.P4 q) 36 1
  rw [PartVLaws.tailFamilyFrom_eq PartV.P4 q hq (le_of_max_le_right hle)]
  exact hp₀ q hq (le_of_max_le_left hle)

/-! ## The remaining obligations -/

variable (blk) in
/-- **Everything that remains between the tree and the target at `a₀`, for the paper's data on its
prefix atoms.** D1's `PaperObligations` with the comparison data on the block atoms and the paper's
block prices: the open data `Dp` and 13 others. Labels and statuses are D1's (P1's); the ledger is
`anchorLedger`. -/
structure BlockPaperObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dp : BlockPaperData blk hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a₀`. *Open* (Part V). -/
  CB : TheoremCBlock.ClassBounds Params.anchorDecay paperM0 blk paperTail Dp.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dp.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dp.toData.B * monomial (Dp.toData.CL.π L) ω else CB.phi L ω) ≤
      anchorLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dp.toData.B ≤ anchorLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)), with the first-stage prices at the paper's block factors.
  *Open* (Part V). -/
  hL₀ : Dp.toData.L₀ ≤ anchorLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dp.toData.ME.T ≤ anchorLedger.T
  /-- **`M_pad(K) ≤` the ledger's `R_I`** (`cert:index-moment`, family F2). *Open* (numeric). -/
  hR : Sarkozy.PaperData.paperRI ≤ anchorLedger.R_I
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ anchorLedger.S + anchorLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
    anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
    anchorLedger.upperError) ≤ Dp.toData.MC.m
  /-- **(E1), the envelope bound with nonnegative remainders** (`lem:bracket-energy` at `ϑ`, via
  `prop:density:production`). *Open at `a₀`*. The selection factor of a selection is now the
  product of the factors of the selected blocks and tail primes only. -/
  hE1 : Dp.toData.EnvelopeBoundNonneg
  /-- **The sharp first-stage terms** (`lem:sharp-first`, `lem:record:folded-energy`). *Open at
  `a₀`*. -/
  hSF : Dp.toData.SharpFirstTerms
  /-- **The fixed-interval envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  hfix : Dp.toData.FixedIntervalEnvelopeEnergies (index_coprime_block Dp.toData)
  /-- **The envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  henv : Dp.toData.EnvelopeEnergies (index_coprime_block Dp.toData)

/-- **The target at `a₀` for the paper's data on its prefix atoms** (`thm:main` at the formal
exponent, via `thm:comparison` and `thm:density:induction`), from the literature inputs and the
remaining obligations, for any block assignment `blk` of the fixed primes. `Target.Weil` is used
for `hunit`, the (R4) mixing and `rpp`; `lem:record:density-can` is D1's, transferred. -/
theorem main_anchor_paper_block (hWeil : Target.Weil)
    (_hMovingRoot : Target.MovingRoot) (_hFourCycle : Target.FourCycle)
    (O : BlockPaperObligations blk hWeil) : Target.SarkozyBound Param.anchorSaving :=
  TheoremCBlock.Ledger.ComparisonData.theoremC_classes_reduced_anchor_of_ledger O.Dp.toData
    (index_coprime_block O.Dp.toData) LedgerAnchor.anchorLedger_bounds card_chamber
    O.Dp.toData.B_nonneg O.hB O.hL₀ O.hT O.Dp.toData.S.index.hR_I O.hR O.hSA O.hm O.CB le_rfl
    O.hΨ O.hE1 O.hCB O.hSF O.Dp.densityCancellation O.hfix O.henv O.Dp.hunit

end Sarkozy.BlockAnchor
