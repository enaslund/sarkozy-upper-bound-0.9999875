module

public import Sarkozy.MainAnchor.Main
public import Sarkozy.MainAnchor.PaperQueries
public import Sarkozy.PaperData.IndexLaw
public import Sarkozy.CancellationSteps.All
public import Sarkozy.TailUnit.All
public import Sarkozy.PartVLaws.ReferenceFields
public import Sarkozy.PartVRecords.TailMixing

@[expose] public section

/-!
# The assembly at `a₀` for the paper's data

`main_anchor_paper` concludes `Target.SarkozyBound Param.anchorSaving` from the literature inputs
and one structure, `PaperObligations`. It is P1's `main_anchor` (`Main.lean`) specialized to the
paper's construction (`def:construction`, `def:record:parameters`, `def:record:functional`). Every
field that the tree now proves for those data is removed.

**The data.**
* The coordinates and moduli are D1's `CancellationSteps.paperM0`, `paperTail`, `paperPr` and
  `paperH`, built from V1's `PartV.Parameters`: `𝒫₁ ∪ 𝒫₃` with `e_p = 2𝔪` on `𝒫₁`, the tail
  `P₄ ≤ p ≤ N^{1/20}`, and `M₀`.
* The queries are the paper's six queries `𝓔₆` (`paperQueries`, `PaperQueries.lean`), indexed by
  `j ∈ ℤ/6ℤ`.
* The standing data (`def:cp0`) are `paperStanding`. Their eleven structural fields (prime
  powers, distinct primes, `h₂ = 129`, the coprimality of `M₀`) are proved.
* The reference (`def:cp1`) is V2's `PartVLaws.tailReference`, with the following tail fields:
  - `μp := tailFamilyFrom P₄`, with `invp` and `unifp` (V2);
  - `rpp` from Weil and the tail inputs `TailInputsValid P₄` (V2);
  - `mixing` (R4) from V3's `PartVRecords.tailLawFamily_mixing`;
  - `P₅ = 2^{65536}`.
* The ledger is `LedgerAnchor.anchorLedger`, whose `AnchorBounds` are proved.

**Removed from P1's 32 fields, as proved.**
* The twelve inputs of `lem:record:density-can`: `h64`, `C₂`, `hC₂`, `Mfib`, `hMfib`, `Cε`, `hCε`,
  `Lstep`, `hppinj`, `hne`, `hcover` and `hSteps`. D1's
  `CancellationSteps.densityCancellation_paper` gives `DensityCancellation` for the paper's data
  with no hypothesis.
* `hunit`, from D1's `TailUnit.tailLawFamily_unit` (`Target.Weil`).
* `hcard`, since there are six queries by construction (`card_chamber`).
* `l` and `hl`: the ledger is `anchorLedger` (`LedgerAnchor.anchorLedger_bounds`).
* `𝓔` and `h𝓔`: the energy constant is `anchorLedger.E`.
* Inside `D`, these subfields are proved or fixed:
  - the eleven structural fields of the standing data, and its queries `Q := paperQueries`;
  - the index law (`Sarkozy.PaperData.paperIndexLaw`): the increments (V1's square
    increments, with their nonvanishing square property proved), the paper's depth tails and
    the moment `R_I = M_pad(K)` (V2-A's `Mpad`). Only the transition bound
    `lem:imp:padic-envelope` remains (`Dp.hIdx`), and the numeric value of `R_I` is
    `cert:index-moment` (`hR`);
  - `μp`, `invp`, `unifp`, `P5` and `mixing` of the reference;
  - `rpp`, which is reduced to `TailInputsValid P₄` (`lem:tail-law`(i)).

**What remains** is `PaperObligations`: 14 fields, namely the open parts of the data (`Dp`, a
`PaperData` with 14 fields, down from 31 in `D`) and 13 others. Each keeps P1's label and
status.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.MainAnchor

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.Comparison (PrimitiveLedger)
open Sarkozy.Param (Params)
open Sarkozy.LedgerAnchor (AnchorBounds anchorLedger)
open Sarkozy.CancellationSteps Sarkozy.PaperFrame Sarkozy.FourierArithmetic Sarkozy.Functional
  Sarkozy.IndexSupport

/-! ## The standing data and the reference of the paper -/

/-- **The paper's standing data** (`def:cp0`) from its open parts: the selection factor of the
prefix atom and the index law. The queries are the paper's `𝓔₆` (`paperQueries`); the other
fields are proved for D1's data (`CancellationSteps.paper_standing_fields`). -/
noncomputable def paperStanding (selPre : ℝ) (one_le_selPre : 1 ≤ selPre)
    (index : IndexLaw paperPr paperH Chamber) :
    StandingData paperM0 paperTail paperPr paperH Chamber where
  pp := paperPP
  ep := paperEP
  pp_prime := paperJ0_prime
  ep_pos := one_le_paperEP
  m₀_eq _ := rfl
  p_prime _ j := paperTail_prime j
  p_inj _ := Subtype.val_injective
  selPre := selPre
  one_le_selPre := one_le_selPre
  Q := paperQueries
  index := index
  pr_prime := paperPr_prime
  pr_inj := Subtype.val_injective
  h_two := (paper_standing_fields).2.2.2.2.2.1
  modulus_coprime := paper_hcop0

/-- **The paper's reference** (`def:cp1`): V2's `tailReference`. Its fields are the prefix law `μ₀`
with (R1)–(R3), which are open; `μp := tailFamilyFrom P₄` with `rpp`, `invp` and `unifp`
(`rpp` given the tail inputs); `P₅ = 2^{65536}`; and `mixing`, from V3's `tailLawFamily_mixing`. -/
noncomputable def paperReference (hW : Target.Weil)
    (μ₀ : FiniteLaw (Slot → ResidueSpace paperM0))
    (rp₀ : FamilyReflectionPositive (signedIntegral μ₀.weight))
    (inv₀ : ∀ (a : ∀ i, (ZMod (paperM0 i))ˣ) (b : ResidueSpace paperM0),
      (∀ i, IsSquare ((a i : ZMod (paperM0 i)))) → ∀ F : (Slot → ResidueSpace paperM0) → ℝ,
        μ₀.expect (fun z => F (fun v => piAffineEquiv paperM0 a b (z v))) = μ₀.expect F)
    (unif₀ : HasUniformMarginals μ₀) (hV : PartVLaws.TailInputsValid PartV.P4) :
    Reference paperM0 :=
  PartVLaws.tailReference paperM0 μ₀ rp₀ inv₀ unif₀ hW hV PartV.P5 CancellationSteps.P4_le_P5
    (PartVRecords.tailLawFamily_mixing hW)

/-! ## The open parts of the data -/

/-- **The open parts of the comparison data `D` for the paper's construction** (P1's field `D`,
`def:cp0`–`def:cp8`, `def:construction`). All *open* (Part V), with P1's statuses:
* `selPre`, `one_le_selPre`: the selection factor of the merged prefix atom (`def:price`,
  `def:cp0`). It is kept: the paper's `def:price` value for the merged atom, the product of the
  factors of all its atoms, would make the first-stage price total at the merged atom
  astronomically large (WP-FI's note on the merged prefix atom; I1's "Gap 2");
* `hIdx`: the transition bound of the index law by the paper's depth tails
  (`lem:imp:padic-envelope`, analytic; `Sarkozy.PaperData.PaperIndexBound`). The rest of the
  index law and the queries are fixed (`paperIndexLaw`, `paperQueries`);
* `μ₀`, `rp₀`, `inv₀`, `unif₀`: the prefix reference law (the clique and block laws carried to
  `ResidueSpace M`) with (R2), (R3) and uniform marginals. V2's `PartVLaws.prefixAssembly`
  builds these from atom laws with (R1)–(R3), once the block partitions are entered;
* `hV`: `lem:tail-law`(i), the validity of the tail inputs at every tail prime (spectral). It
  gives `rpp`;
* `FS`, `GB`, `CL`, `ME`, `MC`, `SM`: (CP2)–(CP4), (CP6)–(CP8) at `a₀`. -/
structure PaperData (hW : Target.Weil) where
  selPre : ℝ
  one_le_selPre : 1 ≤ selPre
  hIdx : Sarkozy.PaperData.PaperIndexBound
  μ₀ : FiniteLaw (Slot → ResidueSpace paperM0)
  rp₀ : FamilyReflectionPositive (signedIntegral μ₀.weight)
  inv₀ : ∀ (a : ∀ i, (ZMod (paperM0 i))ˣ) (b : ResidueSpace paperM0),
    (∀ i, IsSquare ((a i : ZMod (paperM0 i)))) → ∀ F : (Slot → ResidueSpace paperM0) → ℝ,
      μ₀.expect (fun z => F (fun v => piAffineEquiv paperM0 a b (z v))) = μ₀.expect F
  unif₀ : HasUniformMarginals μ₀
  hV : PartVLaws.TailInputsValid PartV.P4
  FS : TheoremCParam.FirstStage Params.anchorDecay paperM0 paperTail selPre
    (paperReference hW μ₀ rp₀ inv₀ unif₀ hV)
  GB : TheoremCParam.GramBracket Params.anchorDecay paperM0 paperTail selPre FS
  CL : TheoremCParam.ComparisonLaw Params.anchorDecay paperM0 paperTail selPre paperPP paperEP
    paperQueries FS
  ME : TheoremCParam.MatchingEnvelopes Params.anchorDecay paperM0 paperTail GB CL
  MC : TheoremCParam.MeanCredit Params.anchorDecay paperM0 paperTail ME
  SM : TheoremCParam.Summability Params.anchorDecay paperM0 paperTail ME

/-- The comparison data at `a₀` assembled from the open parts. -/
noncomputable def PaperData.toData {hW : Target.Weil} (Dp : PaperData hW) :
    TheoremCParam.ComparisonData Params.anchorDecay paperM0 paperTail paperPr paperH Chamber where
  S := paperStanding Dp.selPre Dp.one_le_selPre
    (Sarkozy.PaperData.paperIndexLaw (Sarkozy.PaperData.paperIndexEnvelope Dp.hIdx))
  R := paperReference hW Dp.μ₀ Dp.rp₀ Dp.inv₀ Dp.unif₀ Dp.hV
  FS := Dp.FS
  GB := Dp.GB
  CL := Dp.CL
  ME := Dp.ME
  MC := Dp.MC
  SM := Dp.SM

/-- **`lem:record:density-can` for the assembled data** (D1's `densityCancellation_paper`). -/
theorem PaperData.densityCancellation {hW : Target.Weil} (Dp : PaperData hW) :
    DensityCancellation paperM0 paperTail paperPr paperH Dp.toData.R.P5 Dp.toData.S.pp
      Dp.toData.S.ep :=
  densityCancellation_paper

/-- **`hunit` for the assembled data**: the reference's tail laws are V1's at the primes `≥ P₄`
(`PartVLaws.tailFamilyFrom_eq`), and those have unit mixed `L³⁶` above a threshold
(`TailUnit.tailLawFamily_unit`). -/
theorem PaperData.hunit {hW : Target.Weil} (Dp : PaperData hW) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q →
      MixedLpBound (Dp.toData.R.μp q) 36 1 := by
  obtain ⟨p₀, hp₀⟩ := TailUnit.tailLawFamily_unit hW
  refine ⟨max p₀ PartV.P4, fun q _ hq hle => ?_⟩
  show MixedLpBound (PartVLaws.tailFamilyFrom PartV.P4 q) 36 1
  rw [PartVLaws.tailFamilyFrom_eq PartV.P4 q hq (le_of_max_le_right hle)]
  exact hp₀ q hq (le_of_max_le_left hle)

/-! ## The remaining obligations -/

/-- **Everything that remains between the tree and the target at `a₀`, for the paper's data.**
P1's `PartVObligations` (32 fields) with the fields now proved removed: 14 fields remain, the open
data `Dp` and 13 others. Labels and statuses are P1's; the ledger is `anchorLedger`. -/
structure PaperObligations (hW : Target.Weil) where
  /-- **The open parts of the comparison data** (`def:cp0`–`def:cp8`). *Open* (Part V). -/
  Dp : PaperData hW
  /-- **The (CP5) class bounds** (`def:cp5`) of the comparison law at `a₀`. *Open* (Part V). -/
  CB : TheoremCParam.ClassBounds Params.anchorDecay paperM0 paperTail Dp.toData.CL
  /-- **The complete polynomial with class bounds is at most the ledger's `E`** at every scale
  (`def:cp5`, `thm:comparison`). *Open* (Part V, certificate family F15). -/
  hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (Dp.toData.CL.T L) => IsSelection ω),
    (if CB.cls L ω = none then Dp.toData.B * monomial (Dp.toData.CL.π L) ω else CB.phi L ω) ≤
      anchorLedger.E
  /-- The class bounds are robust with nonnegative remainders (`def:robust`, (CP5)). *Open*. -/
  hCB : CB.RobustNonneg
  /-- `B ≤` the ledger's `B` ((CP3), `def:closing-quantities`). *Open* (Part V). -/
  hB : Dp.toData.B ≤ anchorLedger.B
  /-- `L₀ ≤` the ledger's `L₀` ((CP2)). *Open* (Part V). -/
  hL₀ : Dp.toData.L₀ ≤ anchorLedger.L₀
  /-- `T ≤` the ledger's `T` ((CP6)). *Open* (Part V). -/
  hT : Dp.toData.ME.T ≤ anchorLedger.T
  /-- **`M_pad(K) ≤` the ledger's `R_I`** (`cert:index-moment`, family F2): the paper's conductor
  moment (`Sarkozy.PaperData.paperRI`, which is `Dp.toData.S.index.R_I`) is at most the ledger's
  value. *Open* (a numeric certificate: small primes plus Abel summation under H2′/H2″). -/
  hR : Sarkozy.PaperData.paperRI ≤ anchorLedger.R_I
  /-- `S + A ≤` the ledger's `S + A` ((CP4)). *Open* (Part V). -/
  hSA : Dp.toData.CL.S + Dp.toData.CL.A ≤ anchorLedger.S + anchorLedger.A
  /-- **The mean credit pays the joint-closing allocations** (`cor:joint-closing`,
  `prop:joint-middle-mean`, `prop:joint-upper-mean`). *Open* (Part V). -/
  hm : anchorLedger.m₁ + 64 * ((anchorLedger.deltaAlpha + anchorLedger.deltaMatching +
    anchorLedger.deltaOdd + anchorLedger.deltaEven) + anchorLedger.deltaUpper -
    anchorLedger.upperError) ≤ Dp.toData.MC.m
  /-- **(E1), the envelope bound with nonnegative remainders** (`lem:bracket-energy` at `ϑ`, via
  `prop:density:production`). *Open at `a₀`* (P1's docstring of `PartVObligations.hE1`). -/
  hE1 : Dp.toData.EnvelopeBoundNonneg
  /-- **The sharp first-stage terms** (`lem:sharp-first`, `lem:record:folded-energy`). *Open at
  `a₀`*. -/
  hSF : Dp.toData.SharpFirstTerms
  /-- **The fixed-interval envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  hfix : Dp.toData.FixedIntervalEnvelopeEnergies (index_coprime Dp.toData)
  /-- **The envelope energies** (`lem:envelope-energy`). *Open at `a₀`*. -/
  henv : Dp.toData.EnvelopeEnergies (index_coprime Dp.toData)

/-- **The target at `a₀` for the paper's data**, from the literature inputs and the remaining
obligations. `Target.Weil` is used for `hunit`, for the (R4) mixing and for `rpp`. -/
theorem main_anchor_paper (hWeil : Target.Weil)
    (_hMovingRoot : Target.MovingRoot) (_hFourCycle : Target.FourCycle)
    (O : PaperObligations hWeil) : Target.SarkozyBound Param.anchorSaving :=
  LedgerAnchor.ComparisonData.theoremC_classes_reduced_anchor_of_ledger O.Dp.toData
    (index_coprime O.Dp.toData) LedgerAnchor.anchorLedger_bounds card_chamber
    O.Dp.toData.B_nonneg O.hB O.hL₀ O.hT O.Dp.toData.S.index.hR_I O.hR O.hSA O.hm O.CB le_rfl
    O.hΨ O.hE1 O.hCB O.hSF O.Dp.densityCancellation O.hfix O.henv O.Dp.hunit

end Sarkozy.MainAnchor
