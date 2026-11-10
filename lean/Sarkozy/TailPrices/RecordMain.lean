module

public import Sarkozy.TailPrices.Main
public import Sarkozy.TailPrices.Assembly
public import Sarkozy.TailPrices.Deletions

@[expose] public section

/-!
# K1's tail fields from the changed records (`lem:tail-prices`)

`paper/sections/27_tail_index.tex`, `lem:tail-prices`. The strongest constructor of the tail
fields of K1's `MainFinal.ComparisonParts`:

* `paperTailRef_eq`: at a tail prime `q ≥ P₄`, the reference `μ_q` of K1's construction is V2's tail
  law `tailLaw q hne` (`def:tail-law`);
* `TailAtomData.congrMu`: transport of the tail atom along an equality of references;
* **`TailPriceInputs.ofRecords`**: `TailPriceInputs` at the paper's reference from
  `TailRecordInputs` (the changed records: replacing laws with acceptance and invariance, prices
  and brackets) and `TailRecordPrices` (`lem:tail-prices`(ii) per record) at every tail prime;
* **`ofTailRecords`**: K1's `ComparisonParts` from `clique`, `blk`, and these two per-prime
  families; `St`, `At`, `tail_S`, `tail_A` and all the per-atom structure of `tail` (the accepted
  part, the change identity, the envelopes, the deletions and their brackets) are constructed;
* **`ofTailRepairs`**: the same with `TailRecordPrices` replaced by the two bounds on the changed
  records (the deleted part is `deleted_le_piDel`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper
  Sarkozy.FirstStagePaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (v2Reference PrefixCoord)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted tailNe)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.MainFinal (bOf specF hCF Blk ComparisonParts)

/-- Transport of the tail atom data along an equality of references. -/
noncomputable def TailAtomData.congrMu {q : ℕ} [Fact q.Prime] {hne : TailNonempty q}
    {μ μ' : SlotMeasure (ZMod q)} (D : TailAtomData q hne μ) (h : μ = μ') :
    TailAtomData q hne μ' where
  rest := D.rest
  w := D.w
  w_pos := D.w_pos
  T := D.T
  Δ := D.Δ
  change := by rw [← h]; exact D.change
  D := D.D
  D_prob := D.D_prob
  D_diag := D.D_diag
  D_unif := D.D_unif
  πt := D.πt
  πt_nonneg := D.πt_nonneg
  bracket := D.bracket

/-- **The reference of K1's construction at a tail prime is the tail law** (`def:tail-law`):
`μ_q = tailLaw q hne` for `q ≥ P₄` (V2's `tailFamilyFrom P₄`). -/
theorem paperTailRef_eq {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs PaperNumbers.paperCell} (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q)
    (hne : TailNonempty q) :
    paperTailRef hW hMR hFour A q = signedIntegral (tailLaw q hne).weight := by
  have h : (v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μp q = tailLaw q hne := by
    change PartVLaws.tailFamilyFrom PartV.P4 q = _
    unfold PartVLaws.tailFamilyFrom
    rw [dite_eq_left (⟨Fact.out, h4⟩ : q.Prime ∧ PartV.P4 ≤ q), dite_eq_left hne]
  change signedIntegral ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μp q).weight = _
  rw [h]

/-- **`TailPriceInputs` at the paper's reference from the changed records** (`lem:tail-prices`(i),
(ii)): per tail prime, `TailRecordInputs` and `TailRecordPrices`. -/
noncomputable def TailPriceInputs.ofRecords {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (R : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordInputs q (tailNe hW h4))
    (H : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordPrices (R q h4)) :
    TailPriceInputs hW (paperTailRef hW hMR hFour A) :=
  TailPriceInputs.ofData
    (fun q _ h4 => (R q h4).toData.congrMu (paperTailRef_eq q h4 _).symm)
    (fun q _ h4 => (H q h4).sym_le) (fun q _ h4 => (H q h4).skew_le)

/-- **K1's (CP4) inputs from the changed tail records**: `ofTailPrices` with
`TailPriceInputs.ofRecords`. -/
noncomputable def ofTailRecords {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
    (R : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordInputs q (tailNe hW h4))
    (H : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordPrices (R q h4)) :
    ComparisonParts hW hMR hFour A :=
  ofTailPrices clique blk (TailPriceInputs.ofRecords R H)

/-- **K1's (CP4) inputs from the repaired tail records**: per tail prime, `TailRecordInputs` and
the two bounds `∑_{changed} π̃^s_ρ ≤ Π^{rep}(r)`, `∑_{changed} π̃^a_ρ ≤ Π^{rep}(r)`
(`lem:tail-prices`(ii), `cert:tail-caps`). -/
noncomputable def ofTailRepairs {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
    (R : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordInputs q (tailNe hW h4))
    (hs : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => UpperComparison.upperFate ρ = .changed), (R q h4).π ρ .sym ≤
        piRep (tailR q))
    (ha : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => UpperComparison.upperFate ρ = .changed), (R q h4).π ρ .skew ≤
        piRep (tailR q)) :
    ComparisonParts hW hMR hFour A :=
  ofTailRecords clique blk R fun q _ h4 => TailRecordPrices.ofRep (hs q h4) (ha q h4)

/-- The numbers of `ofTailRepairs`: `St + At ≤ 1.1·10^{-69}`. -/
theorem ofTailRepairs_St_At {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
    (R : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordInputs q (tailNe hW h4))
    (hs : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => UpperComparison.upperFate ρ = .changed), (R q h4).π ρ .sym ≤
        piRep (tailR q))
    (ha : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => UpperComparison.upperFate ρ = .changed), (R q h4).π ρ .skew ≤
        piRep (tailR q)) :
    (ofTailRepairs (hMR := hMR) (hFour := hFour) clique blk R hs ha).St +
        (ofTailRepairs (hMR := hMR) (hFour := hFour) clique blk R hs ha).At ≤ 11 / 10 ^ 70 :=
  tailSt_add_tailAt_le

end Sarkozy.TailPrices
