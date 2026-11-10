module

public import Sarkozy.MainFinalF1.Structure
public import Sarkozy.TailPrices.All

@[expose] public section

/-!
# T2's tail constructors at `f1Cell` (F1P)

T2's constructors of K1's `ComparisonParts` from the tail repairs at the paper's caps
(`lem:tail-prices`(i),(ii),(iv), `cert:tail-caps`, `def:tail-law`), copied from
`TailPrices/Main.lean`, `Weighted.lean`, `RecordMain.lean`, `RepairMain.lean`, `Caps.lean` with
`paperCell` replaced by `f1Cell`: `paperTailRef`, `ofTailPrices`, `tail_symTotal_eq`,
`tail_skewTotal_eq`, `tail_hCL_le`, `paperTailRef_eq`, `tailInputsOfRecords` (T2's
`TailPriceInputs.ofRecords`), `ofTailRecords`, `ofTailRepairs`, `ofTailRepairData`, `ofTailCaps`,
`ofTailCapsPaper`. They are typed against K1's `ComparisonParts` by name; the content (the tail
law at `q ≥ P₄`, the caps and the ledger `capLedger2`, `capLedger3`) does not depend on the block
partition, and every proof is T2's, verbatim.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MainFinalF1

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper
  Sarkozy.FirstStagePaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (v2Reference PrefixCoord paperAtomMap)
open Sarkozy.ComparisonLawPaper (DeletionInputs TailAtomInputs tailNe paperPrefixAccepted
  P4_le_paperTail)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.MainFinal (hCF)
open Sarkozy.TailPrices hiding paperTailRef ofTailPrices ofTailPrices_St_At tail_symTotal_eq
  tail_skewTotal_eq tail_hCL_le paperTailRef_eq ofTailRecords ofTailRepairs ofTailRepairs_St_At
  ofTailRepairData ofTailCaps ofTailCapsPaper

/-- The tail references of K1's construction: `μ_q = signedIntegral (μp q)` of the paper's
reference `v2Reference` (at a tail prime, V2's `tailLaw q`, `def:tail-law`). -/
noncomputable abbrev paperTailRef (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : PaperAnalyticInputs AnalyticCells.f1Cell) :
    ∀ (q : ℕ) [Fact q.Prime], SlotMeasure (ZMod q) :=
  fun q _ => signedIntegral ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μp q).weight

/-- **K1's (CP4) inputs from the clique and block inputs and `TailPriceInputs`**: the tail
fields `tail`, `St`, `At`, `tail_S`, `tail_A` of `MainFinal.ComparisonParts` at `a_T`, with
`St = S_tail = k_S/2^{253}`, `At = A_tail = k_A/2^{253}` and the tail sums proved
(`lem:tail-prices`(iv)). -/
noncomputable def ofTailPrices {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs AnalyticCells.f1Cell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b))
    (T : TailPriceInputs hW (paperTailRef hW hMR hFour A)) :
    ComparisonParts hW hMR hFour A where
  clique := clique
  blk := blk
  tail q _ h4 := T.atom q h4
  St := tailSt
  At := tailAt
  tail_S := T.tail_S_le targetDecay_nonneg targetDecay_le
  tail_A := T.tail_A_le targetDecay_nonneg targetDecay_le

section Weighted

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs AnalyticCells.f1Cell}

/-- The symmetric total of K1's `CL` at a tail atom is the tail atom's `sprice` at `q^{2a_T}`. -/
theorem tail_symTotal_eq (C : ComparisonParts hW hMR hFour A) (L : ℕ) (j : PaperJt L) :
    symTotal (C.CL.π L) (.inr j) =
      (C.tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
        (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  unfold symTotal TheoremCBlock.ComparisonLaw.π
  rfl

/-- The skew total of K1's `CL` at a tail atom is the tail atom's `aprice` at `q^{2a_T}`. -/
theorem tail_skewTotal_eq (C : ComparisonParts hW hMR hFour A) (L : ℕ) (j : PaperJt L) :
    skewTotal (C.CL.π L) (.inr j) =
      (C.tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
        (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) := by
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget
  unfold skewTotal TheoremCBlock.ComparisonLaw.π
  rfl

/-- **The tail part of `Env.hCL`** (`lem:tail-prices`(iv), `def:cp8`(c)): for the comparison inputs
`ofTailPrices clique blk T`, at every scale `L`,
`∑_j q_j^{1/4}(s_j + a_j) ≤ (k_S + k_A)/2^{124}`. -/
theorem tail_hCL_le
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b))
    (T : TailPriceInputs hW (paperTailRef hW hMR hFour A)) (L : ℕ) :
    ∑ j : PaperJt L, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L
        (.inr j) ^ ((1 : ℝ) / 4) *
      (symTotal ((ofTailPrices clique blk T).CL.π L) (.inr j) +
        skewTotal ((ofTailPrices clique blk T).CL.π L) (.inr j)) ≤ (kS + kA) / 2 ^ 124 := by
  have h := T.tail_weighted_le targetDecay_nonneg targetDecay_le L
  refine le_of_eq_of_le (sum_congr rfl fun j _ => ?_) h
  rw [tail_symTotal_eq, tail_skewTotal_eq, mul_comm]
  rfl

end Weighted

/-- **The reference of K1's construction at a tail prime is the tail law** (`def:tail-law`):
`μ_q = tailLaw q hne` for `q ≥ P₄` (V2's `tailFamilyFrom P₄`). -/
theorem paperTailRef_eq {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs AnalyticCells.f1Cell} (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q)
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
noncomputable def tailInputsOfRecords {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs AnalyticCells.f1Cell}
    (R : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordInputs q (tailNe hW h4))
    (H : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordPrices (R q h4)) :
    TailPriceInputs hW (paperTailRef hW hMR hFour A) :=
  TailPriceInputs.ofData
    (fun q _ h4 => (R q h4).toData.congrMu (paperTailRef_eq q h4 _).symm)
    (fun q _ h4 => (H q h4).sym_le) (fun q _ h4 => (H q h4).skew_le)

/-- **K1's (CP4) inputs from the changed tail records**: `ofTailPrices` with
`tailInputsOfRecords`. -/
noncomputable def ofTailRecords {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs AnalyticCells.f1Cell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b))
    (R : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordInputs q (tailNe hW h4))
    (H : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordPrices (R q h4)) :
    ComparisonParts hW hMR hFour A :=
  ofTailPrices clique blk (tailInputsOfRecords R H)

/-- **K1's (CP4) inputs from the repaired tail records**: per tail prime, `TailRecordInputs` and
the two bounds `∑_{changed} π̃^s_ρ ≤ Π^{rep}(r)`, `∑_{changed} π̃^a_ρ ≤ Π^{rep}(r)`
(`lem:tail-prices`(ii), `cert:tail-caps`). -/
noncomputable def ofTailRepairs {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs AnalyticCells.f1Cell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b))
    (R : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRecordInputs q (tailNe hW h4))
    (hs : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => UpperComparison.upperFate ρ = .changed), (R q h4).π ρ .sym ≤
        piRep (tailR q))
    (ha : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => UpperComparison.upperFate ρ = .changed), (R q h4).π ρ .skew ≤
        piRep (tailR q)) :
    ComparisonParts hW hMR hFour A :=
  ofTailRecords clique blk R fun q _ h4 => TailRecordPrices.ofRep (hs q h4) (ha q h4)

/-- **K1's (CP4) inputs from the repairs of the changed tail records** and the two price sums
(`lem:tail-prices`(ii)). -/
noncomputable def ofTailRepairData {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs AnalyticCells.f1Cell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b))
    (Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (tailNe hW h4))
    (hs : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), (Rp q h4).π ρ .sym ≤ piRep (tailR q))
    (ha : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), (Rp q h4).π ρ .skew ≤
        piRep (tailR q)) :
    ComparisonParts hW hMR hFour A :=
  ofTailRepairs clique blk (fun q _ h4 => (Rp q h4).toRecords) hs ha

/-- **K1's (CP4) inputs from the repairs and the caps** (`cert:tail-caps`): at every tail prime a
repair of every changed record with constants `C^ε_ρ ≤ K_ρ q^{-1/2}`, and the two numerical
ledger inequalities for the caps `K`. -/
noncomputable def ofTailCaps {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs AnalyticCells.f1Cell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b))
    (Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (tailNe hW h4))
    (K : UpIdx → ℝ)
    (hcap : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
      (e : ChangeType), (Rp q h4 t φ h).C e ≤ K (true, ⟨t, φ⟩) * tailR q)
    (h2 : ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 2),
      (tailWQ ρ : ℝ) * K ρ ≤ cRep3)
    (h3 : ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 3),
      (tailWQ ρ : ℝ) * K ρ ≤ cRep4) :
    ComparisonParts hW hMR hFour A :=
  ofTailRepairData clique blk Rp
    (fun q _ h4 => ((Rp q h4).sum_π_le K .sym fun t φ h => hcap q h4 t φ h .sym).trans
      (changed_ledger_le h2 h3 (tailR_nonneg q)))
    (fun q _ h4 => ((Rp q h4).sum_π_le K .skew fun t φ h => hcap q h4 t φ h .skew).trans
      (changed_ledger_le h2 h3 (tailR_nonneg q)))

/-- **K1's (CP4) inputs from the repairs at the paper's caps** (`cert:tail-caps`): per tail prime,
a repair of every changed record with constants `C^ε_ρ ≤ K_ρ q^{-1/2}`, `K = tailCap`. The ledger
inequalities are `capLedger2`, `capLedger3`. -/
noncomputable def ofTailCapsPaper {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs AnalyticCells.f1Cell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b))
    (Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (tailNe hW h4))
    (hcap : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
      (e : ChangeType), (Rp q h4 t φ h).C e ≤ tailCap (true, ⟨t, φ⟩) * tailR q) :
    ComparisonParts hW hMR hFour A :=
  ofTailCaps clique blk Rp tailCap hcap capLedger2 capLedger3

end Sarkozy.MainFinalF1
