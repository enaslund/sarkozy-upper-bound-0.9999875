module

public import Sarkozy.MainFinalF1.Tail
public import Sarkozy.TailCorrelations.Ledger

@[expose] public section

/-!
# K1's tail fields from TC's repairs `tailRp`, at TC's constants (`lem:tail-prices`)

The tail fields `tail`, `St`, `At`, `tail_S`, `tail_A` of K1's `ComparisonParts` (at `f1Cell`),
built from TC's (F7) repairs `TailCorrelations.tailRp hW` of the changed records (proved from H1)
instead of T2's repairs at the paper's caps `cert:tail-caps`. This copies T2's chain
(`MainFinalF1.ofTailRepairData` → `ofTailRepairs` → `ofTailRecords` → `tailInputsOfRecords` →
`TailPriceInputs.ofData` → `ofTailPrices`) with the paper's polynomial `Π^{rep}` and constants
`k_S`, `k_A` replaced by TC's:

* `Π^{rep}_{TC}(r) = tailConst(2⁸¹,2⁸¹)(W₂ r³ + W₃ r⁴)` (`TailCorrelations.piRepTC`);
* **`kSTC = 2¹⁰³`**, **`kATC = 2¹⁰²`**: `(Π^{rep}_{TC} + Π^{del})(r) ≤ kSTC r³` (`piSTC_le`, with
  the deletions `Π^{del}` of `eq:tail-polynomials`, proved by T2: `deleted_le_piDel`, `piS_le`) and
  `Π^{rep}_{TC}(r) ≤ kATC r³` (`TailCorrelations.piRepTC_le`), for `0 ≤ r ≤ 2⁻²⁵⁶`;
* **`tailStTC = kSTC/2²⁵³`**, **`tailAtTC = kATC/2²⁵³`**, `tailStTC + tailAtTC = 3/2¹⁵¹`
  (`tailTC_eq`; the paper's `S_tail + A_tail ≤ 1.1·10⁻⁶⁹` becomes `3/2¹⁵¹ < 10⁻⁴⁴`);
* **`ofTailTC clique blk`**: K1's `ComparisonParts` with the tail from `tailRp` and these numbers;
  `tail_S`, `tail_A` proved (`lem:tail-prices`(iv), T2's `sum_le_tail`);
* `tail_price_le_St_At` (any K1 `ComparisonParts`): the tail atoms cost at most `St + At` at every
  scale; `tail_hCL_le_TC`: the `q^{1/4}`-weighted tail sum is at most `(kSTC + kATC)/2¹²⁴`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MainFinalF1c

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
open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk paperTailRef paperTailRef_eq
  tail_symTotal_eq tail_skewTotal_eq)
open Sarkozy.TailPrices (TailRepairs piDel deleted_le_piDel piS_le piRep price_le_of_poly
  sum_le_tail sum_le_tail_weighted rpow_quarter P4_pos targetDecay_le)
open Sarkozy.TailCorrelations (tailRp piRepTC piRepTC_le tailRp_sum_π_poly)

/-! ## The constants -/

/-- `k_S` at TC's constants: `2¹⁰³`. -/
noncomputable def kSTC : ℝ := 2 ^ 103

/-- `k_A` at TC's constants: `2¹⁰²`. -/
noncomputable def kATC : ℝ := 2 ^ 102

/-- `S_tail` at TC's constants: `kSTC/2²⁵³`. -/
noncomputable def tailStTC : ℝ := kSTC / 2 ^ 253

/-- `A_tail` at TC's constants: `kATC/2²⁵³`. -/
noncomputable def tailAtTC : ℝ := kATC / 2 ^ 253

theorem kSTC_nonneg : 0 ≤ kSTC := by unfold kSTC; positivity

theorem kATC_nonneg : 0 ≤ kATC := by unfold kATC; positivity

/-- **`S_tail + A_tail = 3/2¹⁵¹`** at TC's constants. -/
theorem tailTC_eq : tailStTC + tailAtTC = 3 / 2 ^ 151 := by
  unfold tailStTC tailAtTC kSTC kATC
  norm_num

/-- **The tail total is below `10⁻⁴⁴`** (exact rational arithmetic). -/
theorem tailTC_lt : tailStTC + tailAtTC < 1 / 10 ^ 44 := by
  rw [tailTC_eq]
  norm_num

/-- `Π^{del}(r) ≤ k_S r³` (T2's `piS_le`, as `Π^{rep}(r) ≥ 0`). -/
theorem piDel_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2 ^ 256) :
    piDel r ≤ TailPrices.kS * r ^ 3 := by
  have h := piS_le h0 h1
  have hp : 0 ≤ piRep r := by
    unfold piRep TailPrices.cRep3 TailPrices.cRep4
    positivity
  linarith

/-- **`(Π^{rep}_{TC} + Π^{del})(r) ≤ 2¹⁰³ r³`** for `0 ≤ r ≤ 2⁻²⁵⁶`. -/
theorem piSTC_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2 ^ 256) :
    piRepTC r + piDel r ≤ kSTC * r ^ 3 := by
  have h2 := piRepTC_le h0 h1
  have h3 := piDel_le h0 h1
  have hr3 : 0 ≤ r ^ 3 := pow_nonneg h0 3
  have hk : (2 : ℝ) ^ 102 + TailPrices.kS ≤ 2 ^ 103 := by
    unfold TailPrices.kS; norm_num
  unfold kSTC
  nlinarith

/-! ## The tail atoms -/

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs AnalyticCells.f1Cell}

/-- **The tail atom at `q ≥ P₄`** from TC's repairs (T2's `tailInputsOfRecords`,
`TailPriceInputs.ofData`, with `Rp := tailRp hW`). -/
noncomputable def tailAtomTC (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : PaperAnalyticInputs AnalyticCells.f1Cell) (q : ℕ)
    [Fact q.Prime] (h4 : P4 ≤ q) :
    TailAtomInputs q (tailNe hW h4) (paperTailRef hW hMR hFour A q) :=
  (((tailRp hW q h4).toRecords).toData.congrMu (paperTailRef_eq q h4 _).symm).toInputs
    (ne_two_of_P4 q h4)

/-- `lem:tail-prices`(ii), symmetric, at TC's constants:
`∑_t π̃^s_t ≤ (Π^{rep}_{TC} + Π^{del})(r)`. -/
theorem tailAtomTC_sym_le (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) :
    ∑ t, (tailAtomTC hW hMR hFour A q h4).πt t .sym ≤ piRepTC (tailR q) + piDel (tailR q) := by
  change ∑ ρ : UpIdx, ((tailRp hW q h4).toRecords).piT ρ .sym ≤ _
  rw [TailPrices.TailRecordInputs.sum_piT_sym]
  exact add_le_add (tailRp_sum_π_poly hW q h4 .sym) (deleted_le_piDel (tailR_nonneg q))

/-- `lem:tail-prices`(ii), skew, at TC's constants: `∑_t π̃^a_t ≤ Π^{rep}_{TC}(r)`. -/
theorem tailAtomTC_skew_le (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) :
    ∑ t, (tailAtomTC hW hMR hFour A q h4).πt t .skew ≤ piRepTC (tailR q) := by
  change ∑ ρ : UpIdx, ((tailRp hW q h4).toRecords).piT ρ .skew ≤ _
  rw [TailPrices.TailRecordInputs.sum_piT_skew]
  exact tailRp_sum_π_poly hW q h4 .skew

/-- **`lem:tail-prices`(iii), symmetric, at TC's constants**: `s_q ≤ 2¹⁰³ q^{-(3/2-2a)}`. -/
theorem tailAtomTC_sprice_le (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (a : ℝ) :
    (tailAtomTC hW hMR hFour A q h4).toAtom.sprice ((q : ℝ) ^ (2 * a)) ≤
      kSTC * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) := by
  have e : (tailAtomTC hW hMR hFour A q h4).toAtom.sprice ((q : ℝ) ^ (2 * a)) =
      (∑ t, (tailAtomTC hW hMR hFour A q h4).πt t .sym) * (q : ℝ) ^ (2 * a) := by
    rw [sum_mul]
    rfl
  rw [e]
  exact price_le_of_poly h4 a (fun r => piRepTC r + piDel r) (fun _ h0 h1 => piSTC_le h0 h1)
    (tailAtomTC_sym_le q h4)

/-- **`lem:tail-prices`(iii), skew, at TC's constants**: `a_q ≤ 2¹⁰² q^{-(3/2-2a)}`. -/
theorem tailAtomTC_aprice_le (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (a : ℝ) :
    (tailAtomTC hW hMR hFour A q h4).toAtom.aprice ((q : ℝ) ^ (2 * a)) ≤
      kATC * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) := by
  have e : (tailAtomTC hW hMR hFour A q h4).toAtom.aprice ((q : ℝ) ^ (2 * a)) =
      (∑ t, (tailAtomTC hW hMR hFour A q h4).πt t .skew) * (q : ℝ) ^ (2 * a) := by
    rw [sum_mul]
    rfl
  rw [e]
  exact price_le_of_poly h4 a piRepTC (fun _ h0 h1 => piRepTC_le h0 h1)
    (tailAtomTC_skew_le q h4)

theorem paperTail_injOn (L : ℕ) : Set.InjOn (paperTail L) (univ : Finset (PaperJt L)) :=
  fun _ _ _ _ h => Subtype.ext h

/-! ## K1's comparison inputs -/

/-- **K1's (CP4) inputs with the tail from TC's repairs** (`lem:tail-prices`(i)–(iv), (F7) with the
correlation bounds of (F2), all from H1): T2's `ofTailPrices` with `St = tailStTC`,
`At = tailAtTC`. -/
noncomputable def ofTailTC
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b)) :
    ComparisonParts hW hMR hFour A where
  clique := clique
  blk := blk
  tail q _ h4 := tailAtomTC hW hMR hFour A q h4
  St := tailStTC
  At := tailAtTC
  tail_S L := sum_le_tail univ (paperTail L) (paperTail_injOn L)
    (fun j _ => P4_le_paperTail j) targetDecay_nonneg targetDecay_le kSTC_nonneg _
    (fun j _ => tailAtomTC_sprice_le _ (P4_le_paperTail j) targetDecay)
  tail_A L := sum_le_tail univ (paperTail L) (paperTail_injOn L)
    (fun j _ => P4_le_paperTail j) targetDecay_nonneg targetDecay_le kATC_nonneg _
    (fun j _ => tailAtomTC_aprice_le _ (P4_le_paperTail j) targetDecay)

theorem ofTailTC_St_At
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b)) :
    (ofTailTC (hMR := hMR) (hFour := hFour) clique blk).St +
      (ofTailTC (hMR := hMR) (hFour := hFour) clique blk).At = tailStTC + tailAtTC := rfl

/-- **The tail atoms cost at most `St + At` at every scale** (any K1 `ComparisonParts`; T2's
`tail_price_le` without the numerical value). -/
theorem tail_price_le_St_At (C : ComparisonParts hW hMR hFour A) (L : ℕ) :
    ∑ j : PaperJt L, (symTotal (C.CL.π L) (.inr j) + skewTotal (C.CL.π L) (.inr j)) ≤
      C.St + C.At := by
  have hS := C.tail_S L
  have hA := C.tail_A L
  have e : ∀ j : PaperJt L, symTotal (C.CL.π L) (.inr j) + skewTotal (C.CL.π L) (.inr j) =
      (C.tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
          (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) +
        (C.tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
          (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) := fun j => by
    rw [tail_symTotal_eq, tail_skewTotal_eq]
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib]
  linarith

/-- **The tail part of (CP8)(c) at TC's constants** (`def:cp8`(c)):
`∑_j q_j^{1/4}(s_j + a_j) ≤ (kSTC + kATC)/2¹²⁴` (T2's `tail_weighted_le`, same proof). -/
theorem tail_hCL_le_TC
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn AnalyticCells.f1Cell) (specF hW A b)) (L : ℕ) :
    ∑ j : PaperJt L, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L
        (.inr j) ^ ((1 : ℝ) / 4) *
      (symTotal ((ofTailTC (hMR := hMR) (hFour := hFour) clique blk).CL.π L) (.inr j) +
        skewTotal ((ofTailTC (hMR := hMR) (hFour := hFour) clique blk).CL.π L) (.inr j)) ≤
      (kSTC + kATC) / 2 ^ 124 := by
  have h : ∑ j : PaperJt L, ((tailAtomTC hW hMR hFour A (paperTail L j)
      (P4_le_paperTail j)).toAtom.sprice (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) +
      (tailAtomTC hW hMR hFour A (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay))) *
        ((paperTail L j : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ (kSTC + kATC) / 2 ^ 124 := by
    refine sum_le_tail_weighted univ (paperTail L) (paperTail_injOn L)
      (fun j _ => P4_le_paperTail j) targetDecay_nonneg targetDecay_le
      (add_nonneg kSTC_nonneg kATC_nonneg) _ (fun j _ => ?_)
    have hq0 : 0 < paperTail L j := lt_of_lt_of_le P4_pos (P4_le_paperTail j)
    have hw : 0 ≤ ((paperTail L j : ℕ) : ℝ) ^ (1 / 4 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h1 := tailAtomTC_sprice_le (hW := hW) (hMR := hMR) (hFour := hFour) (A := A) _
      (P4_le_paperTail j) targetDecay
    have h2 := tailAtomTC_aprice_le (hW := hW) (hMR := hMR) (hFour := hFour) (A := A) _
      (P4_le_paperTail j) targetDecay
    rw [← rpow_quarter hq0 targetDecay, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by rw [add_mul]; linarith) hw
  refine le_of_eq_of_le (sum_congr rfl fun j _ => ?_) h
  rw [tail_symTotal_eq, tail_skewTotal_eq, mul_comm]
  rfl

end Sarkozy.MainFinalF1c
