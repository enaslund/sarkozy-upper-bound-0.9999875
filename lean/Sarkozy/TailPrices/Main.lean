module

public import Sarkozy.TailPrices.Scale
public import Sarkozy.TailPrices.Accepted
public import Sarkozy.MainFinal.Structure

@[expose] public section





open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper
  Sarkozy.FirstStagePaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (v2Reference PrefixCoord)
open Sarkozy.ComparisonLawPaper (DeletionInputs TailAtomInputs tailNe paperPrefixAccepted
  P4_le_paperTail)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.MainFinal (bOf specF hCF Blk ComparisonParts)

structure TailPriceInputs (hW : Target.Weil) (μ : ∀ (q : ℕ) [Fact q.Prime], SlotMeasure (ZMod q))
    where
  atom : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailAtomInputs q (tailNe hW h4) (μ q)
  sym_le : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
    ∑ t, (atom q h4).πt t .sym ≤ piRep (tailR q) + piDel (tailR q)
  skew_le : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
    ∑ t, (atom q h4).πt t .skew ≤ piRep (tailR q)

/-- `S_tail = k_S/2^{253}` (`lem:tail-prices`(iv), at any `0 ≤ a ≤ 1/1024`). -/
noncomputable def tailSt : ℝ := kS / 2 ^ 253

/-- `A_tail = k_A/2^{253}` (`lem:tail-prices`(iv), at any `0 ≤ a ≤ 1/1024`). -/
noncomputable def tailAt : ℝ := kA / 2 ^ 253

/-- **`S_tail + A_tail ≤ 1.1·10^{-69}`**. -/
theorem tailSt_add_tailAt_le : tailSt + tailAt ≤ 11 / 10 ^ 70 := by
  unfold tailSt tailAt kS kA
  norm_num

theorem tailSt_nonneg : 0 ≤ tailSt := div_nonneg kS_nonneg (by positivity)

theorem tailAt_nonneg : 0 ≤ tailAt := div_nonneg kA_nonneg (by positivity)

/-- `a_T ≤ 1/1024`. -/
theorem targetDecay_le : targetDecay ≤ 1 / 1024 := by
  unfold targetDecay
  norm_num

namespace TailPriceInputs

variable {hW : Target.Weil} {μ : ∀ (q : ℕ) [Fact q.Prime], SlotMeasure (ZMod q)}
  (T : TailPriceInputs hW μ)

/-- The symmetric price of a tail atom is its unpriced total times the selection factor. -/
theorem sprice_eq {q : ℕ} [Fact q.Prime] (h4 : P4 ≤ q) (sel : ℝ) :
    (T.atom q h4).toAtom.sprice sel = (∑ t, (T.atom q h4).πt t .sym) * sel := by
  rw [sum_mul]
  rfl

/-- The skew price of a tail atom is its unpriced total times the selection factor. -/
theorem aprice_eq {q : ℕ} [Fact q.Prime] (h4 : P4 ≤ q) (sel : ℝ) :
    (T.atom q h4).toAtom.aprice sel = (∑ t, (T.atom q h4).πt t .skew) * sel := by
  rw [sum_mul]
  rfl

/-- **`lem:tail-prices`(iii), symmetric part**: `s_q ≤ k_S q^{-(3/2-2a)}`. -/
theorem sprice_le {q : ℕ} [Fact q.Prime] (h4 : P4 ≤ q) (a : ℝ) :
    (T.atom q h4).toAtom.sprice ((q : ℝ) ^ (2 * a)) ≤ kS * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) := by
  rw [T.sprice_eq]
  exact sym_price_le h4 a (T.sym_le q h4)

/-- **`lem:tail-prices`(iii), skew part**: `a_q ≤ k_A q^{-(3/2-2a)}`. -/
theorem aprice_le {q : ℕ} [Fact q.Prime] (h4 : P4 ≤ q) (a : ℝ) :
    (T.atom q h4).toAtom.aprice ((q : ℝ) ^ (2 * a)) ≤ kA * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) := by
  rw [T.aprice_eq]
  exact skew_price_le h4 a (T.skew_le q h4)

theorem paperTail_injOn (L : ℕ) : Set.InjOn (paperTail L) (univ : Finset (PaperJt L)) :=
  fun _ _ _ _ h => Subtype.ext h

/-- **`lem:tail-prices`(iv), `S_tail`**: at every scale `L` and every `0 ≤ a ≤ 1/1024`,
`∑_{P₄ ≤ p ≤ N^{1/20}} s_p ≤ k_S/2^{253}`. -/
theorem tail_S_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 1024) (L : ℕ) :
    ∑ j : PaperJt L, (T.atom (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * a)) ≤ tailSt :=
  sum_le_tail univ (paperTail L) (paperTail_injOn L) (fun j _ => P4_le_paperTail j) ha0 ha
    kS_nonneg _ (fun j _ => T.sprice_le (P4_le_paperTail j) a)

/-- **`lem:tail-prices`(iv), `A_tail`**: at every scale `L` and every `0 ≤ a ≤ 1/1024`,
`∑_{P₄ ≤ p ≤ N^{1/20}} a_p ≤ k_A/2^{253}`. -/
theorem tail_A_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 1024) (L : ℕ) :
    ∑ j : PaperJt L, (T.atom (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * a)) ≤ tailAt :=
  sum_le_tail univ (paperTail L) (paperTail_injOn L) (fun j _ => P4_le_paperTail j) ha0 ha
    kA_nonneg _ (fun j _ => T.aprice_le (P4_le_paperTail j) a)

/-- **`lem:tail-prices`(iv), the weighted sum**: at every scale `L` and `0 ≤ a ≤ 1/1024`,
`∑_{P₄ ≤ p ≤ N^{1/20}} (s_p + a_p) p^{1/4} ≤ (k_S + k_A)/2^{124}` (the paper's
`∑_{p ≥ P₄} η_p p^{1/4} < ∞`, in explicit form; used in (CP8)(c)). -/
theorem tail_weighted_le {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 1024) (L : ℕ) :
    ∑ j : PaperJt L, ((T.atom (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * a)) +
      (T.atom (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * a))) * ((paperTail L j : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤
        (kS + kA) / 2 ^ 124 := by
  refine sum_le_tail_weighted univ (paperTail L) (paperTail_injOn L)
    (fun j _ => P4_le_paperTail j) ha0 ha (add_nonneg kS_nonneg kA_nonneg) _ (fun j _ => ?_)
  have hq0 : 0 < paperTail L j := lt_of_lt_of_le P4_pos (P4_le_paperTail j)
  have hw : 0 ≤ ((paperTail L j : ℕ) : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 := T.sprice_le (P4_le_paperTail j) a
  have h2 := T.aprice_le (P4_le_paperTail j) a
  rw [← rpow_quarter hq0 a, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by rw [add_mul]; linarith) hw

/-- **`TailPriceInputs` from `TailAtomData`** (the accepted part given by its nonroot part
`ρ_q`, `TailRestData`; its uniform marginals and `Unif(Ω)` query pairs proved,
`TailRestData.accepted`). -/
noncomputable def ofData
    (D : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailAtomData q (tailNe hW h4) (μ q))
    (hs : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ t, (D q h4).πt t .sym ≤ piRep (tailR q) + piDel (tailR q))
    (ha : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q),
      ∑ t, (D q h4).πt t .skew ≤ piRep (tailR q)) :
    TailPriceInputs hW μ where
  atom q _ h4 := (D q h4).toInputs (ne_two_of_P4 q h4)
  sym_le q _ h4 := hs q h4
  skew_le q _ h4 := ha q h4

end TailPriceInputs

/-- The tail references of K1's construction: `μ_q = signedIntegral (μp q)` of the paper's
reference `v2Reference` (at a tail prime, V2's `tailLaw q`, `def:tail-law`). -/
noncomputable abbrev paperTailRef (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : PaperAnalyticInputs PaperNumbers.paperCell) :
    ∀ (q : ℕ) [Fact q.Prime], SlotMeasure (ZMod q) :=
  fun q _ => signedIntegral ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μp q).weight

/-- **K1's (CP4) inputs from the clique and block inputs and `TailPriceInputs`**: the tail
fields `tail`, `St`, `At`, `tail_S`, `tail_A` of `MainFinal.ComparisonParts` at `a_T`, with
`St = S_tail = k_S/2^{253}`, `At = A_tail = k_A/2^{253}` and the tail sums proved
(`lem:tail-prices`(iv)). -/
noncomputable def ofTailPrices {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
    (T : TailPriceInputs hW (paperTailRef hW hMR hFour A)) :
    ComparisonParts hW hMR hFour A where
  clique := clique
  blk := blk
  tail q _ h4 := T.atom q h4
  St := tailSt
  At := tailAt
  tail_S := T.tail_S_le targetDecay_nonneg targetDecay_le
  tail_A := T.tail_A_le targetDecay_nonneg targetDecay_le

/-- The numbers of `ofTailPrices`: `St + At ≤ 1.1·10^{-69}`. -/
theorem ofTailPrices_St_At {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
    (T : TailPriceInputs hW (paperTailRef hW hMR hFour A)) :
    (ofTailPrices clique blk T).St + (ofTailPrices clique blk T).At ≤ 11 / 10 ^ 70 :=
  tailSt_add_tailAt_le

end Sarkozy.TailPrices
