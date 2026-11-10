module

public import Sarkozy.TailPrices.Main

@[expose] public section

/-!
# The tail part of (CP8)(c) (`lem:tail-prices`(iv), `def:cp8`(c))

`paper/sections/27_tail_index.tex`, `lem:tail-prices`(iv): "`∑_{p ≥ P₄} η_p p^{1/4} < ∞` … so their
part of the sum in (CP8)(c) is at most `3 ∑_{p≥P₄} η_p p^{1/4}`". K1's field `Env.hCL` (field 18)
sums `q_𝔟^{1/4}(s_𝔟 + a_𝔟)` over all atoms of `CL`; this file gives its tail part.

* `tail_symTotal_eq`, `tail_skewTotal_eq`: at a tail atom `.inr j`, the totals of K1's `CL` are the
  prices `sprice`, `aprice` of the tail atom at `q_j^{2a_T}` (any `ComparisonParts`);
* **`tail_hCL_le`**: for `ofTailPrices clique blk T`, at every scale,
  `∑_j q_j^{1/4}(s_j + a_j) ≤ (k_S + k_A)/2^{124}`, in the exact summand form of `Env.hCL`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg)
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper
  Sarkozy.FirstStagePaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (v2Reference PrefixCoord paperAtomMap)
open Sarkozy.ComparisonLawPaper (DeletionInputs TailAtomInputs tailNe paperPrefixAccepted
  P4_le_paperTail)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.MainFinal (bOf specF hCF Blk ComparisonParts)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs PaperNumbers.paperCell}

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
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
    (T : TailPriceInputs hW (paperTailRef hW hMR hFour A)) (L : ℕ) :
    ∑ j : PaperJt L, TheoremCBlock.oneWeight (paperAtomMap bOf) paperTail paperPP paperEP L
        (.inr j) ^ ((1 : ℝ) / 4) *
      (symTotal ((ofTailPrices clique blk T).CL.π L) (.inr j) +
        skewTotal ((ofTailPrices clique blk T).CL.π L) (.inr j)) ≤ (kS + kA) / 2 ^ 124 := by
  have h := T.tail_weighted_le targetDecay_nonneg targetDecay_le L
  refine le_of_eq_of_le (sum_congr rfl fun j _ => ?_) h
  rw [tail_symTotal_eq, tail_skewTotal_eq, mul_comm]
  rfl

end Sarkozy.TailPrices
