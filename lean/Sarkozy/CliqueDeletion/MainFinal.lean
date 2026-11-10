module

public import Sarkozy.CliqueDeletion.Price
public import Sarkozy.MainFinal.Structure

@[expose] public section




open Finset
open scoped BigOperators

namespace Sarkozy.CliqueDeletion

open Sarkozy.TheoremC Sarkozy.MainFinal Sarkozy.MainAnchor Sarkozy.MainTarget
  Sarkozy.CancellationSteps
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.PartVLaws (v2Reference PrefixCoord)
open Sarkozy.ComparisonLawPaper (DeletionInputs TailAtomInputs tailNe paperPrefixAccepted
  P4_le_paperTail)
open Sarkozy.MiddleComparison (SpecData)

/-- **K1's field `ComparisonParts.clique`, proved** (`lem:frontier:iidenergy`(ii),
`lem:frontier:iidlocal`(iv),(v); for `p ≥ 2¹⁶` `thm:density:iid-prefix`(a),(c)). -/
noncomputable def cliqueK1 (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : BlockSpecPaper.PaperAnalyticInputs PaperNumbers.paperCell) (q : PrefixCoord) :
    DeletionInputs ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries :=
  paperCliqueDeletion bOf hW (specF hW A) (hCF hW hMR hFour) q

theorem cliqueK1_ω_le (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
    (A : BlockSpecPaper.PaperAnalyticInputs PaperNumbers.paperCell) (q : PrefixCoord) :
    (cliqueK1 hW hMR hFour A q).ω ≤ 12 / 2 ^ PartV.digitPairs :=
  paperCliqueDeletion_ω_le bOf hW (specF hW A) (hCF hW hMR hFour) q

/-- **K1's `ComparisonParts` with the square-clique field proved**: the class-three blocks, the
tail atoms and the two tail numbers remain (`def:cp4`). -/
noncomputable def comparisonPartsOfProvedClique (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : BlockSpecPaper.PaperAnalyticInputs PaperNumbers.paperCell)
    (blk : ∀ b : Blk, SpecData hW (BlockSpecPaper.paperIn PaperNumbers.paperCell) (specF hW A b))
    (tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
      TailAtomInputs q (tailNe hW h4)
        (signedIntegral ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μp q).weight))
    (St At : ℝ)
    (tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St)
    (tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At) :
    ComparisonParts hW hMR hFour A where
  clique := cliqueK1 hW hMR hFour A
  blk := blk
  tail := tail
  St := St
  At := At
  tail_S := tail_S
  tail_A := tail_A

/-- **The square-clique price of `ofProvedClique`** (`lem:frontier:iidenergy`(iii),(iv)):
`∑_p ω_p q_p^{2a_T} ≤ 12 · 2^{-534}`. -/
theorem ofProvedClique_cliquePrice_sum_le (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (A : BlockSpecPaper.PaperAnalyticInputs PaperNumbers.paperCell)
    (blk : ∀ b : Blk, SpecData hW (BlockSpecPaper.paperIn PaperNumbers.paperCell) (specF hW A b))
    (tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
      TailAtomInputs q (tailNe hW h4)
        (signedIntegral ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μp q).weight))
    (St At : ℝ)
    (tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St)
    (tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At) :
    ∑ q, (comparisonPartsOfProvedClique hW hMR hFour A blk tail St At tail_S
      tail_A).Ci.cliquePrice q ≤ 12 / 2 ^ 534 :=
  ComparisonInputs.cliquePrice_sum_le bOf _ (cliqueK1_ω_le hW hMR hFour A)

end Sarkozy.CliqueDeletion
