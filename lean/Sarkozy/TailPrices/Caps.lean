module

public import Sarkozy.TailPrices.RepairMain

@[expose] public section





open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.GramBracketPaper
  Sarkozy.FirstStagePaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (v2Reference PrefixCoord)
open Sarkozy.ComparisonLawPaper (DeletionInputs paperPrefixAccepted tailNe)
open Sarkozy.MiddleComparison (SpecData)
open Sarkozy.MainFinal (bOf specF hCF Blk ComparisonParts)

/-- **The 94 tail repair caps** (`cert:tail-caps`): record and cap `C_ϱ`, from
`upper_v2_local.json`, `tail_comparison.repair2.caps` and `repair3.caps`. -/
def tailCapTable : List (UpIdx × ℚ) := [
  ((true, ⟨(.L, .R), ((), ((0 : Fin 2), (0 : Fin 3)))⟩), 6159219561 / 500000000),
  ((true, ⟨(.L, .R), ((), ((0 : Fin 2), (1 : Fin 3)))⟩), 6159219561 / 500000000),
  ((true, ⟨(.L, .R), ((), ((0 : Fin 2), (2 : Fin 3)))⟩), 6159219561 / 500000000),
  ((true, ⟨(.L, .R), ((), ((1 : Fin 2), (0 : Fin 3)))⟩), 6159219561 / 500000000),
  ((true, ⟨(.L, .R), ((), ((1 : Fin 2), (1 : Fin 3)))⟩), 6159219561 / 500000000),
  ((true, ⟨(.L, .R), ((), ((1 : Fin 2), (2 : Fin 3)))⟩), 6159219561 / 500000000),
  ((true, ⟨(.D, .D), ((1 : Fin 3), (0 : Fin 3))⟩), 3590212419 / 500000000),
  ((true, ⟨(.D, .D), ((1 : Fin 3), (1 : Fin 3))⟩), 3590212419 / 500000000),
  ((true, ⟨(.D, .D), ((1 : Fin 3), (2 : Fin 3))⟩), 3590212419 / 500000000),
  ((true, ⟨(.D, .S), ((1 : Fin 3), (0 : Fin 2))⟩), 10414518489 / 1000000000),
  ((true, ⟨(.D, .S), ((1 : Fin 3), (1 : Fin 2))⟩), 10414518489 / 1000000000),
  ((true, ⟨(.D, .D), ((2 : Fin 3), (0 : Fin 3))⟩), 3590212419 / 500000000),
  ((true, ⟨(.D, .D), ((2 : Fin 3), (1 : Fin 3))⟩), 3590212419 / 500000000),
  ((true, ⟨(.D, .D), ((2 : Fin 3), (2 : Fin 3))⟩), 3590212419 / 500000000),
  ((true, ⟨(.D, .S), ((2 : Fin 3), (0 : Fin 2))⟩), 10414518489 / 1000000000),
  ((true, ⟨(.D, .S), ((2 : Fin 3), (1 : Fin 2))⟩), 10414518489 / 1000000000),
  ((true, ⟨(.S, .D), ((0 : Fin 2), (0 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.S, .D), ((0 : Fin 2), (1 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.S, .D), ((0 : Fin 2), (2 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.S, .S), ((0 : Fin 2), (0 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.S, .S), ((0 : Fin 2), (1 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.S, .D), ((1 : Fin 2), (0 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.S, .D), ((1 : Fin 2), (1 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.S, .D), ((1 : Fin 2), (2 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.S, .S), ((1 : Fin 2), (0 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.S, .S), ((1 : Fin 2), (1 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .L), (((0 : Fin 2), (1 : Fin 3)), ())⟩), 11619211401 / 1000000000),
  ((true, ⟨(.R, .L), (((0 : Fin 2), (2 : Fin 3)), ())⟩), 11619211401 / 1000000000),
  ((true, ⟨(.R, .L), (((1 : Fin 2), (0 : Fin 3)), ())⟩), 11619211401 / 1000000000),
  ((true, ⟨(.R, .L), (((1 : Fin 2), (2 : Fin 3)), ())⟩), 11619211401 / 1000000000),
  ((true, ⟨(.L, .C), ((), (0 : Fin 2))⟩), 22947466461 / 1000000000),
  ((true, ⟨(.L, .C), ((), (1 : Fin 2))⟩), 22947466461 / 1000000000),
  ((true, ⟨(.D, .R), ((0 : Fin 3), ((0 : Fin 2), (0 : Fin 3)))⟩), 3214233277 / 200000000),
  ((true, ⟨(.D, .R), ((0 : Fin 3), ((0 : Fin 2), (1 : Fin 3)))⟩), 3214233277 / 200000000),
  ((true, ⟨(.D, .R), ((0 : Fin 3), ((0 : Fin 2), (2 : Fin 3)))⟩), 3214233277 / 200000000),
  ((true, ⟨(.D, .R), ((0 : Fin 3), ((1 : Fin 2), (0 : Fin 3)))⟩), 3214233277 / 200000000),
  ((true, ⟨(.D, .R), ((0 : Fin 3), ((1 : Fin 2), (1 : Fin 3)))⟩), 3214233277 / 200000000),
  ((true, ⟨(.D, .R), ((0 : Fin 3), ((1 : Fin 2), (2 : Fin 3)))⟩), 3214233277 / 200000000),
  ((true, ⟨(.D, .R), ((1 : Fin 3), ((0 : Fin 2), (0 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((1 : Fin 3), ((0 : Fin 2), (1 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((1 : Fin 3), ((0 : Fin 2), (2 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((1 : Fin 3), ((1 : Fin 2), (0 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((1 : Fin 3), ((1 : Fin 2), (1 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((1 : Fin 3), ((1 : Fin 2), (2 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((2 : Fin 3), ((0 : Fin 2), (0 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((2 : Fin 3), ((0 : Fin 2), (1 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((2 : Fin 3), ((0 : Fin 2), (2 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((2 : Fin 3), ((1 : Fin 2), (0 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((2 : Fin 3), ((1 : Fin 2), (1 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.D, .R), ((2 : Fin 3), ((1 : Fin 2), (2 : Fin 3)))⟩), 4621361933 / 500000000),
  ((true, ⟨(.S, .R), ((0 : Fin 2), ((0 : Fin 2), (0 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((0 : Fin 2), ((0 : Fin 2), (1 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((0 : Fin 2), ((0 : Fin 2), (2 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((0 : Fin 2), ((1 : Fin 2), (0 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((0 : Fin 2), ((1 : Fin 2), (1 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((0 : Fin 2), ((1 : Fin 2), (2 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((1 : Fin 2), ((0 : Fin 2), (0 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((1 : Fin 2), ((0 : Fin 2), (1 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((1 : Fin 2), ((0 : Fin 2), (2 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((1 : Fin 2), ((1 : Fin 2), (0 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((1 : Fin 2), ((1 : Fin 2), (1 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.S, .R), ((1 : Fin 2), ((1 : Fin 2), (2 : Fin 3)))⟩), 4526081053 / 500000000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (0 : Fin 3)), (0 : Fin 3))⟩), 6414264033 / 1000000000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (0 : Fin 3)), (1 : Fin 3))⟩), 6414264033 / 1000000000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (0 : Fin 3)), (2 : Fin 3))⟩), 6414264033 / 1000000000),
  ((true, ⟨(.R, .S), (((0 : Fin 2), (0 : Fin 3)), (0 : Fin 2))⟩), 4000001289 / 1000000000),
  ((true, ⟨(.R, .S), (((0 : Fin 2), (0 : Fin 3)), (1 : Fin 2))⟩), 4000001289 / 1000000000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (1 : Fin 3)), (0 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (1 : Fin 3)), (1 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (1 : Fin 3)), (2 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .S), (((0 : Fin 2), (1 : Fin 3)), (0 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .S), (((0 : Fin 2), (1 : Fin 3)), (1 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (2 : Fin 3)), (0 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (2 : Fin 3)), (1 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((0 : Fin 2), (2 : Fin 3)), (2 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .S), (((0 : Fin 2), (2 : Fin 3)), (0 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .S), (((0 : Fin 2), (2 : Fin 3)), (1 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (0 : Fin 3)), (0 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (0 : Fin 3)), (1 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (0 : Fin 3)), (2 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .S), (((1 : Fin 2), (0 : Fin 3)), (0 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .S), (((1 : Fin 2), (0 : Fin 3)), (1 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (1 : Fin 3)), (0 : Fin 3))⟩), 6414264033 / 1000000000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (1 : Fin 3)), (1 : Fin 3))⟩), 6414264033 / 1000000000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (1 : Fin 3)), (2 : Fin 3))⟩), 6414264033 / 1000000000),
  ((true, ⟨(.R, .S), (((1 : Fin 2), (1 : Fin 3)), (0 : Fin 2))⟩), 4000001289 / 1000000000),
  ((true, ⟨(.R, .S), (((1 : Fin 2), (1 : Fin 3)), (1 : Fin 2))⟩), 4000001289 / 1000000000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (2 : Fin 3)), (0 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (2 : Fin 3)), (1 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .D), (((1 : Fin 2), (2 : Fin 3)), (2 : Fin 3))⟩), 650894531 / 62500000),
  ((true, ⟨(.R, .S), (((1 : Fin 2), (2 : Fin 3)), (0 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.R, .S), (((1 : Fin 2), (2 : Fin 3)), (1 : Fin 2))⟩), 5657033253 / 500000000),
  ((true, ⟨(.C, .L), ((0 : Fin 2), ())⟩), 22956406437 / 1000000000),
  ((true, ⟨(.C, .L), ((1 : Fin 2), ())⟩), 22956406437 / 1000000000)]

/-- The cap of a record (`0` off the table). -/
def tailCapQ (ρ : UpIdx) : ℚ := (tailCapTable.lookup ρ).getD 0

/-- **The table reproduces `c^{rep}_3`**: `∑_{two-layer, deg 2} w_ρ K_ρ = c^{rep}_3`. -/
theorem capTable_rep3 :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => ρ.1 = true ∧ upperDeg ρ = 2), tailWQ ρ * tailCapQ ρ =
      73056854152246473 / 12500000000 := by
  decide +kernel

/-- **The table reproduces `c^{rep}_4`**: `∑_{two-layer, deg 3} w_ρ K_ρ = c^{rep}_4`. -/
theorem capTable_rep4 :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => ρ.1 = true ∧ upperDeg ρ = 3), tailWQ ρ * tailCapQ ρ =
      149151332035400049 / 68359375 := by
  decide +kernel

/-- **Every changed record has a positive cap**. -/
theorem changed_cap_pos : ∀ ρ : UpIdx, upperFate ρ = .changed → 0 < tailCapQ ρ := by
  decide +kernel

/-- The records of the table that W8's fate does not change: `G₀₁L` and `G₁₀L`, kept. -/
theorem capTable_extra : ∀ ρ : UpIdx, 0 < tailCapQ ρ → upperFate ρ ≠ .changed →
    ρ = (true, ⟨(.R, .L), (((0 : Fin 2), (1 : Fin 3)), ())⟩) ∨
      ρ = (true, ⟨(.R, .L), (((1 : Fin 2), (0 : Fin 3)), ())⟩) := by
  decide +kernel

/-- **The ledger inequality in degree two** over the changed records (rational form). -/
theorem capLedger2Q :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 2),
      tailWQ ρ * tailCapQ ρ ≤ 73056854152246473 / 12500000000 := by
  decide +kernel

/-- **The ledger inequality in degree three** over the changed records (rational form). -/
theorem capLedger3Q :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 3),
      tailWQ ρ * tailCapQ ρ ≤ 149151332035400049 / 68359375 := by
  decide +kernel

/-- The caps as reals. -/
noncomputable def tailCap (ρ : UpIdx) : ℝ := (tailCapQ ρ : ℝ)

theorem capLedger2 :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 2),
      (tailWQ ρ : ℝ) * tailCap ρ ≤ cRep3 := by
  have h : ((∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 2),
      tailWQ ρ * tailCapQ ρ : ℚ) : ℝ) ≤ ((73056854152246473 / 12500000000 : ℚ) : ℝ) := by
    exact_mod_cast capLedger2Q
  push_cast at h
  unfold tailCap cRep3
  exact h

theorem capLedger3 :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 3),
      (tailWQ ρ : ℝ) * tailCap ρ ≤ cRep4 := by
  have h : ((∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 3),
      tailWQ ρ * tailCapQ ρ : ℚ) : ℝ) ≤ ((149151332035400049 / 68359375 : ℚ) : ℝ) := by
    exact_mod_cast capLedger3Q
  push_cast at h
  unfold tailCap cRep4
  exact h

/-- **K1's (CP4) inputs from the repairs at the paper's caps** (`cert:tail-caps`): per tail prime,
a repair of every changed record with constants `C^ε_ρ ≤ K_ρ q^{-1/2}`, `K = tailCap`. The ledger
inequalities are `capLedger2`, `capLedger3`. -/
noncomputable def ofTailCapsPaper {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
    (Rp : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (tailNe hW h4))
    (hcap : ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (h : upperFate (true, ⟨t, φ⟩) = .changed)
      (e : ChangeType), (Rp q h4 t φ h).C e ≤ tailCap (true, ⟨t, φ⟩) * tailR q) :
    ComparisonParts hW hMR hFour A :=
  ofTailCaps clique blk Rp tailCap hcap capLedger2 capLedger3

end Sarkozy.TailPrices
