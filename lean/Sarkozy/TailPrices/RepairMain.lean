module

public import Sarkozy.TailPrices.RecordMain
public import Sarkozy.TailPrices.Repairs

@[expose] public section

/-!
# K1's tail fields from the repairs and their caps (`lem:tail-prices`, `cert:tail-caps`)

`paper/sections/27_tail_index.tex`, `eq:tail-polynomials`, `cert:tail-caps`, `lem:tail-prices`(ii):
"A repaired record of state `𝔱` is charged at most `w_𝔱 C_ϱ r^{deg 𝔱 + 1}` in each part, and summing
gives `Π^{rep}(r)`".

* `TailRepairs.π_le_cap`, **`TailRepairs.sum_π_le`**: if every repair has constants
  `C^ε_ρ ≤ K_ρ r` (the cap `K_ρ`, `cert:tail-caps`), then the changed prices sum to at most
  `∑_{changed} c^μ_ρ K_ρ r`;
* **`changed_ledger_le`**: the cap ledger: if `∑_{changed, deg 2} w_ρ K_ρ ≤ c^{rep}_3` and
  `∑_{changed, deg 3} w_ρ K_ρ ≤ c^{rep}_4` (numerical, at the paper's caps), then
  `∑_{changed} c^μ_ρ K_ρ r ≤ Π^{rep}(r)` for every `r ≥ 0`;
* **`ofTailRepairData`**: K1's `ComparisonParts` from `clique`, `blk`, a repair of every changed
  record at every tail prime, and the two price sums;
* **`ofTailCaps`**: the same with the price sums replaced by the caps `K` (`C^ε_ρ ≤ K_ρ r` at every
  tail prime) and the two numerical ledger inequalities.
-/

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

namespace TailRepairs

variable {p : ℕ} [Fact p.Prime] {hne : TailNonempty p} (Rp : TailRepairs p hne)

/-- A changed price is at most `c^μ_ρ K_ρ r` when the repair constant is at most `K_ρ r`. -/
theorem π_le_cap (K : UpIdx → ℝ) (e : ChangeType)
    (hK : ∀ t φ (h : upperFate (true, ⟨t, φ⟩) = .changed), (Rp t φ h).C e ≤ K (true, ⟨t, φ⟩) * tailR p)
    (ρ : UpIdx) (hρ : upperFate ρ = .changed) :
    Rp.π ρ e ≤ upCoeff tailWeights (tailR p) ρ * K ρ * tailR p := by
  have hr := tailR_nonneg p
  have hP := one_le_upPoly tailWeights hr
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact absurd hρ (folded_not_changed t φ)
  · simp only [π, hρ, ↓reduceDIte]
    have hc := upCoeff_nonneg tailWeights hr (true, ⟨t, φ⟩)
    have hC := (Rp t φ hρ).C_nonneg e
    have hinv : (upPoly tailWeights (tailR p))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP
    have hinv0 : 0 ≤ (upPoly tailWeights (tailR p))⁻¹ := inv_nonneg.mpr (by linarith)
    calc (upPoly tailWeights (tailR p))⁻¹ * upCoeff tailWeights (tailR p) (true, ⟨t, φ⟩) *
          (Rp t φ hρ).C e ≤ 1 * upCoeff tailWeights (tailR p) (true, ⟨t, φ⟩) * (Rp t φ hρ).C e :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv hc) hC
      _ ≤ upCoeff tailWeights (tailR p) (true, ⟨t, φ⟩) * (K (true, ⟨t, φ⟩) * tailR p) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left (hK t φ hρ) hc
      _ = _ := by ring

/-- **The changed prices are bounded by the caps**. -/
theorem sum_π_le (K : UpIdx → ℝ) (e : ChangeType)
    (hK : ∀ t φ (h : upperFate (true, ⟨t, φ⟩) = .changed), (Rp t φ h).C e ≤ K (true, ⟨t, φ⟩) * tailR p) :
    ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), Rp.π ρ e ≤
      ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed),
        upCoeff tailWeights (tailR p) ρ * K ρ * tailR p :=
  sum_le_sum fun ρ hρ => Rp.π_le_cap K e hK ρ (mem_filter.mp hρ).2

end TailRepairs

/-- **The cap ledger** (`eq:tail-polynomials`, `cert:tail-caps`): if the caps `K` satisfy
`∑_{changed, deg 2} w_ρ K_ρ ≤ c^{rep}_3` and `∑_{changed, deg 3} w_ρ K_ρ ≤ c^{rep}_4`, then
`∑_{changed} c^μ_ρ K_ρ r ≤ Π^{rep}(r)` for `r ≥ 0` (changed records have degree two or three). -/
theorem changed_ledger_le {K : UpIdx → ℝ}
    (h2 : ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 2),
      (tailWQ ρ : ℝ) * K ρ ≤ cRep3)
    (h3 : ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 3),
      (tailWQ ρ : ℝ) * K ρ ≤ cRep4)
    {r : ℝ} (hr : 0 ≤ r) :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed),
      upCoeff tailWeights r ρ * K ρ * r ≤ piRep r := by
  have hmaps : ∀ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed),
      upperDeg ρ ∈ ({2, 3} : Finset ℕ) := by
    intro ρ hρ
    rcases (upperFate_degrees ρ).1 (mem_filter.mp hρ).2 with h | h <;> simp [h]
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ d, ∑ ρ ∈ (univ.filter (fun ρ : UpIdx => upperFate ρ = .changed)).filter
      (fun ρ => upperDeg ρ = d), upCoeff tailWeights r ρ * K ρ * r =
        (∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = d),
          (tailWQ ρ : ℝ) * K ρ) * r ^ (d + 1) := by
    intro d
    rw [filter_filter, sum_mul]
    refine sum_congr rfl fun ρ hρ => ?_
    rw [upCoeff_tail, (mem_filter.mp hρ).2.2]
    ring
  simp only [hfib]
  rw [sum_insert (by decide), sum_singleton,
    show (2 : ℕ) + 1 = 3 from rfl, show (3 : ℕ) + 1 = 4 from rfl]
  unfold piRep
  have hr3 := pow_nonneg hr 3
  have hr4 := pow_nonneg hr 4
  linarith [mul_le_mul_of_nonneg_right h2 hr3, mul_le_mul_of_nonneg_right h3 hr4]

/-- **K1's (CP4) inputs from the repairs of the changed tail records** and the two price sums
(`lem:tail-prices`(ii)). -/
noncomputable def ofTailRepairData {hW : Target.Weil} {hMR : Target.MovingRoot}
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
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
    {hFour : Target.FourCycle} {A : PaperAnalyticInputs PaperNumbers.paperCell}
    (clique : ∀ q : PrefixCoord, DeletionInputs
      ((v2Reference bOf hW (specF hW A) (hCF hW hMR hFour)).μ₀ (.inl q))
      (paperPrefixAccepted bOf (.inl q)) MainAnchor.paperQueries)
    (blk : ∀ b : Blk, SpecData hW (paperIn PaperNumbers.paperCell) (specF hW A b))
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

end Sarkozy.TailPrices
