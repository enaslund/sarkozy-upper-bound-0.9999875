module

public import Sarkozy.F7Repair.TailOneWay

@[expose] public section

/-!
# The tail repairs: degree three unconditionally, degree two from the correlation bounds

A changed two-layer record `ρ` of degree `d ∈ {2, 3}` has the coefficient `c_ρ = w_ρ r^d`
(`upCoeff`), and its price at the prime `q` is `P_μ(r)⁻¹ c_ρ C^ε_ρ` (T2's `TailRepairs.π`).

* For the `64` records of degree three, the replacement `λ_q(G^new)` with `C = 3`
  (`crudeRepair`, proved from H1 alone) has price `≤ 3 w_ρ r³`, of order `q^{-3/2}`: summable.
* For the `28` records of degree two, an `O(1)` constant would give price `≍ q^{-1}`, which is not
  summable (D1's drop study); they use the (F7) repair `TailCorr.toRepair` with
  `C ≤ tailConst · r`, from the correlation bounds (*hypotheses*).

* `card_changed_deg`: `28` changed records of degree two, `64` of degree three (kernel count);
* **`hybridRepairs`**: K2's field 10 with only the `28` degree-two records conditional;
* **`hybridBound`**, **`hybrid_C_le`**: the constants;
* **`hybrid_sum_π_le`**: `∑_{changed} π^ε_ρ ≤ ∑_{changed} c_ρ · (tailConst · r if deg 2, else 3)`,
  the input to regenerate the tail ledger.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.TailPrices

/-- **`28` changed records have degree two and `64` degree three** (kernel count). -/
theorem card_changed_deg :
    (univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 2)).card = 28 ∧
      (univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 3)).card = 64 := by
  decide +kernel

/-- The correlation inputs of the degree-two changed records at every tail prime. -/
abbrev TailCorr2 (hW : Target.Weil) (ρh ρoh : UpIdx → ℝ) : Type :=
  ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) t φ (_ : upperFate (true, ⟨t, φ⟩) = .changed)
    (_ : upperDeg (true, ⟨t, φ⟩) = 2),
    TailCorr hW h4 (ComparisonLawPaper.tailNe hW h4) t φ (ρh (true, ⟨t, φ⟩)) (ρoh (true, ⟨t, φ⟩))

/-- **K2's field 10, degree three unconditional**: the (F7) repair for the degree-two changed
records, the replacement `λ_q(G^new)` with `C = 3` for the others. -/
noncomputable def hybridRepairs (hW : Target.Weil) (ρh ρoh : UpIdx → ℝ) (Tc : TailCorr2 hW ρh ρoh) :
    ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (ComparisonLawPaper.tailNe hW h4) :=
  fun q _ h4 t φ h =>
    if h2 : upperDeg (true, ⟨t, φ⟩) = 2 then (Tc q h4 t φ h h2).toRepair
    else crudeRepair hW h4 _ t φ

/-- The bound of the repair constants: `tailConst · r` in degree two, `3` otherwise. -/
noncomputable def hybridBound (ρh ρoh : UpIdx → ℝ) (r : ℝ) (ρ : UpIdx) : ℝ :=
  if upperDeg ρ = 2 then tailConst (ρh ρ) (ρoh ρ) * r else crudeC

theorem hybrid_C_le (hW : Target.Weil) (ρh ρoh : UpIdx → ℝ) (Tc : TailCorr2 hW ρh ρoh) (q : ℕ)
    [Fact q.Prime] (h4 : P4 ≤ q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    (hybridRepairs hW ρh ρoh Tc q h4 t φ h).C e ≤ hybridBound ρh ρoh (tailR q) (true, ⟨t, φ⟩) := by
  unfold hybridRepairs hybridBound
  by_cases h2 : upperDeg (true, ⟨t, φ⟩) = 2
  · simp only [h2, ↓reduceDIte, ↓reduceIte]
    exact (Tc q h4 t φ h h2).C_le e
  · simp only [h2, ↓reduceDIte, ↓reduceIte]
    exact le_of_eq (crudeRepair_C hW h4 _ t φ e)

/-- **The tail repair prices**: `∑_{changed} π^ε_ρ ≤ ∑_{changed} c_ρ · hybridBound ρ`. -/
theorem hybrid_sum_π_le (hW : Target.Weil) (ρh ρoh : UpIdx → ℝ) (Tc : TailCorr2 hW ρh ρoh)
    (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (e : ChangeType) :
    ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), (hybridRepairs hW ρh ρoh Tc q h4).π ρ e ≤
      ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed),
        upCoeff tailWeights (tailR q) ρ * hybridBound ρh ρoh (tailR q) ρ := by
  have hr : 0 < tailR q := tailR_pos q
  have h := (hybridRepairs hW ρh ρoh Tc q h4).sum_π_le
    (fun ρ => hybridBound ρh ρoh (tailR q) ρ / tailR q) e (fun t φ h => by
      rw [div_mul_cancel₀ _ hr.ne']
      exact hybrid_C_le hW ρh ρoh Tc q h4 t φ h e)
  refine h.trans (le_of_eq (sum_congr rfl fun ρ _ => ?_))
  rw [mul_assoc, div_mul_cancel₀ _ hr.ne']

end Sarkozy.F7Repair
