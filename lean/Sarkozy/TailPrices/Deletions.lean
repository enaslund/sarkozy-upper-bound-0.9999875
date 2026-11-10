module

public import Sarkozy.TailPrices.Assembly

@[expose] public section

/-!
# The deleted records of the tail atom (`eq:tail-polynomials`, `Π^{del}`)

`paper/sections/27_tail_index.tex`, `eq:tail-polynomials`: `Π^{del}(r) = ∑_{d=3}^7 c^{del}_d r^d`
with `c^{del}_3 = 81606792/25` and `c^{del}_d = c_d` for `d ≥ 4`. With W8's fate `upperFate`
(edge acceptance of `𝓔₆`) at the tail weights, the deleted records have overall degree three to
seven (W8's `upperFate_degrees`), and their weights per degree are computed exactly by the kernel:

* `delW_3`: degree three, `66419592/25` (`≤ c^{del}_3 = 81606792/25`: the paper deletes, at the
  twelve queries, a superset of these records);
* `delW_4`–`delW_7`: degrees four to seven, `c_4, …, c_7` of `def:tail-law` (every record of degree
  at least four is deleted).

**`deleted_le_piDel`**: `∑_{deleted} c^μ_ρ/P_μ(r) ≤ Π^{del}(r)` for `r ≥ 0`: the field `del` of
`TailRecordPrices` is *proved*. `TailRecordPrices.ofRep`: `TailRecordPrices` from the two analytic
bounds on the changed records.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

open Sarkozy.PartV Sarkozy.UpperComparison

/-- The weights of the tail datum as rationals: `w_𝔱` (two-layer), `v_𝔱` (folded). -/
def tailWQ : UpIdx → ℚ
  | (true, ⟨t, _⟩) => tailW t.1 t.2
  | (false, ⟨t, _⟩) => tailV t.1 t.2

theorem upCoeff_tail (r : ℝ) (ρ : UpIdx) :
    upCoeff tailWeights r ρ = (tailWQ ρ : ℝ) * r ^ upperDeg ρ := by
  rcases ρ with ⟨b, t, φ⟩
  cases b <;> rfl

/-- The total weight of the deleted records of overall degree `d`. -/
def delW (d : ℕ) : ℚ :=
  ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .deleted ∧ upperDeg ρ = d), tailWQ ρ

theorem delW_3 : delW 3 = 66419592 / 25 := by unfold delW; decide +kernel

theorem delW_4 : delW 4 = 50638290432 / 5 := by unfold delW; decide +kernel

theorem delW_5 : delW 5 = 621170191872 / 5 := by unfold delW; decide +kernel

theorem delW_6 : delW 6 = 1877429977088 / 7 := by unfold delW; decide +kernel

theorem delW_7 : delW 7 = 970455252992 / 7 := by unfold delW; decide +kernel

theorem deleted_deg (ρ : UpIdx) (h : upperFate ρ = .deleted) : upperDeg ρ ∈ Icc 3 7 :=
  mem_Icc.mpr ((upperFate_degrees ρ).2 h)

/-- **The deleted weight of the tail atom by degree**. -/
theorem deleted_sum (r : ℝ) :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .deleted), upCoeff tailWeights r ρ =
      (delW 3 : ℝ) * r ^ 3 + (delW 4 : ℝ) * r ^ 4 + (delW 5 : ℝ) * r ^ 5 +
        (delW 6 : ℝ) * r ^ 6 + (delW 7 : ℝ) * r ^ 7 := by
  rw [← sum_fiberwise_of_maps_to (g := upperDeg) (t := Icc 3 7)
    (fun ρ hρ => deleted_deg ρ (mem_filter.mp hρ).2)]
  have hfib : ∀ d, ∑ ρ ∈ (univ.filter (fun ρ : UpIdx => upperFate ρ = .deleted)).filter
      (fun ρ => upperDeg ρ = d), upCoeff tailWeights r ρ = (delW d : ℝ) * r ^ d := by
    intro d
    rw [filter_filter]
    have h1 : ∀ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .deleted ∧ upperDeg ρ = d),
        upCoeff tailWeights r ρ = (tailWQ ρ : ℝ) * r ^ d := by
      intro ρ hρ
      rw [upCoeff_tail, (mem_filter.mp hρ).2.2]
    rw [sum_congr rfl h1, ← sum_mul]
    unfold delW
    push_cast
    rfl
  simp only [hfib]
  rw [show (Icc 3 7 : Finset ℕ) = {3, 4, 5, 6, 7} by decide]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  ring

/-- **The deleted records of the tail atom cost at most `Π^{del}(r)`** (`eq:tail-polynomials`). -/
theorem deleted_le_piDel {r : ℝ} (hr : 0 ≤ r) :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .deleted),
      upCoeff tailWeights r ρ / upPoly tailWeights r ≤ piDel r := by
  have hP := one_le_upPoly tailWeights hr
  have h3 := pow_nonneg hr 3
  calc ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .deleted),
        upCoeff tailWeights r ρ / upPoly tailWeights r ≤
      ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .deleted), upCoeff tailWeights r ρ :=
        sum_le_sum fun ρ _ => div_le_self (upCoeff_nonneg _ hr ρ) hP
    _ = (delW 3 : ℝ) * r ^ 3 + (delW 4 : ℝ) * r ^ 4 + (delW 5 : ℝ) * r ^ 5 +
        (delW 6 : ℝ) * r ^ 6 + (delW 7 : ℝ) * r ^ 7 := deleted_sum r
    _ ≤ piDel r := by
        rw [delW_3, delW_4, delW_5, delW_6, delW_7]
        unfold piDel cDel3 cDel4 cDel5 cDel6 cDel7
        push_cast
        linarith

/-- **`TailRecordPrices` from the bounds on the changed records** (`lem:tail-prices`(ii),
`cert:tail-caps`): the deleted part is `deleted_le_piDel`. -/
theorem TailRecordPrices.ofRep {p : ℕ} [Fact p.Prime] {hne : TailNonempty p}
    {R : TailRecordInputs p hne}
    (hs : ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), R.π ρ .sym ≤ piRep (tailR p))
    (ha : ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), R.π ρ .skew ≤ piRep (tailR p)) :
    TailRecordPrices R :=
  ⟨hs, ha, deleted_le_piDel (tailR_nonneg p)⟩

end Sarkozy.TailPrices
