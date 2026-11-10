module

public import Sarkozy.TailCorrelations.Tail

@[expose] public section

/-!
# The tail repair prices of `tailRp`, as a polynomial in `r` (input to rebuild the tail ledger)

`27_tail_index.tex`, `eq:tail-polynomials` and `lem:tail-prices`(ii),(iii), with the repair
constants of `tailRp` (`C^ε_ρ ≤ K r`, `K = tailConst(2⁸¹, 2⁸¹)` for every changed record) instead
of the paper's caps `cert:tail-caps`:

* `changed_deg2_weight`, `changed_deg3_weight`: `∑_{changed, deg 2} w_ρ = 10264581/25` and
  `∑_{changed, deg 3} w_ρ = 4824148992/35` (kernel);
* `changed_sum_const`: `∑_{changed} c_ρ K r = K (W₂ r³ + W₃ r⁴)`;
* **`tailRp_sum_π_poly`**: `∑_{changed} π^ε_ρ ≤ Π^{rep}_{TC}(r) := K (W₂ r³ + W₃ r⁴)`, which
  replaces the paper's `Π^{rep}(r) = c^{rep}_3 r³ + c^{rep}_4 r⁴` (`TailPrices.piRep`);
* `piRepTC_le`: `Π^{rep}_{TC}(r) ≤ 2¹⁰² r³` for `0 ≤ r ≤ 2⁻²⁵⁶` (the role of `k_A = 5844549`);
* **`tailRp_price_le`**: `(∑_{changed} π^ε_ρ) q^{2a} ≤ 2¹⁰² q^{-(3/2 - 2a)}` at every tail prime.

The coefficient `2¹⁰²` is large but harmless: the tail sum `∑_{q ≥ 2⁵¹²} q^{-(3/2-2a)}` is below
`2⁻²⁵³` (T2's `Sums`), so the repair part of the tail price is below `2⁻¹⁵¹`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailCorrelations

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.TailPrices Sarkozy.F7Repair
open Sarkozy.ComparisonLawPaper (tailNe)

/-- `W₂ = ∑_{changed, deg 2} w_ρ = 10264581/25` (the 28 records). -/
theorem changed_deg2_weight :
    (∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 2), tailWQ ρ) =
      10264581 / 25 := by
  decide +kernel

/-- `W₃ = ∑_{changed, deg 3} w_ρ = 4824148992/35` (the 64 records). -/
theorem changed_deg3_weight :
    (∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = 3), tailWQ ρ) =
      4824148992 / 35 := by
  decide +kernel

/-- **`∑_{changed} c_ρ K r = K (W₂ r³ + W₃ r⁴)`** for a constant `K`. -/
theorem changed_sum_const (K r : ℝ) :
    ∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed),
      upCoeff tailWeights r ρ * K * r =
        K * (10264581 / 25 * r ^ 3 + 4824148992 / 35 * r ^ 4) := by
  have hmaps : ∀ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed),
      upperDeg ρ ∈ ({2, 3} : Finset ℕ) := by
    intro ρ hρ
    rcases (upperFate_degrees ρ).1 (mem_filter.mp hρ).2 with h | h <;> simp [h]
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ d, ∑ ρ ∈ (univ.filter (fun ρ : UpIdx => upperFate ρ = .changed)).filter
      (fun ρ => upperDeg ρ = d), upCoeff tailWeights r ρ * K * r =
        (((∑ ρ ∈ univ.filter (fun ρ : UpIdx => upperFate ρ = .changed ∧ upperDeg ρ = d),
          tailWQ ρ : ℚ) : ℝ)) * K * r ^ (d + 1) := by
    intro d
    rw [filter_filter, Rat.cast_sum, sum_mul, sum_mul]
    refine sum_congr rfl fun ρ hρ => ?_
    rw [upCoeff_tail, (mem_filter.mp hρ).2.2]
    ring
  simp only [hfib]
  rw [sum_insert (by decide), sum_singleton, changed_deg2_weight, changed_deg3_weight]
  push_cast
  ring

/-- **The repair polynomial of `tailRp`**: `Π^{rep}_{TC}(r) = K (W₂ r³ + W₃ r⁴)` with
`K = tailConst(2⁸¹, 2⁸¹)`. -/
noncomputable def piRepTC (r : ℝ) : ℝ :=
  tailConst rhoHat rhoHat * (10264581 / 25 * r ^ 3 + 4824148992 / 35 * r ^ 4)

/-- **`∑_{changed} π^ε_ρ ≤ Π^{rep}_{TC}(r)`** at every tail prime (`lem:tail-prices`(ii) with the
constants of `tailRp`). -/
theorem tailRp_sum_π_poly (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q)
    (e : ChangeType) :
    ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), (tailRp hW q h4).π ρ e ≤
      piRepTC (tailR q) :=
  (tailRp_sum_π_le hW q h4 e).trans (le_of_eq (changed_sum_const _ _))

/-- `Π^{rep}_{TC}(r) ≤ 2¹⁰² r³` for `0 ≤ r ≤ 2⁻²⁵⁶`. -/
theorem piRepTC_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2 ^ 256) : piRepTC r ≤ 2 ^ 102 * r ^ 3 := by
  unfold piRepTC
  rw [tailConst_rhoHat]
  have hr3 : 0 ≤ r ^ 3 := pow_nonneg h0 3
  have e : (10264581 / 25 * r ^ 3 + 4824148992 / 35 * r ^ 4 : ℝ) =
      r ^ 3 * (10264581 / 25 + 4824148992 / 35 * r) := by ring
  rw [e]
  have hb : (10264581 / 25 + 4824148992 / 35 * r : ℝ) ≤
      10264581 / 25 + 4824148992 / 35 * (1 / 2 ^ 256) := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 4824148992 / 35)
    linarith
  have hc : ((2 + 1 / 2 ^ 10) * 2 ^ 81 + 1 / 2 ^ 50 : ℝ) *
      (10264581 / 25 + 4824148992 / 35 * (1 / 2 ^ 256)) ≤ 2 ^ 102 := by norm_num
  have hK : (0 : ℝ) ≤ (2 + 1 / 2 ^ 10) * 2 ^ 81 + 1 / 2 ^ 50 := by norm_num
  calc ((2 + 1 / 2 ^ 10) * 2 ^ 81 + 1 / 2 ^ 50 : ℝ) * (r ^ 3 * (10264581 / 25 + 4824148992 / 35 * r))
      = r ^ 3 * (((2 + 1 / 2 ^ 10) * 2 ^ 81 + 1 / 2 ^ 50) *
          (10264581 / 25 + 4824148992 / 35 * r)) := by ring
    _ ≤ r ^ 3 * 2 ^ 102 :=
        mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hb hK).trans hc) hr3
    _ = 2 ^ 102 * r ^ 3 := by ring

/-- **The per-prime repair price of `tailRp`** (`lem:tail-prices`(iii), repair part):
`(∑_{changed} π^ε_ρ) q^{2a} ≤ 2¹⁰² q^{-(3/2 - 2a)}` at every tail prime `q ≥ P₄`. -/
theorem tailRp_price_le (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (a : ℝ)
    (e : ChangeType) :
    (∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), (tailRp hW q h4).π ρ e) *
        (q : ℝ) ^ (2 * a) ≤ 2 ^ 102 * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) :=
  price_le_of_poly h4 a piRepTC (fun _ h0 h1 => piRepTC_le h0 h1) (tailRp_sum_π_poly hW q h4 e)

end Sarkozy.TailCorrelations
