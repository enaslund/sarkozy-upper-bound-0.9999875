module

public import Sarkozy.LetterTotals.Totals
public import Sarkozy.UpperRepair.Scaled

@[expose] public section

/-!
# The symmetric upper total, at the paper's ledgers (HX)

HX, 8 November 2026. UR's `band_le_scaled` (HS's `band_le` with ledgers scaled by `c ≥ 1`) bounds
each band's symmetric and skew terms together by `c · roundQ`. Its first steps are per change type:
HS's band checks `bandCheck_all` give `bandBound a_T d β ≤ UBQ a_T β d`, HS's `coefS_le` bounds
W8's symmetric coefficient at the paper's ledgers by `cSQ β d`, and UR's `coefS_scale` gives the
factor `c`. Here they are kept for the symmetric terms only:

* `upperSQ`: the rational number `∑_β ∑_{d=3}^{7} cSQ(β, d) · UBQ(a_T, β, d)`, at the paper's state
  ledgers (`cert:upper-lower-bands`) and HS's per-band upper bounds of the charges;
* **`upperS_le_scaled`**: for record coefficients with `ScaledLedgers c` (`1 ≤ c`),
  `upperS ≤ c · upperSQ`.

No new kernel computation: `upperSQ` is stated, not evaluated (it is the symmetric half of HS's
`bandTot`, whose total is at most `21/1000`; RB's untrusted value of the symmetric half is
`0.011596`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.LetterTotals

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV
open Sarkozy.UpperComparison (upperLedger upperDegrees RecordLedger)
open Sarkozy.NumericalFields (bandBound)
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.HsumProof (cSQ UBQ aT aT_cast bandBound_le_UBQ bandCheck bandCheck_all coefS_le
  changedOf ledS)
open Sarkozy.UpperRepair (ScaledLedgers coefS_scale)

/-- **The symmetric upper total at the paper's ledgers**:
`∑_β ∑_{d=3}^{7} cSQ(β, d) · UBQ(a_T, β, d)` (rational, not evaluated). -/
def upperSQ : ℚ := ∑ β : Fin 310, ∑ d ∈ upperDegrees, cSQ β d * UBQ aT β d

/-- **The symmetric upper total with scaled ledgers**: `upperS ≤ c · upperSQ` (UR's
`band_le_scaled`, symmetric terms only). -/
theorem upperS_le_scaled (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) {c : ℝ} (hc : 1 ≤ c) (hL : ScaledLedgers c Cs Ca) :
    upperS Cs Ca hCs hCa ≤ c * (upperSQ : ℝ) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hterm : ∀ β : Fin 310, ∀ d ∈ upperDegrees,
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)).coefS d *
          bandBound targetDecay d β ≤ c * ((cSQ β d : ℝ) * (UBQ aT β d : ℝ)) := by
    intro β d hd
    have hcb := bandCheck_all β
    simp only [bandCheck, Bool.and_eq_true, decide_eq_true_eq] at hcb
    obtain ⟨⟨hok, hUB0⟩, -⟩ := hcb
    have hLs : ∀ t, ∑ ρ ∈ changedOf t, Cs β ρ / c ≤ (ledS β t : ℝ) := fun t => by
      rw [← Finset.sum_div, div_le_iff₀ hc0, mul_comm]
      exact (hL β t).1
    have hd' : d ∈ Finset.Icc 3 7 := hd
    have hd2 : 2 ≤ d := by
      have := (Finset.mem_Icc.mp hd').1
      omega
    have hb := bandBound_le_UBQ aT β hok hd2
    rw [aT_cast] at hb
    have hU0 : (0 : ℝ) ≤ (UBQ aT β d : ℝ) := by exact_mod_cast hUB0 d hd'
    have hS := coefS_le β (fun ρ => Cs β ρ / c) (fun ρ => Ca β ρ / c)
      (fun i => div_nonneg (hCs β i) hc0.le) (fun i => div_nonneg (hCa β i) hc0.le) hLs hd'
    have hS' := (coefS_scale (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β) hc d).trans
      (mul_le_mul_of_nonneg_left hS hc0.le)
    have hS0 := RecordLedger.coefS_nonneg
      (upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β) (hCa β)) d
    have h1 := (mul_le_mul_of_nonneg_left hb hS0).trans (mul_le_mul_of_nonneg_right hS' hU0)
    calc _ ≤ c * (cSQ β d : ℝ) * (UBQ aT β d : ℝ) := h1
      _ = _ := by ring
  unfold upperS upperSQ
  calc _ ≤ ∑ β : Fin 310, ∑ d ∈ upperDegrees, c * ((cSQ β d : ℝ) * (UBQ aT β d : ℝ)) :=
        sum_le_sum fun β _ => sum_le_sum fun d hd => hterm β d hd
    _ = _ := by
        simp only [Rat.cast_sum, Rat.cast_mul, mul_sum]

end Sarkozy.LetterTotals
