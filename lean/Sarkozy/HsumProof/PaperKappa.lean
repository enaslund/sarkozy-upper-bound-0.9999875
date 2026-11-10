module

public import Sarkozy.HsumProof.Middle
public import Sarkozy.HsumProof.PaperKappaData

@[expose] public section

/-!
# The paper's middle constants `κ` and the middle part of `hsum` at them (HS)

`paperKappa i = (s_F, a_F, ℓ_t, s_E, a_E)` of piece `i`, as in `lem:middle-comparison-prices`:
* `s_F`, `a_F`, `ℓ_t` of `eq:signed-constants` (`prop:signed-bounds`);
* `s_E(X)`, `a_E(X)` of `lem:record:exact-marginal-e`(ii);

all at the piece start `X`, `q = 1/X`, `r = 1/⌊√X⌋`, `t = 127/500` (`MainFinal2.tPaper`). The
numbers are the upper endpoints of `cert:signed-local`'s outward interval evaluation (the
research functions `sharp_bounds`, `e_bounds` of `low_domain.py`), rounded up to `10⁻⁹`
(`PaperKappaData.kappaTab`). At `Q₃` they are the values the certificate prints:
`s_F < 11.166062`, `a_F < 4.7973987`, `ℓ_t < 1.2731978`, `s_E < 5.4072·10⁻⁴`, `a_E < 1.0000003`.
That they bound the paper's constants is the certificate's claim (research code), not a Lean
theorem.

**RG's rebase (7 November 2026).** The table is now RB's loosened `kappaTab′`
(`PaperKappaData`): `ℓ_t`, `s_E`, `a_E` are the values above times `1.01`, and `s_F`, `a_F` are
raised to about `1811.8`, `1810.8` (the fold constants at the component constant `c₊ = 38`). Every
entry is at least the paper's, so `paperKappa` still bounds the paper's constants (by the same
certificate), with room; the name is kept.

* `kappaTab_starts`: the table's piece starts are Lean's `pieceStart`;
* `paperKappa_nonneg`, `paperKappa_bounds` (`s_E + a_E + ℓ_t ≤ 23/10`, `s_F + a_F ≤ 3700`);
* **`middlePart_paperKappa`**: `middlePart paperKappa ≤ 0.8349`, the middle budget at `a_G` (the
  value is `0.8348806`; RG), so E3's `hsum_of_budget` closes `hsum` at `κ = paperKappa` together
  with `upperPart_le`: **`hsum_paperKappa`**.
-/

open Finset

namespace Sarkozy.HsumProof

open Sarkozy.PartV Sarkozy.MainFinal Sarkozy.NumericalFields
open Sarkozy.TargetLedger (targetDecay targetLedger)
open Sarkozy.AnalyticCells (f1c2 f1c3)
open PaperKappaData (kappaTab)

/-- The table row of piece `i`. -/
def kappaRow (i : Fin 33) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := kappaTab.getD i.val (0, 0, 0, 0, 0, 0)

/-- The five constants of piece `i`, as rationals. -/
def kSF (i : Fin 33) : ℚ := ((kappaRow i).2.1 : ℚ) / 10 ^ 9
def kAF (i : Fin 33) : ℚ := ((kappaRow i).2.2.1 : ℚ) / 10 ^ 9
def kL (i : Fin 33) : ℚ := ((kappaRow i).2.2.2.1 : ℚ) / 10 ^ 9
def kSE (i : Fin 33) : ℚ := ((kappaRow i).2.2.2.2.1 : ℚ) / 10 ^ 9
def kAE (i : Fin 33) : ℚ := ((kappaRow i).2.2.2.2.2 : ℚ) / 10 ^ 9

/-- **The piece constants** `(s_F, a_F, ℓ_t, s_E, a_E)` of piece `i` (`cert:signed-local`): RB's
loosened table, each entry at least the paper's (RG). -/
noncomputable def paperKappa (i : Fin 33) : MiddleConsts :=
  ⟨(kSF i : ℝ), (kAF i : ℝ), (kL i : ℝ), (kSE i : ℝ), (kAE i : ℝ)⟩

/-- The table is ordered by Lean's piece starts. -/
theorem kappaTab_starts : ∀ i : Fin 33, (kappaRow i).1 = pieceStart i := by decide +kernel

theorem paperKappa_nonneg (i : Fin 33) : KappaNonneg (paperKappa i) := by
  unfold KappaNonneg paperKappa kSF kAF kL kSE kAE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> positivity

theorem kappa_bounds_Q : ∀ i : Fin 33, kSE i + kAE i + kL i ≤ 23 / 10 ∧ kSF i + kAF i ≤ 3700 := by
  decide +kernel

/-- **The paper's constants satisfy the per-piece bounds** of `middlePart_le_of_kappa`. -/
theorem paperKappa_bounds (i : Fin 33) :
    (paperKappa i).sE + (paperKappa i).aE + (paperKappa i).ℓ ≤ 23 / 10 ∧
      (paperKappa i).sF + (paperKappa i).aF ≤ 3700 := by
  obtain ⟨h1, h2⟩ := kappa_bounds_Q i
  constructor
  · have h : ((kSE i + kAE i + kL i : ℚ) : ℝ) ≤ ((23 / 10 : ℚ) : ℝ) := by exact_mod_cast h1
    simpa [paperKappa] using h
  · have h : ((kSF i + kAF i : ℚ) : ℝ) ≤ ((3700 : ℚ) : ℝ) := by exact_mod_cast h2
    simpa [paperKappa] using h

/-- The rational check at the table's constants, against the middle budget `0.8349` (RG, at `a_G`;
the value is `0.8348806`; it was E3's `0.9304` at `a_T`). -/
theorem middle_paper_check :
    ∑ i : Fin 33, (midW2 i * (kSE i + kAE i + kL i) + midW3 i * (kSF i + kAF i) + midFix i) ≤
      8349 / 10000 := by
  decide +kernel

/-- **The middle part of `hsum` at the table's constants**: `middlePart paperKappa ≤ 0.8349`. -/
theorem middlePart_paperKappa : middlePart paperKappa ≤ middleBudget := by
  refine (middlePart_le_linear paperKappa).trans ?_
  calc ∑ i : Fin 33, ((midW2 i : ℝ) * ((paperKappa i).sE + (paperKappa i).aE + (paperKappa i).ℓ) +
        (midW3 i : ℝ) * ((paperKappa i).sF + (paperKappa i).aF) + (midFix i : ℝ)) =
      ((∑ i : Fin 33, (midW2 i * (kSE i + kAE i + kL i) + midW3 i * (kSF i + kAF i) +
        midFix i) : ℚ) : ℝ) := by
        push_cast
        rfl
    _ ≤ ((8349 / 10000 : ℚ) : ℝ) := by exact_mod_cast middle_paper_check
    _ = middleBudget := by unfold middleBudget; push_cast; rfl

/-- **`SAParts3.hsum` at the paper's data**: for per-record data `Cs`, `Ca` with the paper's
ledgers and `κ = paperKappa`, the field holds (E3's `hsum_of_budget` with `upperPart_le_budget`
and `middlePart_paperKappa`). -/
theorem hsum_paperKappa (Cs Ca : Fin 310 → UpIdx → ℝ) (hCs : ∀ k i, 0 ≤ Cs k i)
    (hCa : ∀ k i, 0 ≤ Ca k i) (hL : PaperLedgers Cs Ca) :
    12 / 2 ^ 534 + ∑ β, ∑ d ∈ UpperComparison.upperDegrees,
        ((UpperComparison.upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefS d * bandBound targetDecay d β +
          (UpperComparison.upperLedger (UpperRecords.bandWeights β) (Cs β) (Ca β) (hCs β)
            (hCa β)).coefA d * bandBound targetDecay d β) +
      ∑ i : Fin 33, (midK2 paperKappa i * f1c2 i +
        (midK3 paperKappa i + midK4 i * pieceScale i + midK5 i * pieceScale i ^ 2) * f1c3 i) +
        11 / 10 ^ 70 ≤ targetLedger.S + targetLedger.A :=
  hsum_of_budget Cs Ca hCs hCa paperKappa (upperPart_le_budget Cs Ca hCs hCa hL)
    middlePart_paperKappa

end Sarkozy.HsumProof
