module

public import Sarkozy.PaperNumbers.BinData
public import Sarkozy.PaperNumbers.BandData
public import Sarkozy.BlockSpecPaper.BudgetWitness
public import Sarkozy.PartV.Blocks
public import Sarkozy.Misc.BlockCharge
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# The paper's within-site block rule (`def:record:exact-blocks`(b)–(d), `def:record:upper-bands`(b))

`paper/sections/20_middle_reference.tex`, `def:record:exact-blocks`;
`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`(b), `rem:upper-band-choices`.

B1's block assignment `paperBlockOf cell` (`BlockSpecPaper/Layout.lean`) labels a class-three prime
`p` by `(siteOf p, cell p)`, where `cell` is the within-site rule. This file defines that rule.

**Below `X_Ch = 4 800 162 890`** (`def:record:exact-blocks`(b), (c)): the exact blocks.
* `binEnds` (`BinData.lean`, generated) are the endpoints of the 5668 count bins of `[2²⁴, X_Ch)`;
  the bin integer of `p` is `binU p = ⌈2⁴⁰ log hi⌉` for the bin `[lo, hi)` of `p` (the paper's
  definition; the generator checks that it equals the recorded integer on all 5668 bins);
* `thresholdData` are the 36 threshold points; the 35 parts are the intervals between them;
* `partList k` lists the primes `≡ 3 (mod 4)` of part `k` in increasing order, and the blocks of the
  part are V1's greedy blocks `greedyBlocks binU 𝔲_* (partList k)`;
* the cell value of `p` is `⟨0, ⟨partOf p, greedyIdx p⟩⟩` (`Nat.pair`), where `greedyIdx p` is the
  index of the greedy block containing `p`.

**From `X_Ch`** (`def:record:exact-blocks`(d), `def:record:upper-bands`(b)): fixed-cardinality
cells. A `CellRule` gives the cell index of a prime (`idx`), the cell's upper end `x_{j+1}` (`top`)
and the block cardinality `n_j` (`card`). Inside a cell, the primes `≡ 3 (mod 4)` in increasing
order are grouped into consecutive blocks of `n_j` primes: the cell value of `p` is
`⟨1, ⟨idx p, pos p / n_{idx p}⟩⟩`, where `pos p` is the position of `p` in the increasing list of
the primes `≡ 3 (mod 4)` of its cell `[x_j, x_{j+1})` (`cellPos`; M2's `cellList`), so that the
blocks are M2's `cellBlock`s.
* The middle pieces use `middleRule i`, the geometric cells `x_j = x^{1-j/𝗇} Y^{j/𝗇}` of
  `[x, Y) = [max(X_i, X_Ch), Y_i)` with `𝗇 = ⌈128 log₂(Y/x)⌉` and `n_j = ⌊570/log x_{j+1}⌋`
  (V1's `cellPoint`, `cellCount`, `cellCard`): exactly the paper's definition.
* The upper bands use a family `U : Fin 310 → CellRule` (`paperCellWith U`). By
  `rem:upper-band-choices` the cells and the `n_j` of a band are choices, and any recorded choice
  with `n_j log x_{j+1} ≤ L_band` is valid (`BandRulesValid U`). The default `paperBandRule` is
  `def:record:upper-bands`(b): two geometric cells below `2⁵²`, `128 log₂(Y/X)` cells from `2⁵²`,
  with `n_j = ⌊L_band / log x_{j+1}⌋`, the largest integers the paper allows.
  **The recorded upper `n_j`** (`recordedBandRule`): below `2⁵²` they equal
  `⌊L_band / log x_{j+1}⌋` (checked by `generate_band_runs.py` on all 602 cells of
  `upper_dense_refined.json`), so `paperBandRule` is the recorded rule there; from `2⁵²` they are
  the recorded runs of `upper_v2_price.json` (`BandData.lean`, `farRule`). T1's formal ledger
  prices the far bands on R4's coarser 58 cells instead; `paperCellWith U` covers every valid
  choice.

`paperCell := paperCellWith recordedBandRule`: the default cells below `2⁵²` (which are the
recorded ones) and the recorded runs from `2⁵²` (`farRule`, `BandData.lean`).
-/

open Finset

namespace Sarkozy.PaperNumbers

open Sarkozy.PartV Sarkozy.BlockSpecPaper

/-- The explicit Chebyshev threshold `X_Ch = 4 800 162 890` (`thm:bmor`,
`def:record:exact-blocks`). -/
def XCh : ℕ := 4800162890

theorem Q3_lt_XCh : Q3 < XCh := by norm_num [Q3, XCh]

theorem XCh_lt_P3 : XCh < P3 := by norm_num [P3, XCh]

/-! ## The bins and the bin integers (`def:record:exact-blocks`(c)) -/

/-- The `i`-th bin endpoint. -/
def binE (i : ℕ) : ℕ := binEnds.getD i 0

theorem binEnds_length : binEnds.length = 5669 := by decide +kernel

theorem binE_zero : binE 0 = 2 ^ 24 := by decide +kernel

theorem binE_last : binE 5668 = XCh := by decide +kernel

theorem binEnds_le : binEnds.all (· ≤ XCh) = true := by decide +kernel

theorem binE_le_XCh {i : ℕ} (hi : i < 5669) : binE i ≤ XCh := by
  have hl : i < binEnds.length := by rw [binEnds_length]; exact hi
  have hm : binEnds[i] ∈ binEnds := List.getElem_mem hl
  have h := List.all_eq_true.mp binEnds_le _ hm
  unfold binE
  rw [List.getD_eq_getElem _ _ hl]
  simpa using h

theorem exists_bin {p : ℕ} (h1 : 2 ^ 24 ≤ p) (h2 : p < XCh) :
    ∃ i < 5668, binE i ≤ p ∧ p < binE (i + 1) :=
  exists_interval binE (binE_zero ▸ h1) 5668 (binE_last ▸ h2)

/-- The upper endpoint `hi` of the bin `[lo, hi)` containing `p` (`X_Ch` outside `[2²⁴, X_Ch)`). -/
noncomputable def binHi (p : ℕ) : ℕ :=
  if h : 2 ^ 24 ≤ p ∧ p < XCh then binE ((exists_bin h.1 h.2).choose + 1) else XCh

theorem lt_binHi {p : ℕ} (h1 : 2 ^ 24 ≤ p) (h2 : p < XCh) : p < binHi p := by
  unfold binHi
  simp only [h1, h2, and_self, ↓reduceDIte]
  exact (exists_bin h1 h2).choose_spec.2.2

theorem binHi_le (p : ℕ) : binHi p ≤ XCh := by
  unfold binHi
  split_ifs with h
  · exact binE_le_XCh (by have := (exists_bin h.1 h.2).choose_spec.1; omega)
  · exact le_rfl

theorem binHi_pos (p : ℕ) : 0 < binHi p := by
  unfold binHi
  split_ifs with h
  · have := (exists_bin h.1 h.2).choose_spec.2.2
    have := h.1
    omega
  · norm_num [XCh]

/-- **The bin integer** `𝔲(p) = ⌈2⁴⁰ log hi⌉` of the bin `[lo, hi)` of `p`
(`def:record:exact-blocks`(c)). -/
noncomputable def binU (p : ℕ) : ℕ := ⌈(2 : ℝ) ^ 40 * Real.log (binHi p)⌉₊

theorem log_binHi_le (p : ℕ) : Real.log (binHi p) ≤ 33 := by
  have h0 : (0 : ℝ) < binHi p := by exact_mod_cast binHi_pos p
  have h1 : (binHi p : ℝ) ≤ 2 ^ 33 := by
    have : binHi p ≤ 2 ^ 33 := (binHi_le p).trans (by norm_num [XCh])
    exact_mod_cast this
  have h2 : Real.log (binHi p) ≤ Real.log ((2 : ℝ) ^ 33) := Real.log_le_log h0 h1
  rw [Real.log_pow] at h2
  have h3 := Real.log_two_lt_d9
  push_cast at h2
  linarith

/-- Every bin integer is at most `𝔲_*`. -/
theorem binU_le (p : ℕ) : binU p ≤ integerBudget := by
  unfold binU
  rw [Nat.ceil_le]
  have h := log_binHi_le p
  have h' : (integerBudget : ℝ) = 2 ^ 40 * 570 := by
    unfold integerBudget middleBudget
    push_cast
    ring
  rw [h']
  have : (2 : ℝ) ^ 40 * Real.log (binHi p) ≤ 2 ^ 40 * 33 :=
    mul_le_mul_of_nonneg_left h (by positivity)
  linarith

/-- **`log p < 𝔲(p)/2⁴⁰`** for `2²⁴ ≤ p < X_Ch`. -/
theorem log_lt_binU {p : ℕ} (h1 : 2 ^ 24 ≤ p) (h2 : p < XCh) :
    Real.log p < (binU p : ℝ) / 2 ^ 40 := by
  have hp : (0 : ℝ) < p := by
    have : 0 < p := lt_of_lt_of_le (by norm_num) h1
    exact_mod_cast this
  have hlt : (p : ℝ) < binHi p := by exact_mod_cast lt_binHi h1 h2
  have h3 : Real.log p < Real.log (binHi p) := Real.log_lt_log hp hlt
  have h4 : (2 : ℝ) ^ 40 * Real.log (binHi p) ≤ binU p := Nat.le_ceil _
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-! ## The parts and the greedy exact blocks (`def:record:exact-blocks`(b), (c)) -/

/-- The `k`-th threshold point. -/
def partE (k : ℕ) : ℕ := (thresholdData.map Prod.fst).getD k 0

theorem partE_zero : partE 0 = Q3 := by decide +kernel

theorem partE_last : partE 35 = XCh := by decide +kernel

theorem exists_part {p : ℕ} (h1 : Q3 ≤ p) (h2 : p < XCh) :
    ∃ k < 35, partE k ≤ p ∧ p < partE (k + 1) :=
  exists_interval partE (partE_zero ▸ h1) 35 (partE_last ▸ h2)

/-- The part of `p` (`0` outside `[Q₃, X_Ch)`). -/
noncomputable def partOf (p : ℕ) : ℕ :=
  if h : Q3 ≤ p ∧ p < XCh then (exists_part h.1 h.2).choose else 0

theorem partOf_spec {p : ℕ} (h1 : Q3 ≤ p) (h2 : p < XCh) :
    partE (partOf p) ≤ p ∧ p < partE (partOf p + 1) := by
  unfold partOf
  simp only [h1, h2, and_self, ↓reduceDIte]
  exact (exists_part h1 h2).choose_spec.2

/-- The primes `p ≡ 3 (mod 4)` of the part `[partE k, partE (k+1))`. -/
def partPrimes (k : ℕ) : Finset ℕ :=
  (range (partE (k + 1))).filter fun q => q.Prime ∧ q % 4 = 3 ∧ partE k ≤ q

/-- **The primes `≡ 3 (mod 4)` of part `k` in increasing order** (`def:record:exact-blocks`(c)). -/
noncomputable def partList (k : ℕ) : List ℕ := (partPrimes k).sort (· ≤ ·)

theorem mem_partList {k p : ℕ} :
    p ∈ partList k ↔ p.Prime ∧ p % 4 = 3 ∧ partE k ≤ p ∧ p < partE (k + 1) := by
  unfold partList partPrimes
  rw [Finset.mem_sort, mem_filter, mem_range]
  tauto

theorem partList_nodup (k : ℕ) : (partList k).Nodup := Finset.sort_nodup _ _

/-- **The exact blocks of part `k`**: V1's greedy blocks with the bin integers `𝔲` and the budget
`𝔲_* = 2⁴⁰ · 570` (`def:record:exact-blocks`(c)). -/
noncomputable def greedyOf (k : ℕ) : List (List ℕ) := greedyBlocks binU integerBudget (partList k)

/-- The index of the exact block containing `p` in its part. -/
noncomputable def greedyIdx (p : ℕ) : ℕ := (greedyOf (partOf p)).findIdx fun B => decide (p ∈ B)

theorem greedyIdx_spec {p : ℕ} (h : p ∈ partList (partOf p)) :
    ∃ hlt : greedyIdx p < (greedyOf (partOf p)).length, p ∈ (greedyOf (partOf p))[greedyIdx p] := by
  have hflat : p ∈ (greedyOf (partOf p)).flatten := by
    unfold greedyOf
    rw [greedyBlocks_flatten]
    exact h
  obtain ⟨B, hB, hpB⟩ := List.mem_flatten.mp hflat
  have hlt : greedyIdx p < (greedyOf (partOf p)).length :=
    List.findIdx_lt_length_of_exists ⟨B, hB, by simpa using hpB⟩
  refine ⟨hlt, ?_⟩
  unfold greedyIdx at hlt ⊢
  have := List.findIdx_getElem (w := hlt)
  simpa using this

/-! ## Fixed-cardinality cells -/

/-- **A within-site cell rule**: the cell index of a prime, the ends `x_j`, `x_{j+1}` of cell `j`,
and the block cardinality `n_j` of cell `j`. -/
structure CellRule where
  /-- the cell index of a prime -/
  idx : ℕ → ℕ
  /-- the lower end `x_j` of cell `j` -/
  bot : ℕ → ℝ
  /-- the upper end `x_{j+1}` of cell `j` -/
  top : ℕ → ℝ
  /-- the block cardinality `n_j` of cell `j` -/
  card : ℕ → ℕ

/-- The geometric cell index `⌊𝗇 log(p/x)/log(Y/x)⌋` of `p ∈ [x, Y)`: `x_j ≤ p < x_{j+1}` for
`x_j = x^{1-j/𝗇} Y^{j/𝗇}` (`geoIdx_spec`). -/
noncomputable def geoIdx (x Y : ℝ) (n : ℕ) (p : ℕ) : ℕ :=
  ⌊(n : ℝ) * (Real.log (p / x) / Real.log (Y / x))⌋₊

/-- **The geometric cells of `[x, Y)` with `𝗇` cells and budget `L`**: `x_j = x^{1-j/𝗇} Y^{j/𝗇}`
(V1's `cellPoint`) and `n_j = ⌊L / log x_{j+1}⌋` (V1's `cellCard`). -/
noncomputable def geoRule (x Y : ℝ) (n : ℕ) (L : ℝ) : CellRule where
  idx := geoIdx x Y n
  bot j := cellPoint x Y n j
  top j := cellPoint x Y n (j + 1)
  card j := cellCard L x Y n j

/-- **The cells of a middle piece above `X_Ch`** (`def:record:exact-blocks`(d)):
`[x, Y) = [max(X_i, X_Ch), Y_i)`, `𝗇 = ⌈128 log₂(Y/x)⌉`, `n_j = ⌊570/log x_{j+1}⌋`. -/
noncomputable def middleRule (i : Fin 33) : CellRule :=
  geoRule (max (pieceStart i : ℝ) XCh) (pieceStop i)
    (cellCount (max (pieceStart i : ℝ) XCh) (pieceStop i)) middleBudget

/-- The number of cells of band `k` (`def:record:upper-bands`(b)): `2` below `2⁵²`,
`128 log₂(Y/X)` from `2⁵²`. -/
noncomputable def bandCells (k : Fin 310) : ℕ :=
  if (bandOf k).1 < 2 ^ 52 then 2
  else ⌈128 * Real.logb 2 (((bandOf k).2 : ℝ) / (bandOf k).1)⌉₊

/-- **The default cells of band `k`** (`def:record:upper-bands`(b)): geometric cells of `[X, Y)`,
`bandCells k` of them, with `n_j = ⌊L_band / log x_{j+1}⌋`. -/
noncomputable def paperBandRule (k : Fin 310) : CellRule :=
  geoRule (bandOf k).1 (bandOf k).2 (bandCells k) (UpperRecords.CompletionData.record k).budget

/-- The cell rule of a site: `middleRule` on a piece, `U k` on band `k`. -/
noncomputable def siteRule (U : Fin 310 → CellRule) : Site → CellRule
  | .inl i => middleRule i
  | .inr k => U k

/-- The primes `≡ 3 (mod 4)` of the cell of `p`, in increasing order (M2's `cellList`). -/
noncomputable def cellListOf (U : Fin 310 → CellRule) (p : ℕ) : List ℕ :=
  Misc.cellList ((siteRule U (siteOf p)).bot ((siteRule U (siteOf p)).idx p))
    ((siteRule U (siteOf p)).top ((siteRule U (siteOf p)).idx p))

/-- The position of `p` in the increasing list of the primes `≡ 3 (mod 4)` of its cell. -/
noncomputable def cellPos (U : Fin 310 → CellRule) (p : ℕ) : ℕ := (cellListOf U p).idxOf p

/-- The cardinality `n_j` of the cell of `p`. -/
noncomputable def cellCardOf (U : Fin 310 → CellRule) (p : ℕ) : ℕ :=
  (siteRule U (siteOf p)).card ((siteRule U (siteOf p)).idx p)

/-! ## The within-site rule -/

/-- **The paper's within-site block rule**, with the band cells `U`: `⟨0, ⟨part, greedy block⟩⟩`
below `X_Ch` (`def:record:exact-blocks`(c)), `⟨1, ⟨cell, pos / n_j⟩⟩` from `X_Ch`
(`def:record:exact-blocks`(d), `def:record:upper-bands`(b)). -/
noncomputable def paperCellWith (U : Fin 310 → CellRule) (p : ℕ) : ℕ :=
  if p < XCh then Nat.pair 0 (Nat.pair (partOf p) (greedyIdx p))
  else Nat.pair 1 (Nat.pair ((siteRule U (siteOf p)).idx p) (cellPos U p / cellCardOf U p))

/-- The recorded cardinality of cell `j` from runs `(first, last, n)` (`1` outside the runs). -/
def runCard (runs : List (ℕ × ℕ × ℕ)) (j : ℕ) : ℕ :=
  ((runs.find? fun r => decide (r.1 ≤ j ∧ j ≤ r.2.1)).map fun r => r.2.2).getD 1

/-- **The recorded cells of a band from `2⁵²`** (band `301 + f`, `[2^b, 2^{b'})`): `128 (b' - b)`
geometric cells (`def:record:upper-bands`(b)) with the recorded `n_j` (`farBand`, from
`upper_v2_price.json`). -/
noncomputable def farRule (k : Fin 310) (f : Fin 9) : CellRule where
  idx := geoIdx (bandOf k).1 (bandOf k).2 (128 * ((farBand f).2.1 - (farBand f).1))
  bot j := cellPoint (bandOf k).1 (bandOf k).2 (128 * ((farBand f).2.1 - (farBand f).1)) j
  top j := cellPoint (bandOf k).1 (bandOf k).2 (128 * ((farBand f).2.1 - (farBand f).1)) (j + 1)
  card j := runCard (farBand f).2.2 j

/-- **The recorded band cells** (`def:record:upper-bands`(b)): below `2⁵²` the default
`paperBandRule` (two cells, `n_j = ⌊L_band / log x_{j+1}⌋`; the generator checks that these are the
recorded `n_j` of `upper_dense_refined.json` on all 602 cells), from `2⁵²` the recorded runs
(`farRule`). -/
noncomputable def recordedBandRule (k : Fin 310) : CellRule :=
  if h : 301 ≤ k.val then farRule k ⟨k.val - 301, by omega⟩ else paperBandRule k

/-- **The paper's within-site block rule**, with the recorded band cells (`recordedBandRule`). -/
noncomputable def paperCell : ℕ → ℕ := paperCellWith recordedBandRule

end Sarkozy.PaperNumbers
