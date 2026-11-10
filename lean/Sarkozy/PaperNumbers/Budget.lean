module

public import Sarkozy.PaperNumbers.Cell

@[expose] public section

/-!
# The log budget of the paper's blocks (`lem:record:local-domain`(ii), `def:record:upper-bands`(b))

**`paperCell_budget : PaperBudget paperCell`**, and more generally
**`paperCellWith_budget : BandRulesValid U → PaperBudget (paperCellWith U)`**: every block of a
middle piece has `∑ log p ≤ 570`, every block of band `k` has `∑ log p ≤ L_band(k)`. This is the
proof of `lem:record:local-domain`(ii) for the paper's partition:
* an exact block (`def:record:exact-blocks`(c)) lies in one greedy block of its part, and
  `∑ log p < ∑ 𝔲(p)/2⁴⁰ ≤ 𝔲_*/2⁴⁰ = 570` (V1's `greedy_log_budget`, with `log p < 𝔲(p)/2⁴⁰` from
  `𝔲(p) = ⌈2⁴⁰ log hi⌉`, `p < hi`);
* a block of a cell (`def:record:exact-blocks`(d), `def:record:upper-bands`(b)) has at most `n_j`
  primes, all below `x_{j+1}`, and `n_j log x_{j+1} ≤ L` (`geoRule_valid` for the geometric cells).

`BandRulesValid U` is the condition of `def:record:upper-bands`(b) / `rem:upper-band-choices` on
recorded band cells: every prime of the band lies below the top of its cell, and `1 ≤ n_j`,
`n_j log x_{j+1} ≤ L_band`. `paperBandRule_valid` proves it for the default cells.
-/

open Finset

namespace Sarkozy.PaperNumbers

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper

/-! ## Geometric cells -/

/-- **`x_j ≤ p < x_{j+1}`, upper half, and `x_{j+1} ≤ Y`** for the geometric cell index
`j = ⌊𝗇 log(p/x)/log(Y/x)⌋` of `p ∈ [x, Y)`. -/
theorem geoIdx_spec {x Y : ℝ} {n : ℕ} (hn : 1 ≤ n) (hx : 0 < x) (hxY : x < Y) {p : ℕ}
    (hxp : x ≤ p) (hpY : (p : ℝ) < Y) :
    (p : ℝ) < cellPoint x Y n (geoIdx x Y n p + 1) ∧
      cellPoint x Y n (geoIdx x Y n p + 1) ≤ Y ∧ cellPoint x Y n (geoIdx x Y n p) ≤ p ∧
      geoIdx x Y n p < n := by
  have hY : 0 < Y := hx.trans hxY
  have hp : (0 : ℝ) < p := hx.trans_le hxp
  have hℓpos : 0 < Real.log (Y / x) := Real.log_pos ((one_lt_div hx).mpr hxY)
  have hℓ : Real.log (Y / x) = Real.log Y - Real.log x := Real.log_div hY.ne' hx.ne'
  have hpx : Real.log (p / x) = Real.log p - Real.log x := Real.log_div hp.ne' hx.ne'
  have ht0 : 0 ≤ Real.log (p / x) / Real.log (Y / x) :=
    div_nonneg (Real.log_nonneg ((one_le_div hx).mpr hxp)) hℓpos.le
  have ht1 : Real.log (p / x) / Real.log (Y / x) < 1 := by
    rw [div_lt_one hℓpos]
    exact Real.log_lt_log (div_pos hp hx) ((div_lt_div_iff_of_pos_right hx).mpr hpY)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (n : ℝ) * (Real.log (p / x) / Real.log (Y / x)) < geoIdx x Y n p + 1 :=
    Nat.lt_floor_add_one _
  have hjn : geoIdx x Y n p < n := by
    unfold geoIdx
    rw [Nat.floor_lt (mul_nonneg hn'.le ht0)]
    calc (n : ℝ) * (Real.log (p / x) / Real.log (Y / x)) < n * 1 :=
          mul_lt_mul_of_pos_left ht1 hn'
      _ = n := mul_one _
  have hcp : cellPoint x Y n (geoIdx x Y n p + 1) =
      Real.exp (Real.log x + (((geoIdx x Y n p + 1 : ℕ) : ℝ) / n) * (Real.log Y - Real.log x)) := by
    unfold cellPoint
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hY, ← Real.exp_add]
    congr 1
    ring
  have hts : Real.log (p / x) / Real.log (Y / x) < ((geoIdx x Y n p + 1 : ℕ) : ℝ) / n := by
    rw [lt_div_iff₀ hn']
    push_cast
    linarith
  have hs1 : ((geoIdx x Y n p + 1 : ℕ) : ℝ) / n ≤ 1 := by
    rw [div_le_one hn']
    exact_mod_cast hjn
  have hpe : Real.log p = Real.log x +
      (Real.log (p / x) / Real.log (Y / x)) * (Real.log Y - Real.log x) := by
    rw [← hℓ, div_mul_cancel₀ _ hℓpos.ne', hpx]
    ring
  have hℓ' : 0 < Real.log Y - Real.log x := hℓ ▸ hℓpos
  have hfl : ((geoIdx x Y n p : ℕ) : ℝ) / n ≤ Real.log (p / x) / Real.log (Y / x) := by
    rw [div_le_iff₀ hn', mul_comm]
    exact Nat.floor_le (mul_nonneg hn'.le ht0)
  have hcp0 : cellPoint x Y n (geoIdx x Y n p) =
      Real.exp (Real.log x + (((geoIdx x Y n p : ℕ) : ℝ) / n) * (Real.log Y - Real.log x)) := by
    unfold cellPoint
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hY, ← Real.exp_add]
    congr 1
    ring
  refine ⟨?_, ?_, ?_, hjn⟩
  · rw [hcp, ← Real.exp_log hp, hpe]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  · rw [hcp]
    calc Real.exp (Real.log x + (((geoIdx x Y n p + 1 : ℕ) : ℝ) / n) * (Real.log Y - Real.log x))
        ≤ Real.exp (Real.log x + 1 * (Real.log Y - Real.log x)) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = Y := by
          rw [show Real.log x + 1 * (Real.log Y - Real.log x) = Real.log Y by ring]
          exact Real.exp_log hY
  · rw [hcp0, ← Real.exp_log hp, hpe]
    exact Real.exp_le_exp.mpr (by nlinarith)

/-- **The cell conditions** of a rule `R` at a prime `p` with budget `L`: `x_j ≤ p < x_{j+1}` for
the cell `j` of `p`, `1 ≤ n_j` and `n_j log x_{j+1} ≤ L`. -/
def CellOK (R : CellRule) (L : ℝ) (p : ℕ) : Prop :=
  R.bot (R.idx p) ≤ p ∧ (p : ℝ) < R.top (R.idx p) ∧ 1 ≤ R.card (R.idx p) ∧
    (R.card (R.idx p) : ℝ) * Real.log (R.top (R.idx p)) ≤ L

/-- **The geometric cells satisfy the cell conditions**: `p < x_{j+1}`, `1 ≤ n_j` and
`n_j log x_{j+1} ≤ L` for `n_j = ⌊L / log x_{j+1}⌋`, when `log Y ≤ L`. -/
theorem geoRule_valid {x Y L : ℝ} {n : ℕ} (hn : 1 ≤ n) (hx : 1 ≤ x) (hxY : x < Y)
    (hYL : Real.log Y ≤ L) {p : ℕ} (hxp : x ≤ p) (hpY : (p : ℝ) < Y) :
    CellOK (geoRule x Y n L) L p := by
  obtain ⟨h1, h2, h0, -⟩ := geoIdx_spec hn (by linarith) hxY hxp hpY
  have hc1 : 1 < cellPoint x Y n (geoIdx x Y n p + 1) := lt_of_le_of_lt (hx.trans hxp) h1
  have hlc : 0 < Real.log (cellPoint x Y n (geoIdx x Y n p + 1)) := Real.log_pos hc1
  have hlcY : Real.log (cellPoint x Y n (geoIdx x Y n p + 1)) ≤ L :=
    (Real.log_le_log (by linarith) h2).trans hYL
  refine ⟨h0, h1, ?_, ?_⟩
  · change 1 ≤ cellCard L x Y n (geoIdx x Y n p)
    unfold cellCard
    rw [Nat.one_le_floor_iff, one_le_div hlc]
    exact hlcY
  · change (cellCard L x Y n (geoIdx x Y n p) : ℝ) *
      Real.log (cellPoint x Y n (geoIdx x Y n p + 1)) ≤ L
    unfold cellCard
    have hL : 0 ≤ L := hlc.le.trans hlcY
    have := Nat.floor_le (div_nonneg hL hlc.le)
    calc _ ≤ L / Real.log (cellPoint x Y n (geoIdx x Y n p + 1)) *
          Real.log (cellPoint x Y n (geoIdx x Y n p + 1)) :=
          mul_le_mul_of_nonneg_right this hlc.le
      _ = L := div_mul_cancel₀ L hlc.ne'

theorem one_le_cellCount {x Y : ℝ} (hx : 0 < x) (hxY : x < Y) : 1 ≤ cellCount x Y := by
  unfold cellCount
  have : 0 < Real.logb 2 (Y / x) := Real.logb_pos (by norm_num) ((one_lt_div hx).mpr hxY)
  exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))

/-- **The middle cells satisfy the cell conditions** with `L = 570`. -/
theorem middleRule_valid (i : Fin 33) {p : ℕ} (hX : XCh ≤ p) (h1 : pieceStart i ≤ p)
    (h2 : p < pieceStop i) : CellOK (middleRule i) (middleBudget : ℝ) p := by
  have hx1 : (1 : ℝ) ≤ max (pieceStart i : ℝ) XCh :=
    le_max_of_le_right (by norm_num [XCh])
  have hxp : max (pieceStart i : ℝ) XCh ≤ p :=
    max_le (by exact_mod_cast h1) (by exact_mod_cast hX)
  have hpY : (p : ℝ) < pieceStop i := by exact_mod_cast h2
  have hxY : max (pieceStart i : ℝ) XCh < pieceStop i := hxp.trans_lt hpY
  have hYL : Real.log (pieceStop i) ≤ (middleBudget : ℝ) := by
    have := log_siteStop_lt (.inl i)
    have h570 : (355 : ℝ) ≤ middleBudget := by norm_num [middleBudget]
    exact (le_of_lt this).trans h570
  exact geoRule_valid (one_le_cellCount (by linarith) hxY) hx1 hxY hYL hxp hpY

/-- **The condition on recorded band cells** (`def:record:upper-bands`(b),
`rem:upper-band-choices`):
every prime of band `k` lies in its cell `[x_j, x_{j+1})`, and `1 ≤ n_j`,
`n_j log x_{j+1} ≤ L_band(k)`. -/
def BandRulesValid (U : Fin 310 → CellRule) : Prop :=
  ∀ (k : Fin 310) (p : ℕ), (bandOf k).1 ≤ p → p < (bandOf k).2 →
    CellOK (U k) (UpperRecords.CompletionData.record k).budget p

/-- **The default band cells satisfy the condition** (two cells below `2⁵²`, `128 log₂(Y/X)` from
`2⁵²`, `n_j = ⌊L_band / log x_{j+1}⌋`). -/
theorem paperBandRule_valid : BandRulesValid paperBandRule := by
  intro k p h1 h2
  have hx1 : (1 : ℝ) ≤ (bandOf k).1 := by
    have := P3_le_bandStart k
    have h' : 1 ≤ (bandOf k).1 := le_trans (by norm_num [P3]) this
    exact_mod_cast h'
  have hxp : ((bandOf k).1 : ℝ) ≤ p := by exact_mod_cast h1
  have hpY : (p : ℝ) < (bandOf k).2 := by exact_mod_cast h2
  have hxY : ((bandOf k).1 : ℝ) < (bandOf k).2 := hxp.trans_lt hpY
  have hYL : Real.log (bandOf k).2 ≤ ((UpperRecords.CompletionData.record k).budget : ℝ) := by
    have h3 := log_siteStop_lt (.inr k)
    have h4 := budget_ge_550 (.inr k)
    exact (le_of_lt h3).trans (le_trans (by norm_num) h4)
  have hn : 1 ≤ bandCells k := by
    unfold bandCells
    split_ifs
    · norm_num
    · exact one_le_cellCount (by linarith) hxY
  exact geoRule_valid hn hx1 hxY hYL hxp hpY

/-- The cell conditions at the site of a prime `X_Ch ≤ p < P₄`, with the site's budget. -/
theorem siteRule_valid {U : Fin 310 → CellRule} (hU : BandRulesValid U) {p : ℕ} (hQ : Q3 ≤ p)
    (hP : p < P4) (hX : XCh ≤ p) :
    CellOK (siteRule U (siteOf p)) (siteBudget (siteOf p) : ℝ) p := by
  have hm := siteOf_mem hQ hP
  rcases hs : siteOf p with i | k
  · rw [hs] at hm
    exact middleRule_valid i hX hm.1 hm.2
  · rw [hs] at hm
    exact hU k p hm.1 hm.2

/-! ## Positions in a cell -/

/-- A finite family with injective ranks of a common quotient `m` by `n ≥ 1` has at most `n`
members. -/
theorem card_le_of_rank {ι : Type} [Fintype ι] {n m : ℕ} (hn : 1 ≤ n) (r : ι → ℕ)
    (hr : Function.Injective r) (hdiv : ∀ i, r i / n = m) : Fintype.card ι ≤ n := by
  let f : ι → Fin n := fun i => ⟨r i % n, Nat.mod_lt _ hn⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hmod : r x % n = r y % n := congrArg Fin.val hxy
    apply hr
    rw [← Nat.div_add_mod (r x) n, ← Nat.div_add_mod (r y) n, hdiv x, hdiv y, hmod]
  simpa using Fintype.card_le_of_injective f hf

/-! ## The budget -/

theorem siteOf_lt_P3 {p : ℕ} (h1 : Q3 ≤ p) (h2 : p < P3) : ∃ i, siteOf p = .inl i := by
  unfold siteOf
  simp only [h1, h2, and_self, ↓reduceDIte]
  exact ⟨_, rfl⟩

theorem partE_bounds : ∀ k < 36, Q3 ≤ partE k ∧ partE k ≤ XCh := by decide +kernel

theorem partOf_lt {p : ℕ} (h1 : Q3 ≤ p) (h2 : p < XCh) : partOf p < 35 := by
  unfold partOf
  simp only [h1, h2, and_self, ↓reduceDIte]
  exact (exists_part h1 h2).choose_spec.1

theorem mem_partList_partOf {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) (h1 : Q3 ≤ p)
    (h2 : p < XCh) : p ∈ partList (partOf p) :=
  mem_partList.mpr ⟨hp, h3, (partOf_spec h1 h2).1, (partOf_spec h1 h2).2⟩

theorem mem_greedy_getD {p : ℕ} (h : p ∈ partList (partOf p)) :
    p ∈ (greedyOf (partOf p)).getD (greedyIdx p) [] := by
  obtain ⟨hlt, hm⟩ := greedyIdx_spec h
  rw [List.getD_eq_getElem _ _ hlt]
  exact hm

/-- `log p < 𝔲(p)/2⁴⁰` on a part. -/
theorem log_lt_binU_part {k : ℕ} (hk : k < 35) {q : ℕ} (hq : q ∈ partList k) :
    Real.log q < (binU q : ℝ) / 2 ^ 40 := by
  obtain ⟨-, -, h1, h2⟩ := mem_partList.mp hq
  have hb1 := (partE_bounds k (by omega)).1
  have hb2 := (partE_bounds (k + 1) (by omega)).2
  exact log_lt_binU (le_trans (by norm_num [Q3]) (hb1.trans h1)) (lt_of_lt_of_le h2 hb2)

variable {U : Fin 310 → CellRule}

/-- The coordinates of a block of the paper's rule. -/
abbrev Coord (U : Fin 310 → CellRule) (b : PaperBlock (paperCellWith U)) : Type :=
  {j : PaperJ0 // paperAtomMap (paperBlockOf (paperCellWith U)) j = .inr b}

/-- The facts on the coordinates of a block used below. -/
theorem coord_facts (b : PaperBlock (paperCellWith U)) (j : Coord U b) :
    blockPrimes (paperBlockOf (paperCellWith U)) b j = j.1.1 ∧
      (j.1.1.Prime ∧ j.1.1 % 4 = 3 ∧ Q3 ≤ j.1.1 ∧ j.1.1 < P4) ∧
      b.1 = (siteOf j.1.1, paperCellWith U j.1.1) := by
  have hP : blockPrimes (paperBlockOf (paperCellWith U)) b j = j.1.1 :=
    paperM0_cls3 (blockOf_of_coord j).1
  have h := blockPrimes_mod_ge b j
  rw [hP] at h
  exact ⟨hP, ⟨paperJ0_prime j.1, h.1, h.2, paperJ0_lt_P4 j.1⟩, (blockOf_of_coord j).2⟩

/-- **The kind of an exact block**: all its coordinates lie below `X_Ch`, in the same part and the
same greedy block. -/
theorem coord_exact {b : PaperBlock (paperCellWith U)} {j0 : Coord U b} (hX0 : j0.1.1 < XCh)
    (j : Coord U b) :
    j.1.1 < XCh ∧ partOf j.1.1 = partOf j0.1.1 ∧ greedyIdx j.1.1 = greedyIdx j0.1.1 := by
  have h := ((coord_facts b j).2.2.symm.trans (coord_facts b j0).2.2)
  have h' : paperCellWith U j.1.1 = paperCellWith U j0.1.1 := (Prod.ext_iff.mp h).2
  unfold paperCellWith at h'
  simp only [hX0, ↓reduceIte] at h'
  by_cases hXj : j.1.1 < XCh
  · simp only [hXj, ↓reduceIte] at h'
    obtain ⟨-, h''⟩ := Nat.pair_eq_pair.mp h'
    exact ⟨hXj, (Nat.pair_eq_pair.mp h'').1, (Nat.pair_eq_pair.mp h'').2⟩
  · simp only [hXj, ↓reduceIte] at h'
    exact absurd (Nat.pair_eq_pair.mp h').1 (by norm_num)

/-- **The kind of a cell block**: all its coordinates lie from `X_Ch` on, in the same site, the
same cell and the same block of the cell. -/
theorem coord_cell {b : PaperBlock (paperCellWith U)} {j0 : Coord U b} (hX0 : ¬ j0.1.1 < XCh)
    (j : Coord U b) :
    XCh ≤ j.1.1 ∧ siteOf j.1.1 = siteOf j0.1.1 ∧
      (siteRule U (siteOf j0.1.1)).idx j.1.1 = (siteRule U (siteOf j0.1.1)).idx j0.1.1 ∧
      cellPos U j.1.1 / cellCardOf U j.1.1 = cellPos U j0.1.1 / cellCardOf U j0.1.1 := by
  have h := ((coord_facts b j).2.2.symm.trans (coord_facts b j0).2.2)
  have hs : siteOf j.1.1 = siteOf j0.1.1 := (Prod.ext_iff.mp h).1
  have h' : paperCellWith U j.1.1 = paperCellWith U j0.1.1 := (Prod.ext_iff.mp h).2
  unfold paperCellWith at h'
  simp only [hX0, ↓reduceIte] at h'
  by_cases hXj : j.1.1 < XCh
  · simp only [hXj, ↓reduceIte] at h'
    exact absurd (Nat.pair_eq_pair.mp h').1 (by norm_num)
  · simp only [hXj, ↓reduceIte] at h'
    rw [hs] at h'
    obtain ⟨-, h''⟩ := Nat.pair_eq_pair.mp h'
    exact ⟨not_lt.mp hXj, hs, (Nat.pair_eq_pair.mp h'').1, (Nat.pair_eq_pair.mp h'').2⟩

theorem cellListOf_eq {p p' : ℕ} (hs : siteOf p = siteOf p')
    (hi : (siteRule U (siteOf p')).idx p = (siteRule U (siteOf p')).idx p') :
    cellListOf U p = cellListOf U p' := by
  unfold cellListOf
  rw [hs, hi]

theorem cellCardOf_eq {p p' : ℕ} (hs : siteOf p = siteOf p')
    (hi : (siteRule U (siteOf p')).idx p = (siteRule U (siteOf p')).idx p') :
    cellCardOf U p = cellCardOf U p' := by
  unfold cellCardOf
  rw [hs, hi]

theorem mem_cellListOf {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {L : ℝ}
    (hok : CellOK (siteRule U (siteOf p)) L p) : p ∈ cellListOf U p := by
  unfold cellListOf
  rw [Misc.mem_cellList, Misc.mem_cellPrimes]
  exact ⟨hp, h3, hok.1, hok.2.1⟩

/-- **The budget of a block of the paper's rule, at its site's budget.** -/
theorem paperCellWith_sum_le (hU : BandRulesValid U) (b : PaperBlock (paperCellWith U)) :
    ∑ j, Real.log (blockPrimes (paperBlockOf (paperCellWith U)) b j) ≤
      (siteBudget (blockSite b) : ℝ) := by
  obtain ⟨j0⟩ := blockIdx_nonempty b
  have hbs : blockSite b = siteOf j0.1.1 := by
    unfold blockSite
    rw [(coord_facts b j0).2.2]
  have hlog0 : ∀ q : ℕ, q.Prime → 0 ≤ Real.log q := fun q hq =>
    Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
  have hinjP : Function.Injective fun j : Coord U b => j.1.1 :=
    fun x y h => Subtype.ext (Subtype.ext h)
  rw [hbs]
  simp only [fun j => (coord_facts b j).1]
  obtain ⟨hpr0, h30, hQ0, hP0⟩ := (coord_facts b j0).2.1
  by_cases hX0 : j0.1.1 < XCh
  · -- an exact block
    obtain ⟨i, hi⟩ := siteOf_lt_P3 hQ0 (hX0.trans XCh_lt_P3)
    rw [hi]
    set K := partOf j0.1.1
    set B := (greedyOf K).getD (greedyIdx j0.1.1) []
    have hmemB : ∀ j : Coord U b, j.1.1 ∈ B := by
      intro j
      obtain ⟨hpr, h3, hQ, -⟩ := (coord_facts b j).2.1
      obtain ⟨hXj, hK, hm⟩ := coord_exact hX0 j
      have := mem_greedy_getD (mem_partList_partOf hpr h3 hQ hXj)
      rw [hK, hm] at this
      exact this
    have hlen : greedyIdx j0.1.1 < (greedyOf K).length :=
      (greedyIdx_spec (mem_partList_partOf hpr0 h30 hQ0 hX0)).1
    have hBG : B ∈ greedyOf K := by
      change (greedyOf K).getD (greedyIdx j0.1.1) [] ∈ greedyOf K
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    have hnodup : B.Nodup := by
      have hflat : (greedyOf K).flatten.Nodup := by
        change (greedyBlocks binU integerBudget (partList K)).flatten.Nodup
        rw [greedyBlocks_flatten]
        exact partList_nodup K
      exact (List.nodup_flatten.mp hflat).1 B hBG
    have hKlt : K < 35 := partOf_lt hQ0 hX0
    have hbud : (B.map fun q : ℕ => Real.log (q : ℝ)).sum ≤ middleBudget :=
      greedy_log_budget binU binU_le (partList K) (fun q hq => log_lt_binU_part hKlt hq) B hBG
    have hBsub : ∀ q ∈ B, q ∈ partList K := by
      intro q hq
      rw [← greedyBlocks_flatten binU integerBudget (partList K)]
      exact List.mem_flatten.mpr ⟨B, hBG, hq⟩
    calc ∑ j : Coord U b, Real.log (j.1.1 : ℝ)
        = ∑ q ∈ univ.image (fun j : Coord U b => j.1.1), Real.log (q : ℝ) := by
          rw [sum_image fun x _ y _ h => hinjP h]
      _ ≤ ∑ q ∈ B.toFinset, Real.log (q : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro q hq
            obtain ⟨j, -, rfl⟩ := mem_image.mp hq
            exact List.mem_toFinset.mpr (hmemB j)
          · intro q hq _
            exact hlog0 q (mem_partList.mp (hBsub q (List.mem_toFinset.mp hq))).1
      _ = (B.map fun q : ℕ => Real.log (q : ℝ)).sum := List.sum_toFinset _ hnodup
      _ ≤ middleBudget := hbud
      _ = (siteBudget (.inl i) : ℝ) := rfl
  · -- a block of a cell
    have hX0' : XCh ≤ j0.1.1 := not_lt.mp hX0
    have hok0 := siteRule_valid hU hQ0 hP0 hX0'
    obtain ⟨-, htop0, hn1, hnL⟩ := hok0
    set R := siteRule U (siteOf j0.1.1)
    set n := R.card (R.idx j0.1.1)
    set top := R.top (R.idx j0.1.1)
    have hokj : ∀ j : Coord U b, CellOK (siteRule U (siteOf j.1.1))
        (siteBudget (siteOf j.1.1) : ℝ) j.1.1 := fun j =>
      siteRule_valid hU (coord_facts b j).2.1.2.2.1 (coord_facts b j).2.1.2.2.2 (coord_cell hX0 j).1
    have hlist : ∀ j : Coord U b, cellListOf U j.1.1 = cellListOf U j0.1.1 := fun j =>
      cellListOf_eq (coord_cell hX0 j).2.1 (coord_cell hX0 j).2.2.1
    have hmem : ∀ j : Coord U b, j.1.1 ∈ cellListOf U j0.1.1 := fun j => by
      rw [← hlist j]
      exact mem_cellListOf (coord_facts b j).2.1.1 (coord_facts b j).2.1.2.1 (hokj j)
    have hjtop : ∀ j : Coord U b, (j.1.1 : ℝ) < top := by
      intro j
      have := (hokj j).2.1
      rw [(coord_cell hX0 j).2.1, (coord_cell hX0 j).2.2.1] at this
      exact this
    have htop1 : 1 < top := by
      have : (1 : ℝ) < j0.1.1 := by exact_mod_cast hpr0.one_lt
      exact this.trans htop0
    have hltop : 0 < Real.log top := Real.log_pos htop1
    have hcard : Fintype.card (Coord U b) ≤ n := by
      apply card_le_of_rank hn1 (fun j => cellPos U j.1.1)
      · intro x y hxy
        have hxy' : (cellListOf U j0.1.1).idxOf x.1.1 = (cellListOf U j0.1.1).idxOf y.1.1 := by
          have := hxy
          simp only [cellPos] at this
          rw [hlist x, hlist y] at this
          exact this
        exact hinjP ((List.idxOf_inj (hmem x)).mp hxy')
      · intro j
        have := (coord_cell hX0 j).2.2.2
        rw [cellCardOf_eq (coord_cell hX0 j).2.1 (coord_cell hX0 j).2.2.1] at this
        exact this
    calc ∑ j : Coord U b, Real.log (j.1.1 : ℝ)
        ≤ ∑ _j : Coord U b, Real.log top := by
          apply sum_le_sum
          intro j _
          have hpos : (0 : ℝ) < j.1.1 := by exact_mod_cast (coord_facts b j).2.1.1.pos
          exact Real.log_le_log hpos (hjtop j).le
      _ = (Fintype.card (Coord U b) : ℝ) * Real.log top := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ (n : ℝ) * Real.log top :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hltop.le
      _ ≤ (siteBudget (siteOf j0.1.1) : ℝ) := hnL

/-- **`lem:record:local-domain`(ii) for the paper's partition with recorded band cells `U`**:
`PaperBudget (paperCellWith U)` whenever the band cells satisfy `def:record:upper-bands`(b). -/
theorem paperCellWith_budget (hU : BandRulesValid U) : PaperBudget (paperCellWith U) := by
  intro b
  have hsum := paperCellWith_sum_le hU b
  refine ⟨fun i hs => ?_, fun k hs => ?_⟩
  · rw [hs] at hsum
    exact hsum
  · rw [hs] at hsum
    exact hsum

/-! ## The recorded cells of the bands from `2⁵²` -/

/-- The nine far bands are `[2^b, 2^{b'})`, `b < b'`. -/
theorem farBand_spec : ∀ f : Fin 9,
    bandOf ⟨301 + f.val, by omega⟩ = (2 ^ (farBand f).1, 2 ^ (farBand f).2.1) ∧
      (farBand f).1 < (farBand f).2.1 := by decide +kernel

/-- **The recorded runs satisfy `n_j ≥ 1` and `n_j log x_{j+1} ≤ L_band`** at the last cell of
every run, with `log x_{m} = (b + m/128) log 2 < (b + m/128) · 0.6931471808`. -/
theorem farRuns_check : ∀ f : Fin 9, ((farBand f).2.2).all (fun r =>
    decide (1 ≤ r.2.2) &&
      decide ((r.2.2 : ℚ) * (((farBand f).1 : ℚ) + ((r.2.1 + 1 : ℕ) : ℚ) / 128) *
      (6931471808 / 10 ^ 10) ≤
        ((UpperRecords.CompletionData.record ⟨301 + f.val, by omega⟩).budget : ℚ))) = true := by
  decide +kernel

theorem log_cellPoint_pow2 {b b' : ℕ} (hbb : b < b') (m : ℕ) :
    Real.log (cellPoint ((2 : ℝ) ^ b) ((2 : ℝ) ^ b') (128 * (b' - b)) m) =
      ((b : ℝ) + (m : ℝ) / 128) * Real.log 2 := by
  have hJ : ((128 * (b' - b) : ℕ) : ℝ) = 128 * ((b' : ℝ) - b) := by
    rw [Nat.cast_mul, Nat.cast_sub hbb.le]
    norm_num
  have hJ0 : (b' : ℝ) - b ≠ 0 := by
    have : (b : ℝ) < b' := by exact_mod_cast hbb
    linarith
  unfold cellPoint
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
    Real.log_rpow (by positivity), Real.log_pow, Real.log_pow, hJ]
  field_simp
  ring

theorem runCard_spec (runs : List (ℕ × ℕ × ℕ)) (j : ℕ) :
    runCard runs j = 1 ∨ ∃ r ∈ runs, r.1 ≤ j ∧ j ≤ r.2.1 ∧ runCard runs j = r.2.2 := by
  unfold runCard
  cases h : runs.find? (fun r => decide (r.1 ≤ j ∧ j ≤ r.2.1)) with
  | none => left; rfl
  | some r =>
      right
      have hp := List.find?_some h
      simp only [decide_eq_true_eq] at hp
      exact ⟨r, List.mem_of_find?_eq_some h, hp.1, hp.2, rfl⟩

/-- **The recorded far-band cells satisfy the cell conditions.** -/
theorem farRule_valid (k : Fin 310) (f : Fin 9) (hk : k.val = 301 + f.val) (p : ℕ)
    (h1 : (bandOf k).1 ≤ p) (h2 : p < (bandOf k).2) :
    CellOK (farRule k f) (UpperRecords.CompletionData.record k).budget p := by
  have hk' : k = ⟨301 + f.val, by omega⟩ := Fin.ext hk
  obtain ⟨hband, hbb⟩ := farBand_spec f
  rw [← hk'] at hband
  set b := (farBand f).1
  set b' := (farBand f).2.1
  have hX : ((bandOf k).1 : ℝ) = (2 : ℝ) ^ b := by rw [hband]; push_cast; rfl
  have hY : ((bandOf k).2 : ℝ) = (2 : ℝ) ^ b' := by rw [hband]; push_cast; rfl
  have hJ1 : 1 ≤ 128 * (b' - b) := by omega
  have hx1 : (1 : ℝ) ≤ (bandOf k).1 := by rw [hX]; exact one_le_pow₀ (by norm_num)
  have hxp : ((bandOf k).1 : ℝ) ≤ p := by exact_mod_cast h1
  have hpY : (p : ℝ) < (bandOf k).2 := by exact_mod_cast h2
  have hxY : ((bandOf k).1 : ℝ) < (bandOf k).2 := hxp.trans_lt hpY
  obtain ⟨htop, htopY, hbot, hidx⟩ := geoIdx_spec hJ1 (by linarith) hxY hxp hpY
  have hL550 := budget_ge_550 (.inr k)
  have hlogY := log_siteStop_lt (.inr k)
  change (550 : ℝ) ≤ ((UpperRecords.CompletionData.record k).budget : ℝ) at hL550
  change Real.log ((bandOf k).2 : ℝ) < 355 at hlogY
  have htop1 : 1 < cellPoint ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (128 * (b' - b))
      (geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (128 * (b' - b)) p + 1) := by
    have : (1 : ℝ) ≤ p := hx1.trans hxp
    linarith
  refine ⟨hbot, htop, ?_, ?_⟩
  · change 1 ≤ runCard (farBand f).2.2 (geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ)
      (128 * (b' - b)) p)
    rcases runCard_spec (farBand f).2.2 (geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ)
        (128 * (b' - b)) p) with h | ⟨r, hmem, -, -, heq⟩
    · rw [h]
    · rw [heq]
      have hc := List.all_eq_true.mp (farRuns_check f) r hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
  · change (runCard (farBand f).2.2 (geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ)
      (128 * (b' - b)) p) : ℝ) * Real.log (cellPoint ((bandOf k).1 : ℝ)
        ((bandOf k).2 : ℝ) (128 * (b' - b)) (geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ)
          (128 * (b' - b)) p + 1)) ≤ _
    have hlogpos : 0 < Real.log (cellPoint ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (128 * (b' - b))
        (geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (128 * (b' - b)) p + 1)) :=
      Real.log_pos htop1
    rcases runCard_spec (farBand f).2.2 (geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ)
        (128 * (b' - b)) p) with h | ⟨r, hmem, -, hhi, heq⟩
    · rw [h, Nat.cast_one, one_mul]
      have := Real.log_le_log (by linarith) htopY
      linarith
    · rw [heq]
      have hc := List.all_eq_true.mp (farRuns_check f) r hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨-, hcq⟩ := hc
      have hcq' : (((r.2.2 : ℚ) * ((b : ℚ) + ((r.2.1 + 1 : ℕ) : ℚ) / 128) *
          (6931471808 / 10 ^ 10) : ℚ) : ℝ) ≤
          (((UpperRecords.CompletionData.record k).budget : ℚ) : ℝ) := by
        rw [hk']
        exact_mod_cast hcq
      push_cast at hcq'
      rw [hX, hY, log_cellPoint_pow2 hbb]
      have hl2 : Real.log 2 < 6931471808 / 10 ^ 10 := by
        have := Real.log_two_lt_d9
        norm_num at this ⊢
        linarith
      have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hm : ((geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (128 * (b' - b)) p + 1 : ℕ) : ℝ) ≤
          ((r.2.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hhi
      have hn0 : (0 : ℝ) ≤ r.2.2 := Nat.cast_nonneg _
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
      have hstep : (r.2.2 : ℝ) * (((b : ℝ) + ((geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ)
          (128 * (b' - b)) p + 1 : ℕ) : ℝ) / 128) * Real.log 2) ≤
          (r.2.2 : ℝ) * (((b : ℝ) + ((r.2.1 + 1 : ℕ) : ℝ) / 128) * (6931471808 / 10 ^ 10)) := by
        apply mul_le_mul_of_nonneg_left _ hn0
        apply mul_le_mul (by linarith) hl2.le hl2'.le (by positivity)
      rw [hX, hY] at hstep
      push_cast at hstep ⊢
      linarith

/-- **The recorded band cells satisfy `def:record:upper-bands`(b).** -/
theorem recordedBandRule_valid : BandRulesValid recordedBandRule := by
  intro k p h1 h2
  unfold recordedBandRule
  by_cases hk : 301 ≤ k.val
  · simp only [hk, ↓reduceDIte]
    exact farRule_valid k ⟨k.val - 301, by omega⟩ (by simp; omega) p h1 h2
  · simp only [hk, ↓reduceDIte]
    exact paperBandRule_valid k p h1 h2

/-- **`lem:record:local-domain`(ii) for the paper's partition** (`def:record:exact-blocks`(c), (d)
with the recorded bins, `def:record:upper-bands`(b) with the recorded cells): every block of a
middle piece has `∑ log p ≤ 570`, every block of band `k` has `∑ log p ≤ L_band(k)`. -/
theorem paperCell_budget : PaperBudget paperCell := paperCellWith_budget recordedBandRule_valid

end Sarkozy.PaperNumbers
