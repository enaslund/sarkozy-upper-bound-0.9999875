module

public import Sarkozy.AnalyticCells.F1Data
public import Sarkozy.PaperNumbers.Budget

@[expose] public section






open Finset

namespace Sarkozy.AnalyticCells

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.PaperNumbers

/-- The F1 cell count of piece `i` (`i ≤ 28`). -/
def nF1 (i : Fin 33) : ℕ := f1Cells.getD i.val 1

/-- **The cells of middle piece `i`**: F1 geometric cells for `i ≤ 28`, the paper's above. -/
noncomputable def f1Rule (i : Fin 33) : CellRule :=
  if i.val < 29 then geoRule (pieceStart i : ℝ) (pieceStop i : ℝ) (nF1 i) (middleBudget : ℝ)
  else middleRule i

/-- The cell rule of a site. -/
noncomputable def f1SiteRule : Site → CellRule
  | .inl i => f1Rule i
  | .inr k => recordedBandRule k

/-- The primes `≡ 3 (mod 4)` of the cell of `p`, in increasing order. -/
noncomputable def f1CellList (p : ℕ) : List ℕ :=
  Misc.cellList ((f1SiteRule (siteOf p)).bot ((f1SiteRule (siteOf p)).idx p))
    ((f1SiteRule (siteOf p)).top ((f1SiteRule (siteOf p)).idx p))

/-- The position of `p` in its cell. -/
noncomputable def f1Pos (p : ℕ) : ℕ := (f1CellList p).idxOf p

/-- The cardinality `n_j` of the cell of `p`. -/
noncomputable def f1Card (p : ℕ) : ℕ :=
  (f1SiteRule (siteOf p)).card ((f1SiteRule (siteOf p)).idx p)

/-- **The F1 within-site rule.** -/
noncomputable def f1Cell (p : ℕ) : ℕ :=
  Nat.pair ((f1SiteRule (siteOf p)).idx p) (f1Pos p / f1Card p)

/-! ## The cell conditions -/

theorem nF1_pos : ∀ i : Fin 33, i.val < 29 → 1 ≤ nF1 i := by decide +kernel

theorem pieceStart_ge_XCh : ∀ i : Fin 33, 29 ≤ i.val → XCh ≤ pieceStart i := by decide +kernel

theorem pieceStop_le_two34 : ∀ i : Fin 33, i.val < 29 → pieceStop i ≤ 2 ^ 34 := by decide +kernel

theorem f1Rule_valid (i : Fin 33) {p : ℕ} (h1 : pieceStart i ≤ p) (h2 : p < pieceStop i) :
    CellOK (f1Rule i) (middleBudget : ℝ) p := by
  unfold f1Rule
  split_ifs with hi
  · have hQ : Q3 ≤ pieceStart i := pieceStart_ge_Q3 i
    have hx1 : (1 : ℝ) ≤ pieceStart i := by
      have : 1 ≤ pieceStart i := le_trans (by norm_num [Q3]) hQ
      exact_mod_cast this
    have hxp : (pieceStart i : ℝ) ≤ p := by exact_mod_cast h1
    have hpY : (p : ℝ) < pieceStop i := by exact_mod_cast h2
    have hYL : Real.log (pieceStop i) ≤ (middleBudget : ℝ) := by
      have hs := pieceStop_le_two34 i hi
      have h0 : (0 : ℝ) < pieceStop i := by linarith
      have h3 : (pieceStop i : ℝ) ≤ 2 ^ 34 := by exact_mod_cast hs
      have h4 : Real.log (pieceStop i) ≤ Real.log ((2 : ℝ) ^ 34) := Real.log_le_log h0 h3
      rw [Real.log_pow] at h4
      have h5 := Real.log_two_lt_d9
      have h6 : ((middleBudget : ℕ) : ℝ) = 570 := by unfold middleBudget; norm_num
      rw [h6]
      push_cast at h4
      linarith
    exact geoRule_valid (nF1_pos i hi) hx1 (hxp.trans_lt hpY) hYL hxp hpY
  · exact middleRule_valid i ((pieceStart_ge_XCh i (by omega)).trans h1) h1 h2

theorem f1SiteRule_valid {p : ℕ} (hQ : Q3 ≤ p) (hP : p < P4) :
    CellOK (f1SiteRule (siteOf p)) (siteBudget (siteOf p) : ℝ) p := by
  have hm := siteOf_mem hQ hP
  rcases hs : siteOf p with i | k
  · rw [hs] at hm
    exact f1Rule_valid i hm.1 hm.2
  · rw [hs] at hm
    exact recordedBandRule_valid k p hm.1 hm.2

/-! ## The budget -/

/-- The coordinates of a block of the F1 rule. -/
abbrev F1Coord (b : PaperBlock f1Cell) : Type :=
  {j : PaperJ0 // paperAtomMap (paperBlockOf f1Cell) j = .inr b}

theorem f1coord_facts (b : PaperBlock f1Cell) (j : F1Coord b) :
    blockPrimes (paperBlockOf f1Cell) b j = j.1.1 ∧
      (j.1.1.Prime ∧ j.1.1 % 4 = 3 ∧ Q3 ≤ j.1.1 ∧ j.1.1 < P4) ∧
      b.1 = (siteOf j.1.1, f1Cell j.1.1) := by
  have hP : blockPrimes (paperBlockOf f1Cell) b j = j.1.1 :=
    paperM0_cls3 (blockOf_of_coord j).1
  have h := blockPrimes_mod_ge b j
  rw [hP] at h
  exact ⟨hP, ⟨paperJ0_prime j.1, h.1, h.2, paperJ0_lt_P4 j.1⟩, (blockOf_of_coord j).2⟩

/-- All coordinates of a block lie in the same site, the same cell and the same block of the
cell. -/
theorem f1coord_cell {b : PaperBlock f1Cell} (j0 j : F1Coord b) :
    siteOf j.1.1 = siteOf j0.1.1 ∧
      (f1SiteRule (siteOf j0.1.1)).idx j.1.1 = (f1SiteRule (siteOf j0.1.1)).idx j0.1.1 ∧
      f1Pos j.1.1 / f1Card j.1.1 = f1Pos j0.1.1 / f1Card j0.1.1 := by
  have h := ((f1coord_facts b j).2.2.symm.trans (f1coord_facts b j0).2.2)
  have hs : siteOf j.1.1 = siteOf j0.1.1 := (Prod.ext_iff.mp h).1
  have h' : f1Cell j.1.1 = f1Cell j0.1.1 := (Prod.ext_iff.mp h).2
  unfold f1Cell at h'
  rw [hs] at h'
  obtain ⟨h1, h2⟩ := Nat.pair_eq_pair.mp h'
  exact ⟨hs, h1, h2⟩

theorem f1CellList_eq {p p' : ℕ} (hs : siteOf p = siteOf p')
    (hi : (f1SiteRule (siteOf p')).idx p = (f1SiteRule (siteOf p')).idx p') :
    f1CellList p = f1CellList p' := by
  unfold f1CellList
  rw [hs, hi]

theorem f1Card_eq {p p' : ℕ} (hs : siteOf p = siteOf p')
    (hi : (f1SiteRule (siteOf p')).idx p = (f1SiteRule (siteOf p')).idx p') :
    f1Card p = f1Card p' := by
  unfold f1Card
  rw [hs, hi]

theorem mem_f1CellList {p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3) {L : ℝ}
    (hok : CellOK (f1SiteRule (siteOf p)) L p) : p ∈ f1CellList p := by
  unfold f1CellList
  rw [Misc.mem_cellList, Misc.mem_cellPrimes]
  exact ⟨hp, h3, hok.1, hok.2.1⟩

/-- **The budget of a block of the F1 rule, at its site's budget.** -/
theorem f1Cell_sum_le (b : PaperBlock f1Cell) :
    ∑ j, Real.log (blockPrimes (paperBlockOf f1Cell) b j) ≤ (siteBudget (blockSite b) : ℝ) := by
  obtain ⟨j0⟩ := blockIdx_nonempty b
  have hbs : blockSite b = siteOf j0.1.1 := by
    unfold blockSite
    rw [(f1coord_facts b j0).2.2]
  have hinjP : Function.Injective fun j : F1Coord b => j.1.1 :=
    fun x y h => Subtype.ext (Subtype.ext h)
  rw [hbs]
  simp only [fun j => (f1coord_facts b j).1]
  obtain ⟨hpr0, h30, hQ0, hP0⟩ := (f1coord_facts b j0).2.1
  have hok0 := f1SiteRule_valid hQ0 hP0
  obtain ⟨-, htop0, hn1, hnL⟩ := hok0
  set R := f1SiteRule (siteOf j0.1.1)
  set n := R.card (R.idx j0.1.1)
  set top := R.top (R.idx j0.1.1)
  have hokj : ∀ j : F1Coord b, CellOK (f1SiteRule (siteOf j.1.1))
      (siteBudget (siteOf j.1.1) : ℝ) j.1.1 := fun j =>
    f1SiteRule_valid (f1coord_facts b j).2.1.2.2.1 (f1coord_facts b j).2.1.2.2.2
  have hlist : ∀ j : F1Coord b, f1CellList j.1.1 = f1CellList j0.1.1 := fun j =>
    f1CellList_eq (f1coord_cell j0 j).1 (f1coord_cell j0 j).2.1
  have hmem : ∀ j : F1Coord b, j.1.1 ∈ f1CellList j0.1.1 := fun j => by
    rw [← hlist j]
    exact mem_f1CellList (f1coord_facts b j).2.1.1 (f1coord_facts b j).2.1.2.1 (hokj j)
  have hjtop : ∀ j : F1Coord b, (j.1.1 : ℝ) < top := by
    intro j
    have := (hokj j).2.1
    rw [(f1coord_cell j0 j).1, (f1coord_cell j0 j).2.1] at this
    exact this
  have htop1 : 1 < top := by
    have : (1 : ℝ) < j0.1.1 := by exact_mod_cast hpr0.one_lt
    exact this.trans htop0
  have hltop : 0 < Real.log top := Real.log_pos htop1
  have hcard : Fintype.card (F1Coord b) ≤ n := by
    apply card_le_of_rank hn1 (fun j => f1Pos j.1.1)
    · intro x y hxy
      have hxy' : (f1CellList j0.1.1).idxOf x.1.1 = (f1CellList j0.1.1).idxOf y.1.1 := by
        have := hxy
        simp only [f1Pos] at this
        rw [hlist x, hlist y] at this
        exact this
      exact hinjP ((List.idxOf_inj (hmem x)).mp hxy')
    · intro j
      have := (f1coord_cell j0 j).2.2
      rw [f1Card_eq (f1coord_cell j0 j).1 (f1coord_cell j0 j).2.1] at this
      exact this
  calc ∑ j : F1Coord b, Real.log (j.1.1 : ℝ)
      ≤ ∑ _j : F1Coord b, Real.log top := by
        apply sum_le_sum
        intro j _
        have hpos : (0 : ℝ) < j.1.1 := by exact_mod_cast (f1coord_facts b j).2.1.1.pos
        exact Real.log_le_log hpos (hjtop j).le
    _ = (Fintype.card (F1Coord b) : ℝ) * Real.log top := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ (n : ℝ) * Real.log top :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hltop.le
    _ ≤ (siteBudget (siteOf j0.1.1) : ℝ) := hnL

/-- **`lem:record:local-domain`(ii) for the F1 partition**: `PaperBudget f1Cell`. -/
theorem f1Cell_budget : PaperBudget f1Cell := by
  intro b
  have hsum := f1Cell_sum_le b
  refine ⟨fun i hs => ?_, fun k hs => ?_⟩
  · rw [hs] at hsum
    exact hsum
  · rw [hs] at hsum
    exact hsum

end Sarkozy.AnalyticCells
