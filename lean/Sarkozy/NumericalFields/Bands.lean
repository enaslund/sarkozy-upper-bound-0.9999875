module

public import Sarkozy.PaperNumbers.Charge
public import Sarkozy.MainFinal.UpperPrices

@[expose] public section





open Finset

namespace Sarkozy.NumericalFields

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.MainTarget Sarkozy.PaperNumbers

/-! ## The recorded cells of a band -/

/-- The index `k - 301` of a far band among the nine far bands (reduced mod `9`, so that no proof
occurs in it). -/
def farIdx (k : Fin 310) : Fin 9 := ⟨(k.val - 301) % 9, Nat.mod_lt _ (by norm_num)⟩

/-- The number `𝗇` of recorded cells of band `k`: `128 (b' - b)` on the far bands `[2^b, 2^{b'})`
(`k ≥ 301`), `bandCells k` (two) below `2⁵²`. -/
noncomputable def bandN (k : Fin 310) : ℕ :=
  if 301 ≤ k.val then 128 * ((farBand (farIdx k)).2.1 - (farBand (farIdx k)).1)
  else bandCells k

/-- The cell points `x_j = X^{1-j/𝗇} Y^{j/𝗇}` of band `k`. -/
noncomputable def bx (k : Fin 310) (j : ℕ) : ℝ :=
  cellPoint ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (bandN k) j

/-- The recorded block cardinalities `n_j` of band `k`. -/
noncomputable def bnc (k : Fin 310) (j : ℕ) : ℕ := (recordedBandRule k).card j

theorem rule_far (k : Fin 310) (hk : 301 ≤ k.val) :
    recordedBandRule k = farRule k (farIdx k) := by
  unfold recordedBandRule
  simp only [hk, ↓reduceDIte]
  have hlt := k.isLt
  exact congrArg (farRule k) (Fin.ext (by simp only [farIdx]; omega))

theorem rule_near (k : Fin 310) (hk : ¬ 301 ≤ k.val) : recordedBandRule k = paperBandRule k := by
  unfold recordedBandRule
  simp only [hk, ↓reduceDIte]

theorem bandN_far (k : Fin 310) (hk : 301 ≤ k.val) :
    bandN k = 128 * ((farBand (farIdx k)).2.1 - (farBand (farIdx k)).1) := by
  unfold bandN
  simp only [hk, ↓reduceIte]

theorem bandN_near (k : Fin 310) (hk : ¬ 301 ≤ k.val) : bandN k = bandCells k := by
  unfold bandN
  simp only [hk, ↓reduceIte]

/-- **The recorded rule of a band is geometric**: index, lower and upper cell points. -/
theorem rule_eq (k : Fin 310) :
    (recordedBandRule k).idx = geoIdx ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (bandN k) ∧
      (recordedBandRule k).bot = bx k ∧ (recordedBandRule k).top = fun j => bx k (j + 1) := by
  unfold bx
  by_cases hk : 301 ≤ k.val
  · rw [rule_far k hk, bandN_far k hk]
    exact ⟨rfl, rfl, rfl⟩
  · rw [rule_near k hk, bandN_near k hk]
    exact ⟨rfl, rfl, rfl⟩

/-- The band ends are even (multiples of `2⁴⁰`). -/
theorem band_even : ∀ k : Fin 310, Even (bandOf k).1 ∧ Even (bandOf k).2 := by
  decide +kernel

/-- The bands are nonempty intervals. -/
theorem band_lt : ∀ k : Fin 310, (bandOf k).1 < (bandOf k).2 := by
  decide +kernel

theorem bandX_pos (k : Fin 310) : (4800162889 : ℝ) ≤ (bandOf k).1 := by
  have h := P3_le_bandStart k
  have h' : 4800162889 ≤ (bandOf k).1 := le_trans (by norm_num [P3]) h
  exact_mod_cast h'

theorem bandXY (k : Fin 310) : ((bandOf k).1 : ℝ) < (bandOf k).2 := by
  exact_mod_cast band_lt k

theorem one_le_bandN (k : Fin 310) : 1 ≤ bandN k := by
  by_cases hk : 301 ≤ k.val
  · rw [bandN_far k hk]
    have := (farBand_spec (farIdx k)).2
    omega
  · rw [bandN_near k hk]
    unfold bandCells
    split_ifs
    · norm_num
    · exact one_le_cellCount (by linarith [bandX_pos k]) (bandXY k)

/-- **`1 ≤ n_j` on every recorded cell** of a band. -/
theorem one_le_bnc (k : Fin 310) {j : ℕ} (hj : j < bandN k) : 1 ≤ bnc k j := by
  unfold bnc
  by_cases hk : 301 ≤ k.val
  · rw [rule_far k hk]
    generalize farIdx k = f
    change 1 ≤ runCard (farBand f).2.2 j
    rcases runCard_spec (farBand f).2.2 j with h | ⟨r, hmem, -, -, heq⟩
    · rw [h]
    · rw [heq]
      have hc := List.all_eq_true.mp (farRuns_check f) r hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
  · rw [rule_near k hk]
    rw [bandN_near k hk] at hj
    have hx0 : (0 : ℝ) < (bandOf k).1 := by linarith [bandX_pos k]
    have hn1 : 1 ≤ bandCells k := bandN_near k hk ▸ one_le_bandN k
    obtain ⟨-, hhi⟩ := cellPoint_le_top hx0 (bandXY k).le hn1 (by omega : j + 1 ≤ bandCells k)
    have hlo : ((bandOf k).1 : ℝ) ≤
        cellPoint ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (bandCells k) (j + 1) :=
      (cellPoint_le_top hx0 (bandXY k).le hn1 (by omega : j + 1 ≤ bandCells k)).1
    have hlc : 0 < Real.log (cellPoint ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (bandCells k)
        (j + 1)) := Real.log_pos (by linarith [bandX_pos k])
    have hlY : Real.log (cellPoint ((bandOf k).1 : ℝ) ((bandOf k).2 : ℝ) (bandCells k) (j + 1)) ≤
        ((UpperRecords.CompletionData.record k).budget : ℝ) := by
      have h1 := Real.log_le_log (by linarith [bandX_pos k]) hhi
      have h2 := log_siteStop_lt (.inr k)
      have h3 := budget_ge_550 (.inr k)
      change Real.log ((bandOf k).2 : ℝ) < 355 at h2
      change (550 : ℝ) ≤ ((UpperRecords.CompletionData.record k).budget : ℝ) at h3
      linarith
    change 1 ≤ cellCard _ _ _ _ j
    unfold cellCard
    rw [Nat.one_le_floor_iff, one_le_div hlc]
    exact hlY

/-! ## The descriptors of the blocks of a band -/

/-- The primes `≡ 3 (mod 4)` of cell `j` of band `k`, in increasing order. -/
noncomputable def cellPsB (k : Fin 310) (j : ℕ) : List ℕ :=
  Misc.cellList ((recordedBandRule k).bot j) ((recordedBandRule k).top j)

/-- M2's term of the `m`-th block of cell `j` of band `k`. -/
noncomputable def cellTermB (k : Fin 310) (a : ℝ) (d j m : ℕ) : ℝ :=
  ((Misc.blockProd (cellPsB k j) (bnc k j) m : ℕ) : ℝ) ^ (2 * a) *
    ((Misc.blockStart (cellPsB k j) (bnc k j) m : ℕ) : ℝ) ^ (-((d : ℝ) / 2))

/-- The term of a descriptor `⟨1, ⟨j, m⟩⟩`. -/
noncomputable def descTermB (k : Fin 310) (a : ℝ) (d c : ℕ) : ℝ :=
  cellTermB k a d (Nat.unpair (Nat.unpair c).2).1 (Nat.unpair (Nat.unpair c).2).2

/-- The descriptors of the blocks of the cells of band `k`. -/
noncomputable def cellDescB (k : Fin 310) : Finset ℕ :=
  ((range (bandN k)).sigma fun j =>
      range (Misc.blockCount (cellPsB k j).length (bnc k j))).image
    fun x => Nat.pair 1 (Nat.pair x.1 x.2)

theorem descTermB_nonneg (k : Fin 310) (a : ℝ) (d c : ℕ) : 0 ≤ descTermB k a d c := by
  unfold descTermB cellTermB
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **The descriptor sum is M2's charge of the cells of the band.** -/
theorem sum_descB (k : Fin 310) (a : ℝ) (d : ℕ) :
    ∑ c ∈ cellDescB k, descTermB k a d c =
      ∑ j ∈ range (bandN k), Misc.cellCharge (cellPsB k j) (bnc k j) a ((d : ℝ) / 2) := by
  unfold cellDescB
  rw [sum_image (pair_sigma_inj 1), sum_sigma]
  simp only [descTermB, Nat.unpair_pair]
  rfl

/-- **The descriptor of a block of band `k`**: its cell value lies in the descriptor set, and its
term is at most the descriptor's term. -/
theorem block_descB (k : Fin 310) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) (b : PaperBlock paperCell)
    (hs : blockSite b = .inr k) :
    b.val.2 ∈ cellDescB k ∧
      BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf paperCell)) a (.inr b) ≤
        descTermB k a d b.val.2 := by
  obtain ⟨j0⟩ := blockIdx_nonempty b
  have hlab := (coord_facts (U := recordedBandRule) b j0).2.2
  have hsite0 : siteOf j0.1.1 = .inr k := by
    have : blockSite b = siteOf j0.1.1 := by unfold blockSite; rw [hlab]
    rw [← this, hs]
  have hval : b.val.2 = paperCellWith recordedBandRule j0.1.1 := by rw [hlab]
  obtain ⟨hpr0, h30, hQ0, hP0⟩ := (coord_facts (U := recordedBandRule) b j0).2.1
  have hmem0 := siteOf_mem hQ0 hP0
  rw [hsite0] at hmem0
  have hband0 : (bandOf k).1 ≤ j0.1.1 ∧ j0.1.1 < (bandOf k).2 := hmem0
  have hX0 : ¬ j0.1.1 < XCh := by
    have := P3_le_bandStart k
    have := XCh_lt_P3
    omega
  have hok0 : CellOK (recordedBandRule k) (UpperRecords.CompletionData.record k).budget j0.1.1 :=
    recordedBandRule_valid k j0.1.1 hband0.1 hband0.2
  have hJ : (siteRule recordedBandRule (siteOf j0.1.1)).idx j0.1.1 =
      (recordedBandRule k).idx j0.1.1 := by
    rw [hsite0]; rfl
  have hps : cellListOf recordedBandRule j0.1.1 = cellPsB k ((recordedBandRule k).idx j0.1.1) := by
    unfold cellListOf
    rw [hsite0]
    rfl
  have hk : cellCardOf recordedBandRule j0.1.1 = bnc k ((recordedBandRule k).idx j0.1.1) := by
    unfold cellCardOf
    rw [hsite0]
    rfl
  have hk1 : 1 ≤ bnc k ((recordedBandRule k).idx j0.1.1) := hok0.2.2.1
  have hc : b.val.2 = Nat.pair 1 (Nat.pair ((recordedBandRule k).idx j0.1.1)
      (cellPos recordedBandRule j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1))) := by
    rw [hval]
    unfold paperCellWith
    simp only [hX0, ↓reduceIte]
    rw [hJ, hk]
  -- the coordinates lie in the cell list
  have hmemj : ∀ j : Coord recordedBandRule b,
      j.1.1 ∈ cellPsB k ((recordedBandRule k).idx j0.1.1) := by
    intro j
    obtain ⟨hpr, h3, hQ, hPj⟩ := (coord_facts b j).2.1
    obtain ⟨-, hsj, hij, -⟩ := coord_cell hX0 j
    rw [← hps, ← cellListOf_eq hsj hij]
    have hmj := siteOf_mem hQ hPj
    rw [hsj, hsite0] at hmj
    have hokj : CellOK (siteRule recordedBandRule (siteOf j.1.1))
        (UpperRecords.CompletionData.record k).budget j.1.1 := by
      rw [hsj, hsite0]
      exact recordedBandRule_valid k j.1.1 hmj.1 hmj.2
    exact mem_cellListOf hpr h3 hokj
  have hidx0 : (cellPsB k ((recordedBandRule k).idx j0.1.1)).idxOf j0.1.1 =
      cellPos recordedBandRule j0.1.1 := by
    unfold cellPos
    rw [hps]
  have hmk : cellPos recordedBandRule j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1) *
      bnc k ((recordedBandRule k).idx j0.1.1) <
        (cellPsB k ((recordedBandRule k).idx j0.1.1)).length := by
    have h1 := Nat.div_mul_le_self (cellPos recordedBandRule j0.1.1)
      (bnc k ((recordedBandRule k).idx j0.1.1))
    have h2 := List.idxOf_lt_length_of_mem (hmemj j0)
    rw [hidx0] at h2
    omega
  have hsubl : List.Sublist (cellBlock (cellPsB k ((recordedBandRule k).idx j0.1.1))
      (bnc k ((recordedBandRule k).idx j0.1.1))
      (cellPos recordedBandRule j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1)))
        (cellPsB k ((recordedBandRule k).idx j0.1.1)) :=
    (List.take_sublist _ _).trans (List.drop_sublist _ _)
  refine ⟨?_, ?_⟩
  · rw [hc]
    apply mem_image.mpr
    refine ⟨⟨(recordedBandRule k).idx j0.1.1,
      cellPos recordedBandRule j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1)⟩, ?_, rfl⟩
    rw [mem_sigma, mem_range, mem_range]
    refine ⟨?_, lt_blockCount hk1 hmk⟩
    rw [(rule_eq k).1]
    have hxp : ((bandOf k).1 : ℝ) ≤ j0.1.1 := by exact_mod_cast hband0.1
    have hpY : (j0.1.1 : ℝ) < (bandOf k).2 := by exact_mod_cast hband0.2
    exact (geoIdx_spec (one_le_bandN k) (by linarith [bandX_pos k]) (bandXY k) hxp hpY).2.2.2
  · rw [hc]
    unfold descTermB cellTermB
    simp only [Nat.unpair_pair]
    have hnd : (cellPsB k ((recordedBandRule k).idx j0.1.1)).Nodup := by
      unfold cellPsB Misc.cellList
      exact Finset.sort_nodup _ _
    have hle := blockTerm_le ha d b _ (hnd.sublist hsubl)
      ((Misc.cellList_sorted _ _).sublist hsubl)
      (fun q hq => (Misc.mem_cellPrimes.mp (Misc.mem_cellList.mp (hsubl.subset hq))).1.pos)
      (fun j => by
        obtain ⟨-, hsj, hij, hmj⟩ := coord_cell hX0 j
        apply mem_cellBlock_of_idx hk1 (hmemj j)
        have e1 : (cellPsB k ((recordedBandRule k).idx j0.1.1)).idxOf j.1.1 =
            cellPos recordedBandRule j.1.1 := by
          unfold cellPos
          rw [cellListOf_eq hsj hij, hps]
        have e2 : bnc k ((recordedBandRule k).idx j0.1.1) = cellCardOf recordedBandRule j.1.1 := by
          rw [cellCardOf_eq hsj hij, hk]
        rw [e1, e2, hmj, cellCardOf_eq hsj hij])
    have hhead : (cellBlock (cellPsB k ((recordedBandRule k).idx j0.1.1))
        (bnc k ((recordedBandRule k).idx j0.1.1))
        (cellPos recordedBandRule j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1))).headD 0 =
          Misc.blockStart (cellPsB k ((recordedBandRule k).idx j0.1.1))
            (bnc k ((recordedBandRule k).idx j0.1.1))
            (cellPos recordedBandRule j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1)) := by
      rw [Misc.cellBlock_eq_cons hk1 hmk]
      rfl
    rw [hhead, neg_div] at hle
    exact hle

/-- **The bridge** (`lem:record:block-charge`(i) at a band): the charge of the paper's blocks of
band `k` is at most M2's `cellCharge` summed over the recorded cells of the band. -/
theorem bandCells_le (k : Fin 310) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    ∑ b ∈ univ.filter (fun b : PaperBlock paperCell => blockSite b = .inr k),
        BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf paperCell)) a (.inr b) ≤
      ∑ j ∈ range (bandN k), Misc.cellCharge (cellPsB k j) (bnc k j) a ((d : ℝ) / 2) := by
  rw [← sum_descB k a d]
  have hinj : Set.InjOn (fun b : PaperBlock paperCell => b.val.2)
      (univ.filter fun b : PaperBlock paperCell => blockSite b = .inr k) := by
    intro x hx y hy h
    have hx' : x.val.1 = .inr k := (mem_filter.mp hx).2
    have hy' : y.val.1 = .inr k := (mem_filter.mp hy).2
    exact PaperBlock.ext (Prod.ext (hx'.trans hy'.symm) h)
  calc ∑ b ∈ univ.filter (fun b : PaperBlock paperCell => blockSite b = .inr k),
        BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf paperCell)) a (.inr b)
      ≤ ∑ b ∈ univ.filter (fun b : PaperBlock paperCell => blockSite b = .inr k),
          descTermB k a d b.val.2 :=
        sum_le_sum fun b hb => (block_descB k ha d b (mem_filter.mp hb).2).2
    _ = ∑ c ∈ (univ.filter (fun b : PaperBlock paperCell => blockSite b = .inr k)).image
          (fun b => b.val.2), descTermB k a d c := (sum_image hinj).symm
    _ ≤ ∑ c ∈ cellDescB k, descTermB k a d c := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro c hc
          obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
          exact (block_descB k ha d b (mem_filter.mp hb).2).1
        · intro c _ _
          exact descTermB_nonneg k a d c

/-! ## `thm:bmor` on the cells of a band -/

/-- **The right side of `eq:record:cell-charge` for band `k`** at `s = d/2`, with the error constant
`2411/(5·10⁶ log X)` of `thm:bmor` (M2's `cell_charge_bmor`). -/
noncomputable def bandBound (a : ℝ) (d : ℕ) (k : Fin 310) : ℝ :=
  ∑ j ∈ range (bandN k), Misc.cellPi a (bx k) (bnc k) j * bx k j ^ (-((d : ℝ) / 2)) +
    (1 / 2 + 2411 / (5000000 * Real.log (bx k 0))) *
      ∑ j ∈ range (bandN k), Misc.cellG a (bx k) (bnc k) j *
        Misc.cellIntegral ((d : ℝ) / 2) (bx k j) (bx k (j + 1)) +
    2411 / (5000000 * Real.log (bx k 0)) *
      Misc.cellEdge (bandN k) (bx k) (Misc.cellG a (bx k) (bnc k)) ((d : ℝ) / 2)

/-- **The band charge from `thm:bmor`** (`Target.BMOR`, H2; `lem:record:block-charge`(i),
`eq:record:cell-charge` with `s = d/2`, any `d`): the charge of the paper's blocks of band `k` is
at most `bandBound a d k`. -/
theorem bandCharge_le_bandBound (hB : Target.BMOR) (k : Fin 310) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    ∑ b ∈ univ.filter (fun b : PaperBlock paperCell => blockSite b = .inr k),
        BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf paperCell)) a (.inr b) ≤ bandBound a d k := by
  have hcells : ∑ j ∈ range (bandN k), Misc.cellCharge (cellPsB k j) (bnc k j) a ((d : ℝ) / 2) =
      ∑ j ∈ range (bandN k),
        Misc.cellCharge (Misc.cellList (bx k j) (bx k (j + 1))) (bnc k j) a ((d : ℝ) / 2) := by
    obtain ⟨-, hbot, htop⟩ := rule_eq k
    unfold cellPsB
    rw [hbot, htop]
  refine (bandCells_le k ha d).trans (hcells.le.trans ?_)
  have hx0 : (0 : ℝ) < (bandOf k).1 := by linarith [bandX_pos k]
  have h0 : (4800162889 : ℝ) ≤ bx k 0 := by
    unfold bx
    rw [Misc.cellPoint_zero]
    exact bandX_pos k
  exact Misc.cell_charge_bmor hB (one_le_bandN k) (bx k) h0
    (fun j _ => Misc.cellPoint_mono hx0 (bandXY k).le _ _)
    (fun j hj => Misc.notPrime3_cellPoint (band_even k).1 (band_even k).2 (one_le_bandN k) hj)
    (bnc k) (fun j hj => one_le_bnc k hj) ha (by positivity)

end Sarkozy.NumericalFields
