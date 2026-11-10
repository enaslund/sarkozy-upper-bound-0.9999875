module

public import Sarkozy.MainFinalF1.Prices
public import Sarkozy.NumericalFields.Bands
public import Sarkozy.AnalyticCells.F1Charge

@[expose] public section

/-!
# E2's band charges at `f1Cell` (F1P)

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`(i), `eq:record:cell-charge`;
`def:record:upper-bands`(b); `prop:record:upper`(ii).

**The one genuinely partition-dependent proof of the port.** E2's bridge `bandCells_le`
(`NumericalFields/Bands.lean`) unfolds `paperCellWith recordedBandRule` above `X_Ch`, whose cell
value is `⟨1, ⟨j, m⟩⟩`. N2's `f1Cell` uses the same rule `recordedBandRule k` on band `k`
(`f1SiteRule (.inr k) = recordedBandRule k`), so the blocks are the same sets of primes, but the
cell value is `⟨j, m⟩` (no leading `1`). Here the bridge is re-proved at `f1Cell` along N2's
`f1_block_desc` (the middle-piece version), with the band's cells `cellPsB k j`, `bnc k j` of E2:

* `f1_block_descB`: every block of band `k` of `f1Cell` maps, by its cell value `⟨j, m⟩`, to the
  `m`-th block of M2's `cellBlock`s of recorded cell `j` of the band, which contains its primes;
* `f1_bandCells_le`: the charge of the `f1Cell` blocks of band `k` is at most the sum of M2's
  `cellCharge` over the band's recorded cells (the same right side as E2's `bandCells_le`);
* `f1_bandCharge_le_bandBound`: with M2's `cell_charge_bmor`, at most E2's `bandBound a d k`
  (`thm:bmor`, H2);
* `upperBand_le_bandBound`: K2's field `hUS` (= `hUA`) at `f1Cell`, `𝒰 = bandBound a_T`.
-/

open Finset

namespace Sarkozy.MainFinalF1

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.MainTarget Sarkozy.PaperNumbers
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg)
open Sarkozy.ComparisonLawPaper (upperBand blockSel specUpper)
open Sarkozy.NumericalFields (bandN bx bnc rule_eq cellPsB cellTermB bandBound one_le_bandN
  one_le_bnc band_even bandX_pos bandXY)
open Sarkozy.AnalyticCells (f1Cell f1SiteRule f1CellList f1Pos f1Card F1Coord f1coord_facts
  f1coord_cell f1CellList_eq f1Card_eq mem_f1CellList f1BlockTerm_le f1_pair_inj)

/-- The descriptors `⟨j, m⟩` of the `f1Cell` blocks of band `k` (E2's `cellDescB` without the
leading `1`). -/
noncomputable def f1DescB (k : Fin 310) : Finset ℕ :=
  ((range (bandN k)).sigma fun j =>
      range (Misc.blockCount (cellPsB k j).length (bnc k j))).image
    fun x => Nat.pair x.1 x.2

/-- The term of a descriptor `⟨j, m⟩` (E2's `cellTermB`). -/
noncomputable def f1DescTermB (k : Fin 310) (a : ℝ) (d c : ℕ) : ℝ :=
  cellTermB k a d (Nat.unpair c).1 (Nat.unpair c).2

theorem f1DescTermB_nonneg (k : Fin 310) (a : ℝ) (d c : ℕ) : 0 ≤ f1DescTermB k a d c := by
  unfold f1DescTermB cellTermB
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **The descriptor sum is M2's charge of the cells of the band.** -/
theorem f1_sum_descB (k : Fin 310) (a : ℝ) (d : ℕ) :
    ∑ c ∈ f1DescB k, f1DescTermB k a d c =
      ∑ j ∈ range (bandN k), Misc.cellCharge (cellPsB k j) (bnc k j) a ((d : ℝ) / 2) := by
  unfold f1DescB
  rw [sum_image f1_pair_inj, sum_sigma]
  simp only [f1DescTermB, Nat.unpair_pair]
  rfl

/-- **The descriptor of an `f1Cell` block of band `k`** (`lem:record:block-charge`(i)): its cell
value lies in the descriptor set, and its term is at most the descriptor's term. -/
theorem f1_block_descB (k : Fin 310) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) (b : PaperBlock f1Cell)
    (hs : blockSite b = .inr k) :
    b.val.2 ∈ f1DescB k ∧
      BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b) ≤
        f1DescTermB k a d b.val.2 := by
  obtain ⟨j0⟩ := blockIdx_nonempty b
  have hlab := (f1coord_facts b j0).2.2
  have hsite0 : siteOf j0.1.1 = .inr k := by
    have : blockSite b = siteOf j0.1.1 := by unfold blockSite; rw [hlab]
    rw [← this, hs]
  have hval : b.val.2 = f1Cell j0.1.1 := by rw [hlab]
  obtain ⟨hpr0, h30, hQ0, hP0⟩ := (f1coord_facts b j0).2.1
  have hmem0 := siteOf_mem hQ0 hP0
  rw [hsite0] at hmem0
  have hband0 : (bandOf k).1 ≤ j0.1.1 ∧ j0.1.1 < (bandOf k).2 := hmem0
  have hRsite : f1SiteRule (siteOf j0.1.1) = recordedBandRule k := by rw [hsite0]; rfl
  have hok0 : CellOK (recordedBandRule k) (UpperRecords.CompletionData.record k).budget j0.1.1 :=
    recordedBandRule_valid k j0.1.1 hband0.1 hband0.2
  have hps : f1CellList j0.1.1 = cellPsB k ((recordedBandRule k).idx j0.1.1) := by
    unfold f1CellList cellPsB
    rw [hRsite]
  have hk : f1Card j0.1.1 = bnc k ((recordedBandRule k).idx j0.1.1) := by
    unfold f1Card bnc
    rw [hRsite]
  have hk1 : 1 ≤ bnc k ((recordedBandRule k).idx j0.1.1) := hok0.2.2.1
  have hc : b.val.2 = Nat.pair ((recordedBandRule k).idx j0.1.1)
      (f1Pos j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1)) := by
    rw [hval]
    unfold f1Cell
    rw [hRsite, ← hk]
  have hmemj : ∀ j : F1Coord b, j.1.1 ∈ cellPsB k ((recordedBandRule k).idx j0.1.1) := by
    intro j
    obtain ⟨hpr, h3, hQ, hPj⟩ := (f1coord_facts b j).2.1
    obtain ⟨hsj, hij, -⟩ := f1coord_cell j0 j
    rw [← hps, ← f1CellList_eq hsj hij]
    have hmj := siteOf_mem hQ hPj
    rw [hsj, hsite0] at hmj
    have hokj : CellOK (f1SiteRule (siteOf j.1.1))
        (UpperRecords.CompletionData.record k).budget j.1.1 := by
      rw [hsj, hsite0]
      exact recordedBandRule_valid k j.1.1 hmj.1 hmj.2
    exact mem_f1CellList hpr h3 hokj
  have hidx0 : (cellPsB k ((recordedBandRule k).idx j0.1.1)).idxOf j0.1.1 = f1Pos j0.1.1 := by
    unfold f1Pos
    rw [hps]
  have hmk : f1Pos j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1) *
      bnc k ((recordedBandRule k).idx j0.1.1) <
        (cellPsB k ((recordedBandRule k).idx j0.1.1)).length := by
    have h1 := Nat.div_mul_le_self (f1Pos j0.1.1) (bnc k ((recordedBandRule k).idx j0.1.1))
    have h2 := List.idxOf_lt_length_of_mem (hmemj j0)
    rw [hidx0] at h2
    omega
  have hsubl : List.Sublist (cellBlock (cellPsB k ((recordedBandRule k).idx j0.1.1))
      (bnc k ((recordedBandRule k).idx j0.1.1))
      (f1Pos j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1)))
        (cellPsB k ((recordedBandRule k).idx j0.1.1)) :=
    (List.take_sublist _ _).trans (List.drop_sublist _ _)
  refine ⟨?_, ?_⟩
  · rw [hc]
    apply mem_image.mpr
    refine ⟨⟨(recordedBandRule k).idx j0.1.1,
      f1Pos j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1)⟩, ?_, rfl⟩
    rw [mem_sigma, mem_range, mem_range]
    refine ⟨?_, lt_blockCount hk1 hmk⟩
    rw [(rule_eq k).1]
    have hxp : ((bandOf k).1 : ℝ) ≤ j0.1.1 := by exact_mod_cast hband0.1
    have hpY : (j0.1.1 : ℝ) < (bandOf k).2 := by exact_mod_cast hband0.2
    exact (geoIdx_spec (one_le_bandN k) (by linarith [bandX_pos k]) (bandXY k) hxp hpY).2.2.2
  · rw [hc]
    unfold f1DescTermB cellTermB
    simp only [Nat.unpair_pair]
    have hnd : (cellPsB k ((recordedBandRule k).idx j0.1.1)).Nodup := by
      unfold cellPsB Misc.cellList
      exact Finset.sort_nodup _ _
    have hle := f1BlockTerm_le ha d b _ (hnd.sublist hsubl)
      ((Misc.cellList_sorted _ _).sublist hsubl)
      (fun q hq => (Misc.mem_cellPrimes.mp (Misc.mem_cellList.mp (hsubl.subset hq))).1.pos)
      (fun j => by
        obtain ⟨hsj, hij, hmj⟩ := f1coord_cell j0 j
        apply mem_cellBlock_of_idx hk1 (hmemj j)
        have e1 : (cellPsB k ((recordedBandRule k).idx j0.1.1)).idxOf j.1.1 = f1Pos j.1.1 := by
          unfold f1Pos
          rw [f1CellList_eq hsj hij, hps]
        have e2 : bnc k ((recordedBandRule k).idx j0.1.1) = f1Card j.1.1 := by
          rw [f1Card_eq hsj hij, hk]
        rw [e1, e2, hmj, f1Card_eq hsj hij])
    have hhead : (cellBlock (cellPsB k ((recordedBandRule k).idx j0.1.1))
        (bnc k ((recordedBandRule k).idx j0.1.1))
        (f1Pos j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1))).headD 0 =
          Misc.blockStart (cellPsB k ((recordedBandRule k).idx j0.1.1))
            (bnc k ((recordedBandRule k).idx j0.1.1))
            (f1Pos j0.1.1 / bnc k ((recordedBandRule k).idx j0.1.1)) := by
      rw [Misc.cellBlock_eq_cons hk1 hmk]
      rfl
    rw [hhead, neg_div] at hle
    exact hle

/-- **The bridge at `f1Cell`** (`lem:record:block-charge`(i) at a band): the charge of the `f1Cell`
blocks of band `k` is at most M2's `cellCharge` summed over the recorded cells of the band. -/
theorem f1_bandCells_le (k : Fin 310) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    ∑ b ∈ univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inr k),
        BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b) ≤
      ∑ j ∈ range (bandN k), Misc.cellCharge (cellPsB k j) (bnc k j) a ((d : ℝ) / 2) := by
  rw [← f1_sum_descB k a d]
  have hinj : Set.InjOn (fun b : PaperBlock f1Cell => b.val.2)
      (univ.filter fun b : PaperBlock f1Cell => blockSite b = .inr k) := by
    intro x hx y hy h
    have hx' : x.val.1 = .inr k := (mem_filter.mp hx).2
    have hy' : y.val.1 = .inr k := (mem_filter.mp hy).2
    exact PaperBlock.ext (Prod.ext (hx'.trans hy'.symm) h)
  calc ∑ b ∈ univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inr k),
        BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b)
      ≤ ∑ b ∈ univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inr k),
          f1DescTermB k a d b.val.2 :=
        sum_le_sum fun b hb => (f1_block_descB k ha d b (mem_filter.mp hb).2).2
    _ = ∑ c ∈ (univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inr k)).image
          (fun b => b.val.2), f1DescTermB k a d c := (sum_image hinj).symm
    _ ≤ ∑ c ∈ f1DescB k, f1DescTermB k a d c := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro c hc
          obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
          exact (f1_block_descB k ha d b (mem_filter.mp hb).2).1
        · intro c _ _
          exact f1DescTermB_nonneg k a d c

/-- **The band charge at `f1Cell` from `thm:bmor`** (`Target.BMOR`, H2; E2's
`bandCharge_le_bandBound` with the bridge `f1_bandCells_le`). -/
theorem f1_bandCharge_le_bandBound (hB : Target.BMOR) (k : Fin 310) {a : ℝ} (ha : 0 ≤ a)
    (d : ℕ) :
    ∑ b ∈ univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inr k),
        BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b) ≤ bandBound a d k := by
  have hcells : ∑ j ∈ range (bandN k), Misc.cellCharge (cellPsB k j) (bnc k j) a ((d : ℝ) / 2) =
      ∑ j ∈ range (bandN k),
        Misc.cellCharge (Misc.cellList (bx k j) (bx k (j + 1))) (bnc k j) a ((d : ℝ) / 2) := by
    obtain ⟨-, hbot, htop⟩ := rule_eq k
    unfold cellPsB
    rw [hbot, htop]
  refine (f1_bandCells_le k ha d).trans (hcells.le.trans ?_)
  have hx0 : (0 : ℝ) < (bandOf k).1 := by linarith [bandX_pos k]
  have h0 : (4800162889 : ℝ) ≤ bx k 0 := by
    unfold bx
    rw [Misc.cellPoint_zero]
    exact bandX_pos k
  exact Misc.cell_charge_bmor hB (one_le_bandN k) (bx k) h0
    (fun j _ => Misc.cellPoint_mono hx0 (bandXY k).le _ _)
    (fun j hj => Misc.notPrime3_cellPoint (band_even k).1 (band_even k).2 (one_le_bandN k) hj)
    (bnc k) (fun j hj => one_le_bnc k hj) ha (by positivity)

/-- **K2's field 35 (`SA.hUS`, = `SA.hUA`) at `f1Cell` from `thm:bmor`** (E2's
`upperBand_le_bandBound` at `f1Cell`; `lem:record:block-charge`(i), `eq:record:cell-charge`,
`def:record:upper-bands`(b), `prop:record:upper`(ii)). -/
theorem upperBand_le_bandBound (hB : Target.BMOR) (hW : Target.Weil)
    (A : PaperAnalyticInputs f1Cell) (β : Fin 310) (d : ℕ) :
    ∑ b ∈ upperBand (specF hW A) bandIdx β, blockSel bOf b * BlockSpecPaper.blockScale b ^ d ≤
      bandBound targetDecay d β := by
  have hsub : upperBand (specF hW A) bandIdx β ⊆
      univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inr β) := by
    intro b hb
    unfold ComparisonLawPaper.upperBand at hb
    rw [mem_filter, mem_filter] at hb
    obtain ⟨⟨-, hup⟩, hβ⟩ := hb
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [blockSite_of_upper b hup, hβ]
  calc ∑ b ∈ upperBand (specF hW A) bandIdx β, blockSel bOf b * BlockSpecPaper.blockScale b ^ d
      = ∑ b ∈ upperBand (specF hW A) bandIdx β, BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf f1Cell)) targetDecay (.inr b) :=
        sum_congr rfl fun b _ => mul_comm _ _
    _ ≤ ∑ b ∈ univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inr β),
          BlockSpecPaper.blockScale b ^ d *
            paperSelAt (paperAtomMap (paperBlockOf f1Cell)) targetDecay (.inr b) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro b _ _
        refine mul_nonneg (pow_nonneg ?_ d)
          (zero_le_one.trans (one_le_paperSelAt _ targetDecay_nonneg _))
        unfold BlockSpecPaper.blockScale
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ ≤ bandBound targetDecay d β := f1_bandCharge_le_bandBound hB β targetDecay_nonneg d

end Sarkozy.MainFinalF1
