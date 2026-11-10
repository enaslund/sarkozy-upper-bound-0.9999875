module

public import Sarkozy.AnalyticCells.F1Cell
public import Sarkozy.PaperNumbers.Charge

@[expose] public section

/-!
# The block charges of the F1 partition (`lem:record:block-charge`, closing sentence)

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`.

**`f1_blockCharge_le`**: the charge `b_d(i) = ∑_{𝔅 ⊆ piece i} b_𝔅^{-d/2} q_𝔅^{2a}` of the F1 blocks
of middle piece `i` is at most M2's `pieceCharge` of `f1Piece i`, the piece with no exact part and
the geometric cells of `[f1X i, Y_i)` (`f1N i` cells, `n_j = ⌊570/log x_{j+1}⌋`). The proof is N1's
`blockCharge_le_pieceCharge` without the exact branch: each block maps injectively, by its cell
value `⟨j, m⟩`, to the `m`-th block of cell `j`, which contains its primes.
-/

open Finset

namespace Sarkozy.AnalyticCells

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.PaperNumbers Sarkozy.MainTarget

/-- The start of the cells of piece `i`: `X_i` for `i ≤ 28`, `max(X_i, X_Ch)` above. -/
def f1XN (i : Fin 33) : ℕ := if i.val < 29 then pieceStart i else max (pieceStart i) XCh

/-- The number of cells of piece `i`. -/
noncomputable def f1N (i : Fin 33) : ℕ :=
  if i.val < 29 then nF1 i else cellCount (cellStart i) (pieceStop i)

theorem f1Rule_eq (i : Fin 33) :
    f1Rule i = geoRule (f1XN i : ℝ) (pieceStop i : ℝ) (f1N i) (middleBudget : ℝ) := by
  unfold f1Rule f1XN f1N
  split_ifs with h
  · rfl
  · change geoRule (cellStart i) (pieceStop i) (cellCount (cellStart i) (pieceStop i))
      (middleBudget : ℝ) = _
    rw [cellStart_eq]

/-- **The F1 partition data of piece `i`** in M2's form: no exact part, the cells of `f1Rule i`. -/
noncomputable def f1Piece (i : Fin 33) : Misc.MiddlePiece where
  parts := []
  n := f1N i
  x := cellPoint (f1XN i : ℝ) (pieceStop i : ℝ) (f1N i)
  nc := cellCard (middleBudget : ℝ) (f1XN i : ℝ) (pieceStop i : ℝ) (f1N i)

theorem f1XN_facts : ∀ i : Fin 33, Even (f1XN i) ∧ Even (pieceStop i) ∧ 1 < f1XN i ∧
    f1XN i < pieceStop i ∧ pieceStart i ≤ f1XN i := by decide +kernel

theorem f1XN_le {i : Fin 33} {p : ℕ} (h1 : pieceStart i ≤ p) : f1XN i ≤ p := by
  unfold f1XN
  split_ifs with h
  · exact h1
  · exact max_le h1 ((pieceStart_ge_XCh i (by omega)).trans h1)

theorem one_le_f1N (i : Fin 33) : 1 ≤ f1N i := by
  unfold f1N
  split_ifs with h
  · exact nF1_pos i h
  · have h4 := f1XN_facts i
    have hx : (0 : ℝ) < cellStart i := lt_of_lt_of_le (by norm_num [XCh]) (le_max_right _ _)
    have hxY : cellStart i < pieceStop i := by
      have : f1XN i = max (pieceStart i) XCh := by unfold f1XN; simp [h]
      rw [cellStart_eq, ← this]
      exact_mod_cast h4.2.2.2.1
    exact one_le_cellCount hx hxY

/-! ## The term of one block -/

theorem f1SelAt_block (a : ℝ) (b : PaperBlock f1Cell) :
    paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b) =
      ∏ j : F1Coord b, (j.1.1 : ℝ) ^ (2 * a) := by
  rw [paperSelAt_eq]
  unfold BlockAnchor.blockSel
  apply Finset.prod_congr rfl
  intro j _
  have hj : j.1.1 % 4 ≠ 1 := (blockOf_of_coord j).1
  unfold BlockAnchor.coordSel paperEP paperPP
  simp only [hj, ↓reduceIte]

theorem f1BlockScale_pow (b : PaperBlock f1Cell) (d : ℕ) :
    BlockSpecPaper.blockScale b ^ d = (blockLeast b : ℝ) ^ (-(d : ℝ) / 2) := by
  unfold BlockSpecPaper.blockScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (blockLeast_pos b).le]
  congr 1
  ring

/-- The term of a block is at most the term of a sorted list of positive primes containing it. -/
theorem f1BlockTerm_le {a : ℝ} (ha : 0 ≤ a) (d : ℕ) (b : PaperBlock f1Cell) (S : List ℕ)
    (hS : S.Nodup) (hsort : S.Pairwise (· < ·)) (hpos : ∀ q ∈ S, 0 < q)
    (hsub : ∀ j : F1Coord b, j.1.1 ∈ S) :
    BlockSpecPaper.blockScale b ^ d * paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b) ≤
      ((S.prod : ℕ) : ℝ) ^ (2 * a) * ((S.headD 0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := by
  rw [f1BlockScale_pow, f1SelAt_block]
  have hinjP : Function.Injective fun j : F1Coord b => j.1.1 :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hprod : ∏ j : F1Coord b, (j.1.1 : ℝ) ^ (2 * a) ≤ ((S.prod : ℕ) : ℝ) ^ (2 * a) := by
    rw [Real.finsetProd_rpow _ _ (fun j _ => Nat.cast_nonneg _)]
    apply Real.rpow_le_rpow (Finset.prod_nonneg fun j _ => Nat.cast_nonneg _) _ (by linarith)
    have himg : ∏ j : F1Coord b, j.1.1 = ∏ q ∈ univ.image (fun j : F1Coord b => j.1.1), q :=
      (prod_image (f := fun q => q) fun x _ y _ h => hinjP h).symm
    have hdvd : (∏ j : F1Coord b, j.1.1) ∣ S.prod := by
      rw [himg]
      have hS' : S.prod = ∏ q ∈ S.toFinset, q := by
        rw [List.prod_toFinset (fun q => q) hS, List.map_id']
      rw [hS']
      exact prod_dvd_prod_of_subset _ _ _ fun q hq => by
        obtain ⟨j, -, rfl⟩ := mem_image.mp hq
        exact List.mem_toFinset.mpr (hsub j)
    have hSpos : 0 < S.prod := List.prod_pos fun q hq => hpos q hq
    have := Nat.le_of_dvd hSpos hdvd
    rw [← Nat.cast_prod]
    exact_mod_cast this
  obtain ⟨j0, hj0⟩ := blockLeast_mem b
  have hp0 : blockPrimes (paperBlockOf f1Cell) b j0 = j0.1.1 := (f1coord_facts b j0).1
  have hhead : S.headD 0 ≤ blockLeast b := by
    rw [← hj0, hp0]
    have hm := hsub j0
    cases S with
    | nil => simp at hm
    | cons x l =>
        simp only [List.headD_cons]
        rcases List.mem_cons.mp hm with h | h
        · exact h.symm.le
        · exact ((List.pairwise_cons.mp hsort).1 _ h).le
  have hhead0 : 0 < S.headD 0 := by
    have hm := hsub j0
    cases S with
    | nil => simp at hm
    | cons x l =>
        simp only [List.headD_cons]
        exact hpos x List.mem_cons_self
  have hleast : (blockLeast b : ℝ) ^ (-(d : ℝ) / 2) ≤ ((S.headD 0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hhead0) (by exact_mod_cast hhead)
      (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  rw [mul_comm]
  exact mul_le_mul hprod hleast (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-! ## The descriptors -/

/-- The primes `≡ 3 (mod 4)` of cell `j` of piece `i`. -/
noncomputable def f1CellPs (i : Fin 33) (j : ℕ) : List ℕ :=
  Misc.cellList ((f1Piece i).x j) ((f1Piece i).x (j + 1))

/-- M2's term of the `m`-th block of cell `j` of piece `i`. -/
noncomputable def f1CellTerm (i : Fin 33) (a : ℝ) (d j m : ℕ) : ℝ :=
  ((Misc.blockProd (f1CellPs i j) ((f1Piece i).nc j) m : ℕ) : ℝ) ^ (2 * a) *
    ((Misc.blockStart (f1CellPs i j) ((f1Piece i).nc j) m : ℕ) : ℝ) ^ (-((d : ℝ) / 2))

/-- The term of a descriptor `⟨j, m⟩`. -/
noncomputable def f1DescTerm (i : Fin 33) (a : ℝ) (d c : ℕ) : ℝ :=
  f1CellTerm i a d (Nat.unpair c).1 (Nat.unpair c).2

/-- The descriptors of the blocks of the cells of piece `i`. -/
noncomputable def f1Desc (i : Fin 33) : Finset ℕ :=
  ((range (f1Piece i).n).sigma fun j =>
      range (Misc.blockCount (f1CellPs i j).length ((f1Piece i).nc j))).image
    fun x => Nat.pair x.1 x.2

theorem f1DescTerm_nonneg (i : Fin 33) (a : ℝ) (d c : ℕ) : 0 ≤ f1DescTerm i a d c := by
  unfold f1DescTerm f1CellTerm
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem f1_pair_inj {s : Finset (Σ _ : ℕ, ℕ)} :
    Set.InjOn (fun x : (Σ _ : ℕ, ℕ) => Nat.pair x.1 x.2) s := by
  intro x _ y _ h
  obtain ⟨h2, h3⟩ := Nat.pair_eq_pair.mp h
  exact Sigma.ext h2 (heq_of_eq h3)

theorem f1_sum_desc (i : Fin 33) (a : ℝ) (d : ℕ) :
    ∑ c ∈ f1Desc i, f1DescTerm i a d c = Misc.pieceCharge binU (f1Piece i) a d := by
  unfold f1Desc Misc.pieceCharge
  rw [sum_image f1_pair_inj, sum_sigma]
  simp only [f1Piece, List.map_nil, List.sum_nil, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  unfold Misc.cellCharge
  simp only [f1DescTerm, Nat.unpair_pair]
  rfl

/-- **The descriptor of a block of piece `i`.** -/
theorem f1_block_desc (i : Fin 33) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) (b : PaperBlock f1Cell)
    (hs : blockSite b = .inl i) :
    b.val.2 ∈ f1Desc i ∧
      BlockSpecPaper.blockScale b ^ d * paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b) ≤
        f1DescTerm i a d b.val.2 := by
  obtain ⟨j0⟩ := blockIdx_nonempty b
  have hlab := (f1coord_facts b j0).2.2
  have hsite0 : siteOf j0.1.1 = .inl i := by
    have : blockSite b = siteOf j0.1.1 := by unfold blockSite; rw [hlab]
    rw [← this, hs]
  have hval : b.val.2 = f1Cell j0.1.1 := by rw [hlab]
  obtain ⟨hpr0, h30, hQ0, hP0⟩ := (f1coord_facts b j0).2.1
  have hmem0 := siteOf_mem hQ0 hP0
  rw [hsite0] at hmem0
  have hpiece0 : pieceStart i ≤ j0.1.1 ∧ j0.1.1 < pieceStop i := hmem0
  set R := geoRule (f1XN i : ℝ) (pieceStop i : ℝ) (f1N i) (middleBudget : ℝ) with hR
  have hRsite : f1SiteRule (siteOf j0.1.1) = R := by rw [hsite0]; exact f1Rule_eq i
  have hok0 : CellOK R (middleBudget : ℝ) j0.1.1 := by
    have := f1Rule_valid i hpiece0.1 hpiece0.2
    rwa [f1Rule_eq] at this
  set J := R.idx j0.1.1 with hJdef
  have hps : f1CellList j0.1.1 = f1CellPs i J := by
    unfold f1CellList f1CellPs
    rw [hRsite]
    rfl
  have hk : f1Card j0.1.1 = (f1Piece i).nc J := by
    unfold f1Card
    rw [hRsite]
    rfl
  have hk1 : 1 ≤ (f1Piece i).nc J := hok0.2.2.1
  have hc : b.val.2 = Nat.pair J (f1Pos j0.1.1 / (f1Piece i).nc J) := by
    rw [hval]
    unfold f1Cell
    rw [hRsite, hk]
  have hmemj : ∀ j : F1Coord b, j.1.1 ∈ f1CellPs i J := by
    intro j
    obtain ⟨hpr, h3, hQ, hPj⟩ := (f1coord_facts b j).2.1
    obtain ⟨hsj, hij, -⟩ := f1coord_cell j0 j
    rw [← hps, ← f1CellList_eq hsj hij]
    have hmj := siteOf_mem hQ hPj
    rw [hsj, hsite0] at hmj
    have hokj : CellOK (f1SiteRule (siteOf j.1.1)) (middleBudget : ℝ) j.1.1 := by
      rw [hsj, hsite0]
      exact f1Rule_valid i hmj.1 hmj.2
    exact mem_f1CellList hpr h3 hokj
  have hidx0 : (f1CellPs i J).idxOf j0.1.1 = f1Pos j0.1.1 := by
    unfold f1Pos
    rw [hps]
  have hmk : f1Pos j0.1.1 / (f1Piece i).nc J * (f1Piece i).nc J < (f1CellPs i J).length := by
    have h1 := Nat.div_mul_le_self (f1Pos j0.1.1) ((f1Piece i).nc J)
    have h2 := List.idxOf_lt_length_of_mem (hmemj j0)
    rw [hidx0] at h2
    omega
  have hsubl : List.Sublist (cellBlock (f1CellPs i J) ((f1Piece i).nc J)
      (f1Pos j0.1.1 / (f1Piece i).nc J)) (f1CellPs i J) :=
    (List.take_sublist _ _).trans (List.drop_sublist _ _)
  refine ⟨?_, ?_⟩
  · rw [hc]
    apply mem_image.mpr
    refine ⟨⟨J, f1Pos j0.1.1 / (f1Piece i).nc J⟩, ?_, rfl⟩
    rw [mem_sigma, mem_range, mem_range]
    refine ⟨?_, lt_blockCount hk1 hmk⟩
    obtain ⟨-, -, h1, h2, -⟩ := f1XN_facts i
    have hx0 : (0 : ℝ) < f1XN i := by
      have : 0 < f1XN i := by omega
      exact_mod_cast this
    have hxY : (f1XN i : ℝ) < pieceStop i := by exact_mod_cast h2
    have hxp : (f1XN i : ℝ) ≤ j0.1.1 := by exact_mod_cast f1XN_le hpiece0.1
    have hpY : (j0.1.1 : ℝ) < pieceStop i := by exact_mod_cast hpiece0.2
    have hJ' : J = geoIdx (f1XN i : ℝ) (pieceStop i : ℝ) (f1N i) j0.1.1 := rfl
    rw [hJ']
    exact (geoIdx_spec (one_le_f1N i) hx0 hxY hxp hpY).2.2.2
  · rw [hc]
    unfold f1DescTerm f1CellTerm
    simp only [Nat.unpair_pair]
    have hnd : (f1CellPs i J).Nodup := by
      unfold f1CellPs Misc.cellList
      exact Finset.sort_nodup _ _
    have hle := f1BlockTerm_le ha d b _ (hnd.sublist hsubl)
      ((Misc.cellList_sorted _ _).sublist hsubl)
      (fun q hq => (Misc.mem_cellPrimes.mp (Misc.mem_cellList.mp (hsubl.subset hq))).1.pos)
      (fun j => by
        obtain ⟨hsj, hij, hmj⟩ := f1coord_cell j0 j
        apply mem_cellBlock_of_idx hk1 (hmemj j)
        have e1 : (f1CellPs i J).idxOf j.1.1 = f1Pos j.1.1 := by
          unfold f1Pos
          rw [f1CellList_eq hsj hij, hps]
        have e2 : (f1Piece i).nc J = f1Card j.1.1 := by
          rw [f1Card_eq hsj hij, hk]
        rw [e1, e2, hmj, f1Card_eq hsj hij])
    have hhead : (cellBlock (f1CellPs i J) ((f1Piece i).nc J)
        (f1Pos j0.1.1 / (f1Piece i).nc J)).headD 0 =
          Misc.blockStart (f1CellPs i J) ((f1Piece i).nc J) (f1Pos j0.1.1 / (f1Piece i).nc J) := by
      rw [Misc.cellBlock_eq_cons hk1 hmk]
      rfl
    rw [hhead, neg_div] at hle
    exact hle

/-- **`lem:record:block-charge` at the F1 partition**: `b_d(i) ≤ pieceCharge (f1Piece i)`. -/
theorem f1_blockCharge_le (i : Fin 33) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    blockCharge (fun b => paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b)) d i ≤
      Misc.pieceCharge binU (f1Piece i) a d := by
  rw [← f1_sum_desc i a d]
  unfold blockCharge
  have hinj : Set.InjOn (fun b : PaperBlock f1Cell => b.val.2)
      (univ.filter fun b : PaperBlock f1Cell => blockSite b = .inl i) := by
    intro x hx y hy h
    have hx' : x.val.1 = .inl i := (mem_filter.mp hx).2
    have hy' : y.val.1 = .inl i := (mem_filter.mp hy).2
    exact PaperBlock.ext (Prod.ext (hx'.trans hy'.symm) h)
  calc ∑ b ∈ univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inl i),
        BlockSpecPaper.blockScale b ^ d * paperSelAt (paperAtomMap (paperBlockOf f1Cell)) a (.inr b)
      ≤ ∑ b ∈ univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inl i),
          f1DescTerm i a d b.val.2 :=
        sum_le_sum fun b hb => (f1_block_desc i ha d b (mem_filter.mp hb).2).2
    _ = ∑ c ∈ (univ.filter (fun b : PaperBlock f1Cell => blockSite b = .inl i)).image
          (fun b => b.val.2), f1DescTerm i a d c := (sum_image hinj).symm
    _ ≤ ∑ c ∈ f1Desc i, f1DescTerm i a d c := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro c hc
          obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
          exact (f1_block_desc i ha d b (mem_filter.mp hb).2).1
        · intro c _ _
          exact f1DescTerm_nonneg i a d c

end Sarkozy.AnalyticCells
