module

public import Sarkozy.PaperNumbers.Budget
public import Sarkozy.Misc.PieceCharge
public import Sarkozy.BlockSpecPaper.Charges

@[expose] public section

/-!
# The block charges of the paper's partition (`lem:record:block-charge`)

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge` (closing sentence).

B1's `hB_of_blockCharges` reduces `hB` to bounds on the per-piece block charges
`b_d(i) = ∑_{𝔅 ⊆ piece i} b_𝔅^{-d/2} q_𝔅^{2a}` (`BlockSpecPaper.blockCharge`), and M2's
`piece_charge_le_bmor` bounds the charge `pieceCharge` of a piece given by its partition data
(`Misc.MiddlePiece`). This file connects the two for the paper's partition:

* `paperPiece i`: the partition data of piece `i` in M2's form: its parts below `X_Ch` (the lists
  `partList k` of the parts `k` inside the piece, `partsOf i`), and its cells above `X_Ch`
  (`x_j = cellPoint`, `n_j = cellCard`, `𝗇 = cellCount` or `0`);
* **`blockCharge_le_pieceCharge`**: `b_d(i) ≤ pieceCharge 𝔲 (paperPiece i) a d` for `a ≥ 0`. Every
  block of the paper's rule in piece `i` lies inside one greedy block of a part, or inside one
  `cellBlock` of a cell (`cellPos`), and distinct blocks get distinct greedy or cell blocks (they
  have distinct labels); the terms are compared through `q_𝔅 ∣ ∏_{p ∈ block} p` and
  `b_𝔅 ≥` the first prime of the block;
* **`blockCharge_le_bmor`**: with `thm:bmor` (`Target.BMOR`, H2), `b_d(i)` is at most M2's
  explicit bound: the sum over the parts of `lem:record:block-charge`(ii) (the price buckets of the
  greedy blocks, `exactBound`) plus `eq:record:cell-charge` with `s = d/2` over the cells
  (`cellBound`, error `𝖾_{x_0} = 2411/(5·10⁶ log x_0)`).

The bound is in terms of the true greedy blocks of the parts (every prime `≡ 3 (mod 4)` below
`X_Ch`): `exactBound` is the quantity the paper evaluates from the authenticated histogram
(`cert:record:middle-price`(b)). Its numerical value is not checked here.
-/

open Finset

namespace Sarkozy.PaperNumbers

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.MainTarget

/-! ## The partition data of a piece in M2's form -/

/-- The parts lying in piece `i`. -/
def partsIn (i : Fin 33) : List ℕ :=
  (List.range 35).filter fun k => decide (pieceStart i ≤ partE k ∧ partE (k + 1) ≤ pieceStop i)

/-- The parts lying in piece `i` that contain a prime `≡ 3 (mod 4)`. -/
noncomputable def partsOf (i : Fin 33) : List ℕ :=
  (partsIn i).filter fun k => !(partList k).isEmpty

theorem partsOf_nodup (i : Fin 33) : (partsOf i).Nodup :=
  (List.nodup_range.filter _).filter _

/-- The start `max(X_i, X_Ch)` of the cells of piece `i`. -/
noncomputable def cellStart (i : Fin 33) : ℝ := max (pieceStart i : ℝ) XCh

/-- The number of cells of piece `i` (`0` if the piece ends below `X_Ch`). -/
noncomputable def cellNum (i : Fin 33) : ℕ :=
  if XCh < pieceStop i then cellCount (cellStart i) (pieceStop i) else 0

/-- **The partition data of piece `i`** in M2's form (`def:record:exact-blocks`(c), (d)). -/
noncomputable def paperPiece (i : Fin 33) : Misc.MiddlePiece where
  parts := (partsOf i).map partList
  n := cellNum i
  x := cellPoint (cellStart i) (pieceStop i) (cellCount (cellStart i) (pieceStop i))
  nc := cellCard middleBudget (cellStart i) (pieceStop i) (cellCount (cellStart i) (pieceStop i))

/-- **A part meeting a piece lies in it** (every piece endpoint below `X_Ch` is a threshold
point, `pieceEnds_thresholds`). -/
theorem part_in_piece : ∀ i : Fin 33, ∀ k < 35, partE k < pieceStop i →
    pieceStart i < partE (k + 1) → pieceStart i ≤ partE k ∧ partE (k + 1) ≤ pieceStop i := by
  decide +kernel

theorem partList_sorted (k : ℕ) : (partList k).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

/-! ## Lists -/

theorem list_sum_eq_sum_range {α : Type} (l : List α) (g : α → ℝ) (x : α) :
    (l.map g).sum = ∑ m ∈ range l.length, g (l.getD m x) := by
  induction l with
  | nil => simp
  | cons y l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-- An element of a list at position `m k + t`, `t < k`, lies in the `m`-th block of `k`. -/
theorem mem_cellBlock_of_idx {ps : List ℕ} {k m p : ℕ} (hk : 1 ≤ k) (hp : p ∈ ps)
    (hm : ps.idxOf p / k = m) : p ∈ cellBlock ps k m := by
  have hlt : ps.idxOf p < ps.length := List.idxOf_lt_length_of_mem hp
  have hget : ps[ps.idxOf p] = p := List.getElem_idxOf hlt
  have hdm := Nat.div_add_mod (ps.idxOf p) k
  rw [hm] at hdm
  have ht : ps.idxOf p % k < k := Nat.mod_lt _ hk
  have hmk : m * k + ps.idxOf p % k < ps.length := by
    rw [mul_comm]; omega
  have hlen : ps.idxOf p % k < ((ps.drop (m * k)).take k).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have : ((ps.drop (m * k)).take k)[ps.idxOf p % k] = p := by
    rw [List.getElem_take, List.getElem_drop]
    have he : m * k + ps.idxOf p % k = ps.idxOf p := by rw [mul_comm]; omega
    simp only [he]
    exact hget
  unfold cellBlock
  rw [← this]
  exact List.getElem_mem hlen

/-! ## The term of one block -/

variable {U : Fin 310 → CellRule}

/-- The selection factor of a block: `q_𝔅^{2a} = ∏_{p ∈ 𝔅} p^{2a}`. -/
theorem paperSelAt_block (a : ℝ) (b : PaperBlock (paperCellWith U)) :
    paperSelAt (paperAtomMap (paperBlockOf (paperCellWith U))) a (.inr b) =
      ∏ j : Coord U b, (j.1.1 : ℝ) ^ (2 * a) := by
  rw [paperSelAt_eq]
  unfold BlockAnchor.blockSel
  apply Finset.prod_congr rfl
  intro j _
  have hj : j.1.1 % 4 ≠ 1 := (blockOf_of_coord j).1
  unfold BlockAnchor.coordSel paperEP paperPP
  simp only [hj, ↓reduceIte]

theorem blockScale_pow (b : PaperBlock (paperCellWith U)) (d : ℕ) :
    BlockSpecPaper.blockScale b ^ d = (blockLeast b : ℝ) ^ (-(d : ℝ) / 2) := by
  unfold BlockSpecPaper.blockScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (blockLeast_pos b).le]
  congr 1
  ring

/-- **The term of a block is at most the term of a list containing it**: for a sorted list `S` of
positive primes containing every prime of the block, `b_𝔅^{-d/2} q_𝔅^{2a} ≤ (∏ S)^{2a} (S₀)^{-d/2}`
with `S₀` the first element of `S`. -/
theorem blockTerm_le {a : ℝ} (ha : 0 ≤ a) (d : ℕ) (b : PaperBlock (paperCellWith U)) (S : List ℕ)
    (hS : S.Nodup) (hsort : S.Pairwise (· < ·)) (hpos : ∀ q ∈ S, 0 < q)
    (hsub : ∀ j : Coord U b, j.1.1 ∈ S) :
    BlockSpecPaper.blockScale b ^ d *
      paperSelAt (paperAtomMap (paperBlockOf (paperCellWith U))) a (.inr b) ≤
      ((S.prod : ℕ) : ℝ) ^ (2 * a) * ((S.headD 0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := by
  rw [blockScale_pow, paperSelAt_block]
  have hinjP : Function.Injective fun j : Coord U b => j.1.1 :=
    fun x y h => Subtype.ext (Subtype.ext h)
  -- the product
  have hprod : ∏ j : Coord U b, (j.1.1 : ℝ) ^ (2 * a) ≤ ((S.prod : ℕ) : ℝ) ^ (2 * a) := by
    rw [Real.finsetProd_rpow _ _ (fun j _ => Nat.cast_nonneg _)]
    apply Real.rpow_le_rpow (Finset.prod_nonneg fun j _ => Nat.cast_nonneg _) _ (by linarith)
    have himg : ∏ j : Coord U b, j.1.1 = ∏ q ∈ univ.image (fun j : Coord U b => j.1.1), q :=
      (prod_image (f := fun q => q) fun x _ y _ h => hinjP h).symm
    have hdvd : (∏ j : Coord U b, j.1.1) ∣ S.prod := by
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
  -- the least prime
  obtain ⟨j0, hj0⟩ := blockLeast_mem b
  have hp0 : blockPrimes (paperBlockOf (paperCellWith U)) b j0 = j0.1.1 := (coord_facts b j0).1
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

/-! ## The descriptors of the blocks of a piece -/

/-- The primes `≡ 3 (mod 4)` of cell `j` of piece `i`, in increasing order. -/
noncomputable def cellPs (i : Fin 33) (j : ℕ) : List ℕ :=
  Misc.cellList ((paperPiece i).x j) ((paperPiece i).x (j + 1))

/-- M2's term of the `m`-th greedy block of part `k`. -/
noncomputable def exTerm (a : ℝ) (d k m : ℕ) : ℝ := Misc.exactTerm a d ((greedyOf k).getD m [])

/-- M2's term of the `m`-th block of cell `j` of piece `i`. -/
noncomputable def cellTerm (i : Fin 33) (a : ℝ) (d j m : ℕ) : ℝ :=
  ((Misc.blockProd (cellPs i j) ((paperPiece i).nc j) m : ℕ) : ℝ) ^ (2 * a) *
    ((Misc.blockStart (cellPs i j) ((paperPiece i).nc j) m : ℕ) : ℝ) ^ (-((d : ℝ) / 2))

/-- The term of a descriptor (a cell value `⟨0, ⟨k, m⟩⟩` or `⟨1, ⟨j, m⟩⟩`). -/
noncomputable def descTerm (i : Fin 33) (a : ℝ) (d c : ℕ) : ℝ :=
  if (Nat.unpair c).1 = 0 then
    exTerm a d (Nat.unpair (Nat.unpair c).2).1 (Nat.unpair (Nat.unpair c).2).2
  else cellTerm i a d (Nat.unpair (Nat.unpair c).2).1 (Nat.unpair (Nat.unpair c).2).2

/-- The descriptors of the greedy blocks of the parts of piece `i`. -/
noncomputable def exDesc (i : Fin 33) : Finset ℕ :=
  ((partsOf i).toFinset.sigma fun k => range (greedyOf k).length).image
    fun x => Nat.pair 0 (Nat.pair x.1 x.2)

/-- The descriptors of the blocks of the cells of piece `i`. -/
noncomputable def cellDesc (i : Fin 33) : Finset ℕ :=
  ((range (cellNum i)).sigma fun j =>
      range (Misc.blockCount (cellPs i j).length ((paperPiece i).nc j))).image
    fun x => Nat.pair 1 (Nat.pair x.1 x.2)

theorem descTerm_nonneg (i : Fin 33) (a : ℝ) (d c : ℕ) : 0 ≤ descTerm i a d c := by
  unfold descTerm exTerm cellTerm Misc.exactTerm
  split_ifs <;> exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem pair_sigma_inj (t : ℕ) {s : Finset (Σ _ : ℕ, ℕ)} :
    Set.InjOn (fun x : (Σ _ : ℕ, ℕ) => Nat.pair t (Nat.pair x.1 x.2)) s := by
  intro x _ y _ h
  have h1 := (Nat.pair_eq_pair.mp h).2
  obtain ⟨h2, h3⟩ := Nat.pair_eq_pair.mp h1
  exact Sigma.ext h2 (heq_of_eq h3)

/-- **The descriptor sum is M2's charge of the piece.** -/
theorem sum_desc (i : Fin 33) (a : ℝ) (d : ℕ) :
    ∑ c ∈ exDesc i ∪ cellDesc i, descTerm i a d c = Misc.pieceCharge binU (paperPiece i) a d := by
  have hdisj : Disjoint (exDesc i) (cellDesc i) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    obtain ⟨x, -, rfl⟩ := mem_image.mp h1
    obtain ⟨y, -, hy⟩ := mem_image.mp h2
    exact absurd (Nat.pair_eq_pair.mp hy).1 (by norm_num)
  rw [sum_union hdisj]
  unfold exDesc cellDesc Misc.pieceCharge
  rw [sum_image (pair_sigma_inj 0), sum_image (pair_sigma_inj 1), sum_sigma, sum_sigma]
  congr 1
  · simp only [descTerm, Nat.unpair_pair, ↓reduceIte]
    have hin : ∀ k, ∑ m ∈ range (greedyOf k).length, exTerm a d k m =
        ((greedyOf k).map (Misc.exactTerm a d)).sum := fun k =>
      (list_sum_eq_sum_range (greedyOf k) (Misc.exactTerm a d) []).symm
    simp only [hin]
    rw [List.sum_toFinset _ (partsOf_nodup i)]
    simp only [paperPiece, List.map_map]
    rfl
  · simp only [descTerm, Nat.unpair_pair, one_ne_zero, ↓reduceIte]
    rfl

/-! ## Each block of a piece has a descriptor -/

theorem lt_blockCount {l k m : ℕ} (hk : 1 ≤ k) (h : m * k < l) : m < Misc.blockCount l k := by
  unfold Misc.blockCount
  have h1 : (m + 1) * k ≤ l + k - 1 := by
    have : (m + 1) * k = m * k + k := by ring
    omega
  have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr h1
  omega

/-- **The descriptor of a block of piece `i`**: its cell value lies in the descriptor set, and its
term is at most the descriptor's term. -/
theorem block_desc (i : Fin 33) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) (b : PaperBlock (paperCellWith U))
    (hs : blockSite b = .inl i) :
    b.val.2 ∈ exDesc i ∪ cellDesc i ∧
      BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf (paperCellWith U))) a (.inr b) ≤
        descTerm i a d b.val.2 := by
  obtain ⟨j0⟩ := blockIdx_nonempty b
  have hlab := (coord_facts b j0).2.2
  have hsite0 : siteOf j0.1.1 = .inl i := by
    have : blockSite b = siteOf j0.1.1 := by unfold blockSite; rw [hlab]
    rw [← this, hs]
  have hval : b.val.2 = paperCellWith U j0.1.1 := by rw [hlab]
  obtain ⟨hpr0, h30, hQ0, hP0⟩ := (coord_facts b j0).2.1
  have hmem0 := siteOf_mem hQ0 hP0
  rw [hsite0] at hmem0
  have hpiece0 : pieceStart i ≤ j0.1.1 ∧ j0.1.1 < pieceStop i := hmem0
  by_cases hX0 : j0.1.1 < XCh
  · -- an exact block
    have hc : b.val.2 = Nat.pair 0 (Nat.pair (partOf j0.1.1) (greedyIdx j0.1.1)) := by
      rw [hval]
      unfold paperCellWith
      simp only [hX0, ↓reduceIte]
    have hpart := mem_partList_partOf hpr0 h30 hQ0 hX0
    obtain ⟨hlen, -⟩ := greedyIdx_spec hpart
    have hKlt : partOf j0.1.1 < 35 := partOf_lt hQ0 hX0
    have hBG : (greedyOf (partOf j0.1.1)).getD (greedyIdx j0.1.1) [] ∈
        greedyOf (partOf j0.1.1) := by
      rw [List.getD_eq_getElem _ _ hlen]
      exact List.getElem_mem hlen
    have hsubl : List.Sublist ((greedyOf (partOf j0.1.1)).getD (greedyIdx j0.1.1) [])
        (partList (partOf j0.1.1)) := by
      have := List.sublist_flatten_of_mem hBG
      unfold greedyOf at this
      rw [greedyBlocks_flatten] at this
      exact this
    refine ⟨?_, ?_⟩
    · rw [hc]
      apply mem_union_left
      apply mem_image.mpr
      refine ⟨⟨partOf j0.1.1, greedyIdx j0.1.1⟩, ?_, rfl⟩
      rw [mem_sigma]
      refine ⟨?_, mem_range.mpr hlen⟩
      rw [List.mem_toFinset]
      unfold partsOf partsIn
      have hsp := partOf_spec hQ0 hX0
      have hin := part_in_piece i _ hKlt (lt_of_le_of_lt hsp.1 hpiece0.2)
        (lt_of_le_of_lt hpiece0.1 hsp.2)
      rw [List.mem_filter, List.mem_filter, List.mem_range]
      refine ⟨⟨hKlt, by simpa using hin⟩, ?_⟩
      have hne : partList (partOf j0.1.1) ≠ [] := List.ne_nil_of_mem hpart
      simpa [List.isEmpty_iff] using hne
    · rw [hc]
      unfold descTerm exTerm
      simp only [Nat.unpair_pair, ↓reduceIte]
      unfold Misc.exactTerm
      refine blockTerm_le ha d b _ ((partList_nodup _).sublist hsubl)
        ((partList_sorted _).sublist hsubl) (fun q hq => (mem_partList.mp (hsubl.subset hq)).1.pos)
        fun j => ?_
      obtain ⟨hpr, h3, hQ, -⟩ := (coord_facts b j).2.1
      obtain ⟨hXj, hK, hm⟩ := coord_exact hX0 j
      have := mem_greedy_getD (mem_partList_partOf hpr h3 hQ hXj)
      rw [hK, hm] at this
      exact this
  · -- a block of a cell
    have hX0' : XCh ≤ j0.1.1 := not_lt.mp hX0
    have hok0 : CellOK (middleRule i) (middleBudget : ℝ) j0.1.1 :=
      middleRule_valid i hX0' hpiece0.1 hpiece0.2
    have hJ : (siteRule U (siteOf j0.1.1)).idx j0.1.1 = (middleRule i).idx j0.1.1 := by
      rw [hsite0]; rfl
    have hps : cellListOf U j0.1.1 = cellPs i ((middleRule i).idx j0.1.1) := by
      unfold cellListOf
      rw [hsite0]
      rfl
    have hk : cellCardOf U j0.1.1 = (paperPiece i).nc ((middleRule i).idx j0.1.1) := by
      unfold cellCardOf
      rw [hsite0]
      rfl
    have hk1 : 1 ≤ (paperPiece i).nc ((middleRule i).idx j0.1.1) := hok0.2.2.1
    have hc : b.val.2 = Nat.pair 1 (Nat.pair ((middleRule i).idx j0.1.1)
        (cellPos U j0.1.1 / (paperPiece i).nc ((middleRule i).idx j0.1.1))) := by
      rw [hval]
      unfold paperCellWith
      simp only [hX0, ↓reduceIte]
      rw [hJ, hk]
    -- the coordinates lie in the cell list
    have hmemj : ∀ j : Coord U b, j.1.1 ∈ cellPs i ((middleRule i).idx j0.1.1) := by
      intro j
      obtain ⟨hpr, h3, hQ, hPj⟩ := (coord_facts b j).2.1
      obtain ⟨hXj, hsj, hij, -⟩ := coord_cell hX0 j
      rw [← hps, ← cellListOf_eq hsj hij]
      have hmj := siteOf_mem hQ hPj
      rw [hsj, hsite0] at hmj
      have hokj : CellOK (siteRule U (siteOf j.1.1)) (middleBudget : ℝ) j.1.1 := by
        rw [hsj, hsite0]
        exact middleRule_valid i hXj hmj.1 hmj.2
      exact mem_cellListOf hpr h3 hokj
    have hidx0 : (cellPs i ((middleRule i).idx j0.1.1)).idxOf j0.1.1 = cellPos U j0.1.1 := by
      unfold cellPos
      rw [hps]
    have hmk : cellPos U j0.1.1 / (paperPiece i).nc ((middleRule i).idx j0.1.1) *
        (paperPiece i).nc ((middleRule i).idx j0.1.1) <
          (cellPs i ((middleRule i).idx j0.1.1)).length := by
      have h1 := Nat.div_mul_le_self (cellPos U j0.1.1)
        ((paperPiece i).nc ((middleRule i).idx j0.1.1))
      have h2 := List.idxOf_lt_length_of_mem (hmemj j0)
      rw [hidx0] at h2
      omega
    have hsubl : List.Sublist (cellBlock (cellPs i ((middleRule i).idx j0.1.1))
        ((paperPiece i).nc ((middleRule i).idx j0.1.1))
        (cellPos U j0.1.1 / (paperPiece i).nc ((middleRule i).idx j0.1.1)))
          (cellPs i ((middleRule i).idx j0.1.1)) :=
      (List.take_sublist _ _).trans (List.drop_sublist _ _)
    refine ⟨?_, ?_⟩
    · rw [hc]
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨⟨(middleRule i).idx j0.1.1,
        cellPos U j0.1.1 / (paperPiece i).nc ((middleRule i).idx j0.1.1)⟩, ?_, rfl⟩
      rw [mem_sigma, mem_range, mem_range]
      refine ⟨?_, lt_blockCount hk1 hmk⟩
      have hx1 : (1 : ℝ) ≤ cellStart i := le_max_of_le_right (by norm_num [XCh])
      have hxp : cellStart i ≤ j0.1.1 :=
        max_le (by exact_mod_cast hpiece0.1) (by exact_mod_cast hX0')
      have hpY : (j0.1.1 : ℝ) < pieceStop i := by exact_mod_cast hpiece0.2
      have hxY : cellStart i < pieceStop i := hxp.trans_lt hpY
      have hnum : cellNum i = cellCount (cellStart i) (pieceStop i) := by
        unfold cellNum
        simp only [lt_of_le_of_lt hX0' hpiece0.2, ↓reduceIte]
      rw [hnum]
      exact (geoIdx_spec (one_le_cellCount (by linarith) hxY) (by linarith) hxY hxp hpY).2.2.2
    · rw [hc]
      unfold descTerm cellTerm
      simp only [Nat.unpair_pair, one_ne_zero, ↓reduceIte]
      have hnd : (cellPs i ((middleRule i).idx j0.1.1)).Nodup := by
        unfold cellPs Misc.cellList
        exact Finset.sort_nodup _ _
      have hle := blockTerm_le ha d b _ (hnd.sublist hsubl)
        ((Misc.cellList_sorted _ _).sublist hsubl)
        (fun q hq => (Misc.mem_cellPrimes.mp (Misc.mem_cellList.mp (hsubl.subset hq))).1.pos)
        (fun j => by
          obtain ⟨-, hsj, hij, hmj⟩ := coord_cell hX0 j
          apply mem_cellBlock_of_idx hk1 (hmemj j)
          have e1 : (cellPs i ((middleRule i).idx j0.1.1)).idxOf j.1.1 = cellPos U j.1.1 := by
            unfold cellPos
            rw [cellListOf_eq hsj hij, hps]
          have e2 : (paperPiece i).nc ((middleRule i).idx j0.1.1) = cellCardOf U j.1.1 := by
            rw [cellCardOf_eq hsj hij, hk]
          rw [e1, e2, hmj, cellCardOf_eq hsj hij])
      have hhead : (cellBlock (cellPs i ((middleRule i).idx j0.1.1))
          ((paperPiece i).nc ((middleRule i).idx j0.1.1))
          (cellPos U j0.1.1 / (paperPiece i).nc ((middleRule i).idx j0.1.1))).headD 0 =
            Misc.blockStart (cellPs i ((middleRule i).idx j0.1.1))
              ((paperPiece i).nc ((middleRule i).idx j0.1.1))
              (cellPos U j0.1.1 / (paperPiece i).nc ((middleRule i).idx j0.1.1)) := by
        rw [Misc.cellBlock_eq_cons hk1 hmk]
        rfl
      rw [hhead, neg_div] at hle
      exact hle

/-- **`lem:record:block-charge` at the paper's partition**: the charge `b_d(i)` of the paper's
blocks in piece `i` is at most M2's `pieceCharge` of the piece's partition data. -/
theorem blockCharge_le_pieceCharge (i : Fin 33) {a : ℝ} (ha : 0 ≤ a) (d : ℕ) :
    blockCharge (fun b => paperSelAt (paperAtomMap (paperBlockOf (paperCellWith U))) a (.inr b))
        d i ≤ Misc.pieceCharge binU (paperPiece i) a d := by
  rw [← sum_desc i a d]
  unfold blockCharge
  have hinj : Set.InjOn (fun b : PaperBlock (paperCellWith U) => b.val.2)
      (univ.filter fun b : PaperBlock (paperCellWith U) => blockSite b = .inl i) := by
    intro x hx y hy h
    have hx' : x.val.1 = .inl i := (mem_filter.mp hx).2
    have hy' : y.val.1 = .inl i := (mem_filter.mp hy).2
    exact PaperBlock.ext (Prod.ext (hx'.trans hy'.symm) h)
  calc ∑ b ∈ univ.filter (fun b : PaperBlock (paperCellWith U) => blockSite b = .inl i),
        BlockSpecPaper.blockScale b ^ d *
          paperSelAt (paperAtomMap (paperBlockOf (paperCellWith U))) a (.inr b)
      ≤ ∑ b ∈ univ.filter (fun b : PaperBlock (paperCellWith U) => blockSite b = .inl i),
          descTerm i a d b.val.2 :=
        sum_le_sum fun b hb => (block_desc i ha d b (mem_filter.mp hb).2).2
    _ = ∑ c ∈ (univ.filter (fun b : PaperBlock (paperCellWith U) => blockSite b = .inl i)).image
          (fun b => b.val.2), descTerm i a d c := (sum_image hinj).symm
    _ ≤ ∑ c ∈ exDesc i ∪ cellDesc i, descTerm i a d c := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro c hc
          obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
          exact (block_desc i ha d b (mem_filter.mp hb).2).1
        · intro c _ _
          exact descTerm_nonneg i a d c

/-! ## The hypotheses of M2's piece bound, and `thm:bmor` -/

theorem piece_even : ∀ i : Fin 33, Even (max (pieceStart i) XCh) ∧ Even (pieceStop i) := by
  decide +kernel

theorem cellStart_eq (i : Fin 33) : cellStart i = ((max (pieceStart i) XCh : ℕ) : ℝ) := by
  unfold cellStart
  push_cast
  rfl

theorem cellPoint_le_top {x Y : ℝ} (hx : 0 < x) (hxY : x ≤ Y) {n j : ℕ} (hn : 1 ≤ n)
    (hj : j ≤ n) : x ≤ cellPoint x Y n j ∧ cellPoint x Y n j ≤ Y := by
  have hY : 0 < Y := lt_of_lt_of_le hx hxY
  rw [Misc.cellPoint_eq hx hY]
  have h1 : 1 ≤ Y / x := (one_le_div hx).mpr hxY
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ (j : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn'.le
  have hs1 : (j : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact_mod_cast hj
  refine ⟨?_, ?_⟩
  · have := Real.one_le_rpow h1 hs0
    nlinarith
  · have h2 : (Y / x) ^ ((j : ℝ) / n) ≤ (Y / x) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hs1
    rw [Real.rpow_one] at h2
    calc x * (Y / x) ^ ((j : ℝ) / n) ≤ x * (Y / x) := mul_le_mul_of_nonneg_left h2 hx.le
      _ = Y := by field_simp

/-- The parts of `paperPiece i` satisfy the hypotheses of `lem:record:block-charge`(ii). -/
theorem paperPiece_partsOK (i : Fin 33) : Misc.PartsOK binU (paperPiece i) := by
  intro ps hps
  simp only [paperPiece, List.mem_map] at hps
  obtain ⟨k, hk, rfl⟩ := hps
  unfold partsOf partsIn at hk
  rw [List.mem_filter, List.mem_filter, List.mem_range] at hk
  obtain ⟨⟨hk35, -⟩, hne⟩ := hk
  refine ⟨by simpa [List.isEmpty_iff] using hne, fun p hp => (mem_partList.mp hp).1.pos,
    fun p hp => ?_, fun p hp => log_lt_binU_part hk35 hp⟩
  obtain ⟨-, -, h1, h2⟩ := mem_partList.mp hp
  have hb1 := (partE_bounds k (by omega)).1
  have hb2 := (partE_bounds (k + 1) (by omega)).2
  have hp24 : 2 ^ 24 ≤ p := le_trans (by norm_num [Q3]) (hb1.trans h1)
  have hlt := lt_binHi hp24 (lt_of_lt_of_le h2 hb2)
  unfold binU
  rw [Nat.one_le_ceil_iff]
  have : (1 : ℝ) < binHi p := by
    have : 1 < binHi p := lt_of_lt_of_le (by norm_num) (hp24.trans hlt.le)
    exact_mod_cast this
  have := Real.log_pos this
  positivity

/-- The cells of `paperPiece i` satisfy the hypotheses of `lem:record:block-charge`(i). -/
theorem paperPiece_cellsOK (i : Fin 33) (hn : 1 ≤ (paperPiece i).n) :
    Misc.CellsOK (paperPiece i) := by
  have hstop : XCh < pieceStop i := by
    by_contra h
    have : (paperPiece i).n = 0 := by
      simp only [paperPiece, cellNum, h, ↓reduceIte]
    omega
  have hN : (paperPiece i).n = cellCount (cellStart i) (pieceStop i) := by
    simp only [paperPiece, cellNum, hstop, ↓reduceIte]
  have hx0 : (XCh : ℝ) ≤ cellStart i := le_max_right _ _
  have hx1 : (1 : ℝ) < cellStart i := lt_of_lt_of_le (by norm_num [XCh]) hx0
  have hxY : cellStart i ≤ pieceStop i := by
    apply max_le
    · exact_mod_cast (pieceStart_lt_pieceStop i).le
    · exact_mod_cast hstop.le
  have hN1 : 1 ≤ cellCount (cellStart i) (pieceStop i) := hN ▸ hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [paperPiece, Misc.cellPoint_zero]
    exact hx1
  · intro j _
    exact Misc.cellPoint_mono (by linarith) hxY _ _
  · intro j hj
    rw [hN] at hj
    simp only [paperPiece]
    have hN1' := hN1
    rw [cellStart_eq] at hN1' hj ⊢
    exact Misc.notPrime3_cellPoint (piece_even i).1 (piece_even i).2 hN1' hj
  · intro j hj
    rw [hN] at hj
    simp only [paperPiece]
    obtain ⟨hlo, hhi⟩ := cellPoint_le_top (by linarith) hxY hN1 (by omega : j + 1 ≤ _)
    have hlc : 0 < Real.log (cellPoint (cellStart i) (pieceStop i)
        (cellCount (cellStart i) (pieceStop i)) (j + 1)) := Real.log_pos (by linarith)
    have hlY : Real.log (cellPoint (cellStart i) (pieceStop i)
        (cellCount (cellStart i) (pieceStop i)) (j + 1)) ≤ (middleBudget : ℝ) := by
      have h1 := Real.log_le_log (by linarith) hhi
      have h2 := log_siteStop_lt (.inl i)
      have h3 : (355 : ℝ) ≤ middleBudget := by norm_num [middleBudget]
      exact h1.trans ((le_of_lt h2).trans h3)
    unfold cellCard
    rw [Nat.one_le_floor_iff, one_le_div hlc]
    exact hlY

theorem paperPiece_x0 (i : Fin 33) : 1 ≤ (paperPiece i).n → 4800162889 ≤ (paperPiece i).x 0 := by
  intro _
  simp only [paperPiece, Misc.cellPoint_zero]
  have : (XCh : ℝ) ≤ cellStart i := le_max_right _ _
  have h' : (4800162889 : ℝ) ≤ XCh := by norm_num [XCh]
  linarith

/-- **`lem:record:block-charge` at the paper's partition, with `thm:bmor`** (`Target.BMOR`, H2):
for `a ≥ 0` and `d ∈ {2, 3, 4}`, the charge `b_d(i)` of the paper's blocks in piece `i` is at most
the sum over the parts of the piece of the bound (ii) (`exactBound`, the price buckets of the
greedy blocks) plus `eq:record:cell-charge` with `s = d/2` over the cells (`cellBound`, with the
error constant `2411/(5·10⁶ log x_0)` of `thm:bmor`). -/
theorem blockCharge_le_bmor (hB : Target.BMOR) (i : Fin 33) {a : ℝ} (ha : 0 ≤ a) {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4) :
    blockCharge (fun b => paperSelAt (paperAtomMap (paperBlockOf (paperCellWith U))) a (.inr b))
        d i ≤
      ((paperPiece i).parts.map (Misc.exactBound binU a d)).sum +
        Misc.cellBound (paperPiece i) a ((d : ℝ) / 2)
          (2411 / (5000000 * Real.log ((paperPiece i).x 0))) :=
  (blockCharge_le_pieceCharge i ha d).trans
    (Misc.piece_charge_le_bmor hB binU binU_le (paperPiece i) (paperPiece_partsOK i)
      (paperPiece_cellsOK i) (paperPiece_x0 i) ha hd)

/-- **M2's explicit bound for the degree-`d` charge of piece `i`** at the exponent `a`: the bounds
(ii) of the parts (`exactBound`) plus `eq:record:cell-charge` with `s = d/2` and `thm:bmor`'s error
over the cells (`cellBound`). -/
noncomputable def pieceBound (a : ℝ) (d : ℕ) (i : Fin 33) : ℝ :=
  ((paperPiece i).parts.map (Misc.exactBound binU a d)).sum +
    Misc.cellBound (paperPiece i) a ((d : ℝ) / 2)
      (2411 / (5000000 * Real.log ((paperPiece i).x 0)))

theorem blockCharge_le_pieceBound (hB : Target.BMOR) (i : Fin 33) {a : ℝ} (ha : 0 ≤ a) {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4) :
    blockCharge (fun b => paperSelAt (paperAtomMap (paperBlockOf (paperCellWith U))) a (.inr b))
      d i ≤ pieceBound a d i :=
  blockCharge_le_bmor hB i ha hd

end Sarkozy.PaperNumbers
