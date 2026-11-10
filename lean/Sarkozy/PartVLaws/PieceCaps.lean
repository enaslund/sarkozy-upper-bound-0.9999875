module

public import Sarkozy.PartV.LocalDomain
public import Sarkozy.PartV.Blocks

@[expose] public section

/-!
# The piece caps (`lem:piece-caps`)

`paper/sections/20_middle_reference.tex`, `lem:piece-caps`, with the histogram bin `k_𝔅` of
`lem:record:block-charge`(ii) and the blocks of `def:record:exact-blocks`(c), (d) (V1's
`PartV/Blocks.lean`).

**The statement.** For a middle piece, `L_i` is the largest of the numbers `k_𝔅 L / 2¹⁶` over
its exact blocks (`def:record:exact-blocks`(c)) and of the recorded upper bounds `R_j` for
`n_j log x_{j+1}` over its cells (`def:record:exact-blocks`(d)). Then every block of the piece
has `log q_𝔅 ≤ L_i ≤ L`, every block has `q_𝔅^{2a} ≤ C_i = e^{2a_* L_i}` for `0 ≤ a ≤ a_*`, and
blocks in pieces `i_1, …, i_k` have `∏_l q_{𝔅_l}^{2a} ≤ ∏_l C_{i_l}`.

**Formalized here.**
* The bin `k_𝔅 = ⌈2¹⁶ 𝔲(𝔅) / 𝔲_*⌉` (`blockBin`), with `1 ≤ k_𝔅 ≤ 2¹⁶` when `0 < 𝔲(𝔅) ≤ 𝔲_*`
  (`one_le_blockBin`, `blockBin_le`), and `log q_𝔅 ≤ 𝔲(𝔅)/2⁴⁰ ≤ k_𝔅 𝔲_*/2⁵⁶ = k_𝔅 L/2¹⁶`
  (`log_le_blockU`, `blockU_le_bin`): the first assertion of `lem:record:block-charge`(ii).
* A cell block has `log q_𝔅 ≤ n_j log x_{j+1}` (`cellBlock_log_le`), and
  `n_j log x_{j+1} ≤ L` for `n_j = ⌊L / log x_{j+1}⌋` (`cellCard_log_le`).
* `pieceCap`: the paper's `L_i`, the maximum of these numbers. **`piece_caps`**: every exact block
  and every cell block of the piece has `log q_𝔅 ≤ L_i`, and `L_i ≤ L`. The recorded cell bounds
  `R_j` are data (`PieceCell`); `L_i ≤ L` needs `R_j ≤ L`, which holds for the exact value
  `R_j = n_j log x_{j+1}` (`PieceCell.ofCard`, `ofCard_R_le`) and is a recorded fact otherwise.
* **`selection_le_pieceCap`**, **`middleBlock_selection_le_cap`** and
  **`prod_selection_le_caps`**: the consequences `q_𝔅^{2a} ≤ C_i` and
  `∏_l q_{𝔅_l}^{2a} ≤ C_m = ∏_l C_{i_l}` (with `C_m` the product over the multiset of pieces).

The numerical values `L_i ∈ [556.79, 570]` (`tab:data:piece-values`) and the histogram of the
exact blocks are recorded data and are not entered here.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.PartV

/-! ## The histogram bin of an exact block -/

/-- The upper logarithm `𝔲(𝔅) = ∑_{p ∈ 𝔅} 𝔲(p)` of a block. -/
def blockU (u : ℕ → ℕ) (b : List ℕ) : ℕ := (b.map u).sum

/-- **The histogram bin** `k_𝔅 = ⌈2¹⁶ 𝔲(𝔅) / 𝔲_*⌉` of an exact block
(`lem:record:block-charge`(ii)). -/
noncomputable def blockBin (u : ℕ → ℕ) (b : List ℕ) : ℕ :=
  ⌈(2 ^ 16 * (blockU u b : ℝ)) / integerBudget⌉₊

theorem integerBudget_pos : (0 : ℝ) < integerBudget := by
  unfold integerBudget middleBudget
  norm_num

theorem integerBudget_eq_real : (integerBudget : ℝ) = 2 ^ 40 * middleBudget := by
  unfold integerBudget
  push_cast
  ring

/-- **`k_𝔅 ≤ 2¹⁶`** when `𝔲(𝔅) ≤ 𝔲_*` (`lem:record:block-charge`(ii)). -/
theorem blockBin_le {u : ℕ → ℕ} {b : List ℕ} (h : blockU u b ≤ integerBudget) :
    blockBin u b ≤ 2 ^ 16 := by
  unfold blockBin
  apply Nat.ceil_le.mpr
  rw [div_le_iff₀ integerBudget_pos]
  have h' : (blockU u b : ℝ) ≤ integerBudget := by exact_mod_cast h
  push_cast
  nlinarith

/-- **`1 ≤ k_𝔅`** when `𝔲(𝔅) > 0`. -/
theorem one_le_blockBin {u : ℕ → ℕ} {b : List ℕ} (h : 0 < blockU u b) : 1 ≤ blockBin u b := by
  unfold blockBin
  have h' : (0 : ℝ) < blockU u b := by exact_mod_cast h
  exact Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
    (Nat.ceil_pos.mpr (div_pos (by positivity) integerBudget_pos)))

/-- **`𝔲(𝔅)/2⁴⁰ ≤ k_𝔅 𝔲_*/2⁵⁶ = k_𝔅 L/2¹⁶`** (`lem:piece-caps`, proof). -/
theorem blockU_le_bin (u : ℕ → ℕ) (b : List ℕ) :
    (blockU u b : ℝ) / 2 ^ 40 ≤ (blockBin u b : ℝ) * middleBudget / 2 ^ 16 := by
  have hk : (2 ^ 16 * (blockU u b : ℝ)) / integerBudget ≤ blockBin u b := Nat.le_ceil _
  rw [div_le_iff₀ integerBudget_pos, integerBudget_eq_real] at hk
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hk]

/-- **`log q_𝔅 ≤ 𝔲(𝔅)/2⁴⁰`** when `log p < 𝔲(p)/2⁴⁰` for every prime of the block
(`def:record:exact-blocks`(c)). -/
theorem log_le_blockU (u : ℕ → ℕ) (b : List ℕ)
    (hlog : ∀ p ∈ b, Real.log p < (u p : ℝ) / 2 ^ 40) :
    (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤ (blockU u b : ℝ) / 2 ^ 40 := by
  rw [blockU, ← list_sum_div]
  exact List.sum_le_sum fun p hp => (hlog p hp).le

/-- **An exact block has `log q_𝔅 ≤ k_𝔅 L / 2¹⁶`.** -/
theorem exactBlock_log_le_bin (u : ℕ → ℕ) (b : List ℕ)
    (hlog : ∀ p ∈ b, Real.log p < (u p : ℝ) / 2 ^ 40) :
    (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤ (blockBin u b : ℝ) * middleBudget / 2 ^ 16 :=
  (log_le_blockU u b hlog).trans (blockU_le_bin u b)

/-- `k_𝔅 L / 2¹⁶ ≤ L` when `𝔲(𝔅) ≤ 𝔲_*`. -/
theorem bin_cap_le {u : ℕ → ℕ} {b : List ℕ} (h : blockU u b ≤ integerBudget) :
    (blockBin u b : ℝ) * middleBudget / 2 ^ 16 ≤ middleBudget := by
  have hk : (blockBin u b : ℝ) ≤ 2 ^ 16 := by exact_mod_cast blockBin_le h
  rw [div_le_iff₀ (by positivity)]
  have hL : (0 : ℝ) ≤ middleBudget := Nat.cast_nonneg _
  nlinarith

/-! ## Cell blocks -/

/-- **`n_j log x_{j+1} ≤ L`** for `n_j = ⌊L / log x_{j+1}⌋`, `x_{j+1} > 1`, `L ≥ 0`
(`def:record:exact-blocks`(d)). -/
theorem cellCard_log_le {L xnext : ℝ} (hx : 1 < xnext) (hL : 0 ≤ L) :
    (⌊L / Real.log xnext⌋₊ : ℝ) * Real.log xnext ≤ L := by
  have hlogx : 0 < Real.log xnext := Real.log_pos hx
  have := Nat.floor_le (div_nonneg hL hlogx.le)
  calc (⌊L / Real.log xnext⌋₊ : ℝ) * Real.log xnext ≤ L / Real.log xnext * Real.log xnext :=
        mul_le_mul_of_nonneg_right this hlogx.le
    _ = L := div_mul_cancel₀ L hlogx.ne'

/-- **A block of a cell has `log q_𝔅 ≤ n_j log x_{j+1}`**: it has at most `n_j` primes, all below
`x_{j+1}` (`lem:piece-caps`, proof). -/
theorem cellBlock_log_le (ps : List ℕ) (k m : ℕ) {xnext : ℝ} (hx : 1 ≤ xnext)
    (hps : ∀ p ∈ ps, 0 < p ∧ (p : ℝ) < xnext) :
    ((cellBlock ps k m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤ k * Real.log xnext := by
  have hlogx : 0 ≤ Real.log xnext := Real.log_nonneg hx
  have hmem : ∀ p ∈ cellBlock ps k m, p ∈ ps := fun p hp =>
    List.mem_of_mem_drop (List.mem_of_mem_take hp)
  have h1 : ((cellBlock ps k m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤
      ((cellBlock ps k m).map fun _ => Real.log xnext).sum := by
    refine List.sum_le_sum fun p hp => ?_
    obtain ⟨hp0, hpx⟩ := hps p (hmem p hp)
    exact Real.log_le_log (by exact_mod_cast hp0) hpx.le
  have h2 : ((cellBlock ps k m).map fun _ => Real.log xnext).sum =
      (cellBlock ps k m).length * Real.log xnext := by
    rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
  have h3 : ((cellBlock ps k m).length : ℝ) ≤ k := by exact_mod_cast cellBlock_length_le ps k m
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ (k : ℝ) * Real.log xnext := mul_le_mul_of_nonneg_right h3 hlogx

/-- **A cell of a middle piece** above `X_Ch` (`def:record:exact-blocks`(d)): the list of its
primes `≡ 3 (mod 4)` in increasing order, all in `(0, x_{j+1})`; its right end `x_{j+1} > 1`; its
block cardinality `n_j`; and a recorded upper bound `R_j ≥ n_j log x_{j+1}`. The blocks of the
cell are `cellBlock ps n m`, `m = 0, 1, …`. -/
structure PieceCell where
  ps : List ℕ
  xnext : ℝ
  n : ℕ
  R : ℝ
  primes_lt : ∀ p ∈ ps, 0 < p ∧ (p : ℝ) < xnext
  one_lt : 1 < xnext
  R_ge : (n : ℝ) * Real.log xnext ≤ R

/-- **A block of a cell has `log q_𝔅 ≤ R_j`.** -/
theorem PieceCell.block_log_le (c : PieceCell) (m : ℕ) :
    ((cellBlock c.ps c.n m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤ c.R :=
  (cellBlock_log_le c.ps c.n m c.one_lt.le c.primes_lt).trans c.R_ge

/-- The cell with the paper's cardinality `n_j = ⌊L / log x_{j+1}⌋` and the exact value
`R_j = n_j log x_{j+1}`. -/
noncomputable def PieceCell.ofCard (ps : List ℕ) (xnext : ℝ)
    (hps : ∀ p ∈ ps, 0 < p ∧ (p : ℝ) < xnext) (hx : 1 < xnext) : PieceCell where
  ps := ps
  xnext := xnext
  n := ⌊(middleBudget : ℝ) / Real.log xnext⌋₊
  R := (⌊(middleBudget : ℝ) / Real.log xnext⌋₊ : ℝ) * Real.log xnext
  primes_lt := hps
  one_lt := hx
  R_ge := le_rfl

/-- **The exact cell bound is at most `L`.** -/
theorem PieceCell.ofCard_R_le (ps : List ℕ) (xnext : ℝ)
    (hps : ∀ p ∈ ps, 0 < p ∧ (p : ℝ) < xnext) (hx : 1 < xnext) :
    (PieceCell.ofCard ps xnext hps hx).R ≤ middleBudget :=
  cellCard_log_le hx (Nat.cast_nonneg _)

/-! ## The piece cap `L_i` -/

theorem le_foldr_max {l : List ℝ} {x : ℝ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ l, x ≤ c) :
    l.foldr max 0 ≤ c := by
  induction l with
  | nil => exact hc
  | cons a l ih =>
    exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

theorem foldr_max_nonneg (l : List ℝ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans (le_max_right _ _)

/-- **The piece cap** `L_i` (`lem:piece-caps`): the largest of the numbers `k_𝔅 L / 2¹⁶` over the
exact blocks of the piece and of the recorded cell bounds `R_j` over its cells (`0` if the piece
has neither). -/
noncomputable def pieceCap (u : ℕ → ℕ) (exact : List (List ℕ)) (cells : List PieceCell) : ℝ :=
  ((exact.map fun b => (blockBin u b : ℝ) * middleBudget / 2 ^ 16) ++ cells.map PieceCell.R).foldr
    max 0

theorem pieceCap_nonneg (u : ℕ → ℕ) (exact : List (List ℕ)) (cells : List PieceCell) :
    0 ≤ pieceCap u exact cells :=
  foldr_max_nonneg _

/-- **`lem:piece-caps`**: every exact block and every cell block of the piece has
`log q_𝔅 ≤ L_i`, and `L_i ≤ L`. The hypotheses: `log p < 𝔲(p)/2⁴⁰` on the exact blocks (the bins
of `def:record:exact-blocks`(c)), `𝔲(𝔅) ≤ 𝔲_*` (the greedy rule, `greedyBlocks_budget`), and the
recorded cell bounds `R_j ≤ L` (exact for `PieceCell.ofCard`). -/
theorem piece_caps (u : ℕ → ℕ) (exact : List (List ℕ)) (cells : List PieceCell)
    (hlog : ∀ b ∈ exact, ∀ p ∈ b, Real.log p < (u p : ℝ) / 2 ^ 40)
    (hbud : ∀ b ∈ exact, blockU u b ≤ integerBudget)
    (hR : ∀ c ∈ cells, c.R ≤ middleBudget) :
    (∀ b ∈ exact, (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤ pieceCap u exact cells) ∧
    (∀ c ∈ cells, ∀ m,
      ((cellBlock c.ps c.n m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤ pieceCap u exact cells) ∧
    pieceCap u exact cells ≤ middleBudget := by
  refine ⟨fun b hb => ?_, fun c hc m => ?_, ?_⟩
  · refine (exactBlock_log_le_bin u b (hlog b hb)).trans (le_foldr_max ?_)
    exact List.mem_append_left _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  · refine (c.block_log_le m).trans (le_foldr_max ?_)
    exact List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  · refine foldr_max_le (Nat.cast_nonneg _) fun x hx => ?_
    rcases List.mem_append.mp hx with h | h
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      exact bin_cap_le (hbud b hb)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      exact hR c hc

/-- **`lem:piece-caps` for the greedy blocks** of a list of primes (`def:record:exact-blocks`(c)):
the budget hypothesis is the greedy rule itself (`greedyBlocks_budget`). -/
theorem piece_caps_greedy (u : ℕ → ℕ) (hu : ∀ p, u p ≤ integerBudget) (ps : List ℕ)
    (hlog : ∀ p ∈ ps, Real.log p < (u p : ℝ) / 2 ^ 40) (cells : List PieceCell)
    (hR : ∀ c ∈ cells, c.R ≤ middleBudget) :
    (∀ b ∈ greedyBlocks u integerBudget ps, (b.map fun p : ℕ => Real.log (p : ℝ)).sum ≤
      pieceCap u (greedyBlocks u integerBudget ps) cells) ∧
    (∀ c ∈ cells, ∀ m, ((cellBlock c.ps c.n m).map fun p : ℕ => Real.log (p : ℝ)).sum ≤
      pieceCap u (greedyBlocks u integerBudget ps) cells) ∧
    pieceCap u (greedyBlocks u integerBudget ps) cells ≤ middleBudget := by
  refine piece_caps u _ cells (fun b hb p hp => hlog p ?_)
    (fun b hb => greedyBlocks_budget u integerBudget hu ps b hb) hR
  rw [← greedyBlocks_flatten u integerBudget ps]
  exact List.mem_flatten.mpr ⟨b, hb, hp⟩

/-! ## Selection factors and products -/

/-- **`q^{2a} ≤ e^{2a_* L_i}`** from `log q ≤ L_i`, `0 ≤ a ≤ a_*`, `0 ≤ L_i`. -/
theorem selection_le_pieceCap {q Li a astar : ℝ} (hq : 0 < q) (hlog : Real.log q ≤ Li)
    (ha : 0 ≤ a) (haa : a ≤ astar) (hLi : 0 ≤ Li) : q ^ (2 * a) ≤ Real.exp (2 * astar * Li) := by
  rw [Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log q * (2 * a) ≤ Li * (2 * a) := mul_le_mul_of_nonneg_right hlog (by linarith)
  have h2 : Li * (2 * a) ≤ 2 * astar * Li := by nlinarith
  linarith

/-- **`lem:piece-caps`, one block**: if a middle block of the piece `i` has `log q_𝔅 ≤ L_i`
(e.g. by `piece_caps`), then `q_𝔅^{2a} ≤ C_i = e^{2a_* L_i}` for `0 ≤ a ≤ a_*`. -/
theorem middleBlock_selection_le_cap (B : MiddleBlock) (Li : Fin 33 → ℝ)
    (hB : ∑ p ∈ B.primes, Real.log p ≤ Li B.piece) (hLi : 0 ≤ Li B.piece) {a astar : ℝ}
    (ha : 0 ≤ a) (haa : a ≤ astar) :
    (∏ p ∈ B.primes, (p : ℝ)) ^ (2 * a) ≤ Real.exp (2 * astar * Li B.piece) := by
  have hpos : ∀ p ∈ B.primes, (0 : ℝ) < p := fun p hp => by exact_mod_cast (B.prime p hp).pos
  have hq : 0 < ∏ p ∈ B.primes, (p : ℝ) := prod_pos hpos
  refine selection_le_pieceCap hq ?_ ha haa hLi
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')]
  exact hB

/-- **`lem:piece-caps`, products**: blocks `𝔅_l` (`l ∈ s`) lying in the pieces `i_l`, each with
`log q_{𝔅_l} ≤ L_{i_l}`, have `∏_l q_{𝔅_l}^{2a} ≤ C_m = ∏_{i ∈ m} C_i`, where `m` is the multiset of
their pieces and `C_i = e^{2a_* L_i}`. -/
theorem prod_selection_le_caps {ι : Type*} (s : Finset ι) (B : ι → MiddleBlock)
    (Li : Fin 33 → ℝ) (hB : ∀ l ∈ s, ∑ p ∈ (B l).primes, Real.log p ≤ Li (B l).piece)
    (hLi : ∀ i, 0 ≤ Li i) {a astar : ℝ} (ha : 0 ≤ a) (haa : a ≤ astar) :
    ∏ l ∈ s, (∏ p ∈ (B l).primes, (p : ℝ)) ^ (2 * a) ≤
      ((s.val.map fun l => (B l).piece).map fun i => Real.exp (2 * astar * Li i)).prod := by
  rw [Multiset.map_map]
  change _ ≤ ∏ l ∈ s, Real.exp (2 * astar * Li (B l).piece)
  refine prod_le_prod₀ (fun l _ => ?_) fun l hl =>
    middleBlock_selection_le_cap (B l) Li (hB l hl) (hLi _) ha haa
  have hq : 0 < ∏ p ∈ (B l).primes, (p : ℝ) :=
    prod_pos fun p hp => by exact_mod_cast ((B l).prime p hp).pos
  exact (Real.rpow_pos_of_pos hq _).le

/-- A middle block listed without repetition: its `log q_𝔅` is the list sum, so `piece_caps`
applies to it. -/
theorem log_sum_toFinset {b : List ℕ} (hb : b.Nodup) :
    ∑ p ∈ b.toFinset, Real.log (p : ℝ) = (b.map fun p : ℕ => Real.log (p : ℝ)).sum :=
  List.sum_toFinset _ hb

end Sarkozy.PartVLaws
