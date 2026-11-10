module

public import Sarkozy.Misc.CellSummation
public import Sarkozy.PartV.Blocks
public import Mathlib.Data.List.GetD

@[expose] public section






open Finset

namespace Sarkozy.Misc

open Sarkozy.PartV

/-! ## Blocks of a cell -/

/-- The number `⌈ℓ/k⌉` of blocks of `k` consecutive primes of a cell with `ℓ` primes. -/
def blockCount (l k : ℕ) : ℕ := (l + k - 1) / k

/-- The start `b_𝔅` of the `m`-th block: the `(m k)`-th prime of the cell. -/
def blockStart (ps : List ℕ) (k m : ℕ) : ℕ := ps.getD (m * k) 0

/-- The product `q_𝔅` of the `m`-th block. -/
def blockProd (ps : List ℕ) (k m : ℕ) : ℕ := (cellBlock ps k m).prod

/-- **The charge of a cell**, `∑_𝔅 q_𝔅^{2a} b_𝔅^{-s}` over its blocks. -/
noncomputable def cellCharge (ps : List ℕ) (k : ℕ) (a s : ℝ) : ℝ :=
  ∑ m ∈ range (blockCount ps.length k),
    ((blockProd ps k m : ℕ) : ℝ) ^ (2 * a) * ((blockStart ps k m : ℕ) : ℝ) ^ (-s)

/-- **The start sum of a cell**, `∑_𝔅 b_𝔅^{-1}` over its blocks (`lem:record:lower-start-sums`). -/
noncomputable def cellStartSum (ps : List ℕ) (k : ℕ) : ℝ :=
  ∑ m ∈ range (blockCount ps.length k), ((blockStart ps k m : ℕ) : ℝ)⁻¹

theorem le_blockCount_mul {l k : ℕ} (hk : 1 ≤ k) : l ≤ blockCount l k * k := by
  unfold blockCount
  have h1 := Nat.div_add_mod (l + k - 1) k
  have h2 := Nat.mod_lt (l + k - 1) (by omega : 0 < k)
  rw [mul_comm]
  omega

theorem mul_lt_of_lt_blockCount {l k m : ℕ} (hk : 1 ≤ k) (hm : m < blockCount l k) : m * k < l := by
  unfold blockCount at hm
  have h1 := Nat.div_add_mod (l + k - 1) k
  have h3 : (m + 1) * k ≤ (l + k - 1) / k * k := Nat.mul_le_mul_right k hm
  have h4 : (l + k - 1) / k * k ≤ l + k - 1 := Nat.div_mul_le_self _ _
  rw [add_mul, one_mul] at h3
  omega

/-- The blocks partition the first `M k` primes. -/
theorem sum_cellBlock_take (ps : List ℕ) (k : ℕ) (f : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ range M, ((cellBlock ps k m).map f).sum = ((ps.take (M * k)).map f).sum := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, add_mul, one_mul, List.take_add, List.map_append, List.sum_append]
    rfl

/-- **The blocks partition the cell**: `∑_𝔅 ∑_{p ∈ 𝔅} f(p) = ∑_p f(p)`. -/
theorem sum_cellBlock (ps : List ℕ) {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℝ) :
    ∑ m ∈ range (blockCount ps.length k), ((cellBlock ps k m).map f).sum = (ps.map f).sum := by
  rw [sum_cellBlock_take, List.take_of_length_le (le_blockCount_mul hk)]

/-- The block starting at index `m k < |ps|` is `ps[m k] :: …`. -/
theorem cellBlock_eq_cons {ps : List ℕ} {k m : ℕ} (hk : 1 ≤ k) (h : m * k < ps.length) :
    cellBlock ps k m = blockStart ps k m :: (ps.drop (m * k + 1)).take (k - 1) := by
  unfold cellBlock blockStart
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.take_succ_cons, Nat.add_sub_cancel]

/-- In an increasing list, the start of a block is its least element. -/
theorem blockStart_le {ps : List ℕ} (hsort : ps.Pairwise (· < ·)) {k m : ℕ} (hk : 1 ≤ k)
    (h : m * k < ps.length) : ∀ p ∈ cellBlock ps k m, blockStart ps k m ≤ p := by
  intro p hp
  have hd : (ps.drop (m * k)).Pairwise (· < ·) := hsort.sublist (List.drop_sublist _ _)
  rw [List.drop_eq_getElem_cons h] at hd
  rw [cellBlock_eq_cons hk h] at hp
  rcases List.mem_cons.mp hp with rfl | hp'
  · exact le_rfl
  · have hrest := (List.pairwise_cons.mp hd).1
    have hp'' : p ∈ ps.drop (m * k + 1) := List.mem_of_mem_take hp'
    have := hrest p hp''
    unfold blockStart
    rw [List.getD_eq_getElem _ _ h]
    exact this.le

/-- The start of a block is a prime of the cell. -/
theorem blockStart_mem {ps : List ℕ} {k m : ℕ} (h : m * k < ps.length) :
    blockStart ps k m ∈ ps := by
  unfold blockStart
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

/-- In an increasing list, every element of block `m` is smaller than the start of block `m + 1`. -/
theorem lt_blockStart_succ {ps : List ℕ} (hsort : ps.Pairwise (· < ·)) {k m : ℕ}
    (h : (m + 1) * k < ps.length) : ∀ p ∈ cellBlock ps k m, p < blockStart ps k (m + 1) := by
  intro p hp
  have hd : (ps.drop (m * k)).Pairwise (· < ·) := hsort.sublist (List.drop_sublist _ _)
  rw [← List.take_append_drop k (ps.drop (m * k)), List.drop_drop] at hd
  have hsplit := (List.pairwise_append.mp hd).2.2
  have hmem : blockStart ps k (m + 1) ∈ ps.drop (m * k + k) := by
    unfold blockStart
    rw [List.getD_eq_getElem _ _ h]
    have he : (m + 1) * k = m * k + k := by ring
    have h' : m * k + k < ps.length := he ▸ h
    rw [List.drop_eq_getElem_cons h']
    simp only [he]
    exact List.mem_cons_self
  exact hsplit p hp _ hmem

/-- A block that is followed by another block has exactly `k` primes. -/
theorem length_cellBlock_of_succ {ps : List ℕ} {k m : ℕ} (h : (m + 1) * k < ps.length) :
    (cellBlock ps k m).length = k := by
  unfold cellBlock
  rw [List.length_take, List.length_drop]
  have : k ≤ ps.length - m * k := by
    have he : (m + 1) * k = m * k + k := by ring
    omega
  exact min_eq_left this

theorem length_cellBlock_le (ps : List ℕ) (k m : ℕ) : (cellBlock ps k m).length ≤ k :=
  cellBlock_length_le ps k m

/-! ## The block step -/

/-- A product of naturals at most `X ≥ 0` is at most `X^{length}`. -/
theorem list_prod_cast_le {l : List ℕ} {X : ℝ} (hX : 0 ≤ X) (h : ∀ p ∈ l, (p : ℝ) ≤ X) :
    ((l.prod : ℕ) : ℝ) ≤ X ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.prod_cons, Nat.cast_mul, List.length_cons, pow_succ]
    have hp := h p List.mem_cons_self
    have hl := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    have h0 : (0 : ℝ) ≤ (l.prod : ℕ) := Nat.cast_nonneg _
    calc (p : ℝ) * (l.prod : ℕ) ≤ X * X ^ l.length := mul_le_mul hp hl h0 hX
      _ = X ^ l.length * X := by ring

/-- **The price of a block**: `q_𝔅^{2a} ≤ exp(2 a k log x_{j+1})` for a block of at most `k` primes
below `x_{j+1} ≥ 1`. -/
theorem blockProd_rpow_le {ps : List ℕ} {k m : ℕ} {a xr : ℝ} (ha : 0 ≤ a) (hxr : 1 ≤ xr)
    (hmem : ∀ p ∈ ps, (p : ℝ) < xr) :
    ((blockProd ps k m : ℕ) : ℝ) ^ (2 * a) ≤ Real.exp (2 * a * k * Real.log xr) := by
  have hxr0 : 0 < xr := by linarith
  have h1 : ((blockProd ps k m : ℕ) : ℝ) ≤ xr ^ (cellBlock ps k m).length :=
    list_prod_cast_le hxr0.le fun p hp =>
      (hmem p (List.mem_of_mem_drop (List.mem_of_mem_take hp))).le
  have h2 : xr ^ (cellBlock ps k m).length ≤ xr ^ k :=
    pow_le_pow_right₀ hxr (length_cellBlock_le ps k m)
  have h3 := Real.rpow_le_rpow (Nat.cast_nonneg _) (h1.trans h2) (by linarith : (0 : ℝ) ≤ 2 * a)
  refine h3.trans (le_of_eq ?_)
  rw [Real.rpow_def_of_pos (pow_pos hxr0 k), Real.log_pow]
  congr 1
  ring

/-- **The block step of `lem:record:block-charge`(i)**: for the increasing list `ps` of the
primes of a cell `[x_j, x_{j+1})` (`0 < x_j`, `1 ≤ x_{j+1}`) and blocks of `k ≥ 1` consecutive
primes,
`∑_𝔅 q_𝔅^{2a} b_𝔅^{-s} ≤ Π x_j^{-s} + (Π/k) ∑_p p^{-s}` with `Π = exp(2 a k log x_{j+1})`. -/
theorem cellCharge_le {ps : List ℕ} {k : ℕ} (hk : 1 ≤ k) {a s xl xr : ℝ} (ha : 0 ≤ a)
    (hs : 0 ≤ s) (hxl : 0 < xl) (hxr : 1 ≤ xr) (hsort : ps.Pairwise (· < ·))
    (hmem : ∀ p ∈ ps, xl ≤ (p : ℝ) ∧ (p : ℝ) < xr) :
    cellCharge ps k a s ≤ Real.exp (2 * a * k * Real.log xr) * xl ^ (-s) +
      Real.exp (2 * a * k * Real.log xr) / k * (ps.map fun p : ℕ => (p : ℝ) ^ (-s)).sum := by
  set P := Real.exp (2 * a * k * Real.log xr) with hP
  set M := blockCount ps.length k with hM
  set f : ℕ → ℝ := fun p => (p : ℝ) ^ (-s) with hf
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpos : ∀ p ∈ ps, (0 : ℝ) < p := fun p hp => lt_of_lt_of_le hxl (hmem p hp).1
  have hstart_pos : ∀ m < M, (0 : ℝ) < blockStart ps k m := fun m hm =>
    hpos _ (blockStart_mem (mul_lt_of_lt_blockCount hk hm))
  -- step 1: price each block by `Π`
  have h1 : cellCharge ps k a s ≤ ∑ m ∈ range M, P * ((blockStart ps k m : ℕ) : ℝ) ^ (-s) := by
    unfold cellCharge
    apply Finset.sum_le_sum
    intro m _
    exact mul_le_mul_of_nonneg_right
      (blockProd_rpow_le ha hxr (fun p hp => (hmem p hp).2))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine h1.trans ?_
  rw [← Finset.mul_sum]
  have hP0 : 0 ≤ P := (Real.exp_pos _).le
  -- step 2: the starts
  have hfsum0 : 0 ≤ (ps.map f).sum :=
    List.sum_nonneg fun y hy => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hy
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [hM0, Finset.sum_range_zero, mul_zero]
    have : 0 ≤ xl ^ (-s) := Real.rpow_nonneg hxl.le _
    positivity
  obtain ⟨M', hM'⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [hM', Finset.sum_range_succ']
  -- the first block
  have hfirst : ((blockStart ps k 0 : ℕ) : ℝ) ^ (-s) ≤ xl ^ (-s) := by
    have h0 : 0 * k < ps.length := mul_lt_of_lt_blockCount hk (by omega : 0 < M)
    exact Real.rpow_le_rpow_of_nonpos hxl (hmem _ (blockStart_mem h0)).1 (by linarith)
  -- the later blocks
  have hlater : ∀ m < M', ((blockStart ps k (m + 1) : ℕ) : ℝ) ^ (-s) ≤
      1 / k * ((cellBlock ps k m).map f).sum := by
    intro m hm
    have hlt : (m + 1) * k < ps.length := mul_lt_of_lt_blockCount hk (by omega)
    have hlen := length_cellBlock_of_succ hlt
    have hb : ∀ p ∈ cellBlock ps k m, ((blockStart ps k (m + 1) : ℕ) : ℝ) ^ (-s) ≤ f p := by
      intro p hp
      have hpp : p ∈ ps := List.mem_of_mem_drop (List.mem_of_mem_take hp)
      have hlt' : (p : ℝ) ≤ blockStart ps k (m + 1) := by
        exact_mod_cast (lt_blockStart_succ hsort hlt p hp).le
      exact Real.rpow_le_rpow_of_nonpos (hpos p hpp) hlt' (by linarith)
    have hsum := List.sum_le_sum hb
    rw [List.map_const', List.sum_replicate, nsmul_eq_mul, hlen] at hsum
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hkR]
    linarith
  have hlater_sum : ∑ m ∈ range M', ((blockStart ps k (m + 1) : ℕ) : ℝ) ^ (-s) ≤
      1 / k * (ps.map f).sum := by
    calc ∑ m ∈ range M', ((blockStart ps k (m + 1) : ℕ) : ℝ) ^ (-s)
        ≤ ∑ m ∈ range M', 1 / k * ((cellBlock ps k m).map f).sum :=
          Finset.sum_le_sum fun m hm => hlater m (mem_range.mp hm)
      _ = 1 / k * ∑ m ∈ range M', ((cellBlock ps k m).map f).sum := by rw [Finset.mul_sum]
      _ ≤ 1 / k * ∑ m ∈ range M, ((cellBlock ps k m).map f).sum := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          intro m _ _
          exact List.sum_nonneg fun y hy => by
            obtain ⟨p, _, rfl⟩ := List.mem_map.mp hy
            exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      _ = 1 / k * (ps.map f).sum := by rw [hM, sum_cellBlock ps hk f]
  have : P * (∑ m ∈ range M', ((blockStart ps k (m + 1) : ℕ) : ℝ) ^ (-s) +
      ((blockStart ps k 0 : ℕ) : ℝ) ^ (-s)) ≤ P * (1 / k * (ps.map f).sum + xl ^ (-s)) :=
    mul_le_mul_of_nonneg_left (add_le_add hlater_sum hfirst) hP0
  calc _ ≤ P * (1 / k * (ps.map f).sum + xl ^ (-s)) := this
    _ = _ := by ring

/-- **The start sum of a cell** (`lem:record:lower-start-sums`(i), block step): a block has at most
`k` primes, all at least its start, so `∑_𝔅 b_𝔅^{-1} ≥ k^{-1} ∑_p p^{-1}`. -/
theorem cellStartSum_ge {ps : List ℕ} {k : ℕ} (hk : 1 ≤ k) (hsort : ps.Pairwise (· < ·))
    (hpos : ∀ p ∈ ps, 0 < p) :
    1 / k * (ps.map fun p : ℕ => (p : ℝ)⁻¹).sum ≤ cellStartSum ps k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold cellStartSum
  rw [← sum_cellBlock ps hk, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hlt := mul_lt_of_lt_blockCount hk (mem_range.mp hm)
  have hb0 : (0 : ℝ) < blockStart ps k m := by exact_mod_cast hpos _ (blockStart_mem hlt)
  have hb : ∀ p ∈ cellBlock ps k m, (p : ℝ)⁻¹ ≤ ((blockStart ps k m : ℕ) : ℝ)⁻¹ := by
    intro p hp
    have hle : (blockStart ps k m : ℝ) ≤ p := by exact_mod_cast blockStart_le hsort hk hlt p hp
    exact inv_anti₀ hb0 hle
  have hsum := List.sum_le_sum hb
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul] at hsum
  have hlen : ((cellBlock ps k m).length : ℝ) ≤ k := by exact_mod_cast length_cellBlock_le ps k m
  have h2 : ((cellBlock ps k m).length : ℝ) * ((blockStart ps k m : ℕ) : ℝ)⁻¹ ≤
      k * ((blockStart ps k m : ℕ) : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hlen (inv_nonneg.mpr hb0.le)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hkR]
  linarith

/-! ## The cells of a sequence of points -/

/-- The primes `p ≡ 3 (mod 4)` of the cell `[a, b)` in increasing order. -/
noncomputable def cellList (a b : ℝ) : List ℕ := (cellPrimes a b).sort (· ≤ ·)

theorem cellList_sorted (a b : ℝ) : (cellList a b).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

theorem mem_cellList {a b : ℝ} {p : ℕ} : p ∈ cellList a b ↔ p ∈ cellPrimes a b :=
  Finset.mem_sort _

theorem sum_cellList (a b : ℝ) (f : ℕ → ℝ) :
    ((cellList a b).map f).sum = ∑ p ∈ cellPrimes a b, f p := by
  unfold cellList
  rw [← List.sum_toFinset f (Finset.sort_nodup _ _), Finset.sort_toFinset]

/-- `Π_j = exp(2 a n_j log x_{j+1})`. -/
noncomputable def cellPi (a : ℝ) (x : ℕ → ℝ) (nc : ℕ → ℕ) (j : ℕ) : ℝ :=
  Real.exp (2 * a * nc j * Real.log (x (j + 1)))

/-- `g_j = Π_j / n_j`. -/
noncomputable def cellG (a : ℝ) (x : ℕ → ℝ) (nc : ℕ → ℕ) (j : ℕ) : ℝ := cellPi a x nc j / nc j

/-- **`lem:record:block-charge`(i), inequality `eq:record:cell-charge`, for any error constant**:
for cell points `x_0 ≤ x_1 ≤ … ≤ x_𝗇` (`𝗇 ≥ 1`, `x_0 > 1`), none of them a prime `≡ 3 (mod 4)`,
integers `n_j ≥ 1`, `a ≥ 0`, `s ≥ 0`, and a constant `e` with `|θ(t; 4, 3) - t/2| ≤ e t` on
`[x_0, x_𝗇]`, the blocks of `n_j` consecutive primes `p ≡ 3 (mod 4)` of the cells satisfy
`∑_𝔅 q_𝔅^{2a} b_𝔅^{-s} ≤ ∑_j Π_j x_j^{-s} + (½ + e) ∑_j g_j I_j(s) + e (2 g_0 x_0^{1-s}/log x_0
+ 2 ∑_{0<j<𝗇} (g_j - g_{j-1})_+ x_j^{1-s}/log x_j)` (`cellEdge`). -/
theorem cell_charge {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx0 : 1 < x 0)
    (hmono : ∀ j < n, x j ≤ x (j + 1)) (hend : ∀ j ≤ n, NotPrime3 (x j)) (nc : ℕ → ℕ)
    (hnc : ∀ j < n, 1 ≤ nc j) {a s e : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hθ : ∀ t, x 0 ≤ t → t ≤ x n → |Target.theta4 t 3 - t / 2| ≤ e * t) :
    ∑ j ∈ range n, cellCharge (cellList (x j) (x (j + 1))) (nc j) a s ≤
      ∑ j ∈ range n, cellPi a x nc j * x j ^ (-s) +
        (1 / 2 + e) * ∑ j ∈ range n, cellG a x nc j * cellIntegral s (x j) (x (j + 1)) +
        e * cellEdge n x (cellG a x nc) s := by
  have hx1 : ∀ j ≤ n, 1 < x j := fun j hj => lt_of_lt_of_le hx0 (chain_le hmono (Nat.zero_le j) hj)
  have hg : ∀ j < n, 0 ≤ cellG a x nc j := fun j _ =>
    div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)
  have hcells := cells_sum_upper hn x hx0 hmono hend (cellG a x nc) hg hs hθ
  have hblock : ∀ j ∈ range n, cellCharge (cellList (x j) (x (j + 1))) (nc j) a s ≤
      cellPi a x nc j * x j ^ (-s) +
        cellG a x nc j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-s) := by
    intro j hj
    have hj' := mem_range.mp hj
    have h := cellCharge_le (ps := cellList (x j) (x (j + 1))) (xl := x j) (xr := x (j + 1))
      (hnc j hj') ha hs
      (by linarith [hx1 j hj'.le]) (hx1 (j + 1) hj').le (cellList_sorted _ _)
      (fun p hp => by
        have := mem_cellPrimes.mp (mem_cellList.mp hp)
        exact ⟨this.2.2.1, this.2.2.2⟩)
    rw [sum_cellList] at h
    unfold cellPi cellG
    exact h
  calc ∑ j ∈ range n, cellCharge (cellList (x j) (x (j + 1))) (nc j) a s
      ≤ ∑ j ∈ range n, (cellPi a x nc j * x j ^ (-s) +
          cellG a x nc j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-s)) :=
        Finset.sum_le_sum hblock
    _ = ∑ j ∈ range n, cellPi a x nc j * x j ^ (-s) +
          ∑ j ∈ range n, cellG a x nc j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-s) :=
        Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-! ## The error constant from the literature inputs -/

/-- **From `thm:bmor`**: for `t ≥ x ≥ X_Ch - 1 = 4 800 162 889`,
`|θ(t; 4, 3) - t/2| ≤ 𝖾_x t` with `𝖾_x = 2411/(5·10⁶ log x)`. -/
theorem bmor_eta_le (hB : Target.BMOR) {x t : ℝ} (hx : 4800162889 ≤ x) (hxt : x ≤ t) :
    |Target.theta4 t 3 - t / 2| ≤ 2411 / (5000000 * Real.log x) * t := by
  have h := hB 3 (by simp) t (by linarith)
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlt : Real.log x ≤ Real.log t := Real.log_le_log (by linarith) hxt
  have ht0 : 0 ≤ t := by linarith
  have h1 : t / Real.log t ≤ t / Real.log x := div_le_div_of_nonneg_left ht0 hlx hlt
  have h2 : 2411 / 5000000 * (t / Real.log t) ≤ 2411 / (5000000 * Real.log x) * t := by
    calc 2411 / 5000000 * (t / Real.log t) ≤ 2411 / 5000000 * (t / Real.log x) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 2411 / (5000000 * Real.log x) * t := by field_simp
  exact h.le.trans h2

/-- From a bound `C √t` below `10¹⁰`: for `1 ≤ x ≤ t`, `C √t ≤ (C/√x) t`. -/
theorem sqrt_le_div_sqrt_mul {C x t : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hxt : x ≤ t) :
    C * Real.sqrt t ≤ C / Real.sqrt x * t := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hst : Real.sqrt x ≤ Real.sqrt t := Real.sqrt_le_sqrt hxt
  have ht : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ hsx]
  have : C * Real.sqrt t * Real.sqrt x ≤ C * Real.sqrt t * Real.sqrt t :=
    mul_le_mul_of_nonneg_left hst (mul_nonneg hC (Real.sqrt_nonneg _))
  nlinarith

/-- **From `Target.ThetaSmall` (H2″)**: for `1 ≤ x ≤ t ≤ 10¹⁰`,
`|θ(t; 4, 3) - t/2| ≤ (2.072/√x) t`. -/
theorem thetaSmall_eta_le (hT : Target.ThetaSmall) {x t : ℝ} (hx : 1 ≤ x) (hxt : x ≤ t)
    (ht : t ≤ 10 ^ 10) : |Target.theta4 t 3 - t / 2| ≤ 2072 / 1000 / Real.sqrt x * t :=
  (hT t (by linarith) ht).trans (sqrt_le_div_sqrt_mul (by norm_num) hx hxt)

/-- **From `Target.ThetaSmallTable` (H2′)**: for `1 ≤ x ≤ t ≤ 10¹⁰`,
`|θ(t; 4, 3) - t/2| ≤ (1.034832/√x) t`. -/
theorem thetaSmallTable_eta_le (hT : Target.ThetaSmallTable) {x t : ℝ} (hx : 1 ≤ x) (hxt : x ≤ t)
    (ht : t ≤ 10 ^ 10) : |Target.theta4 t 3 - t / 2| ≤ 1034832 / 1000000 / Real.sqrt x * t :=
  (hT t (by linarith) ht).trans (sqrt_le_div_sqrt_mul (by norm_num) hx hxt)

/-- **`lem:record:block-charge`(i), `eq:record:cell-charge`, with `𝖾 = 𝖾_x` from `thm:bmor`**
(`Target.BMOR`): cells above `X_Ch - 1 = 4 800 162 889`. -/
theorem cell_charge_bmor (hB : Target.BMOR) {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ)
    (hx0 : 4800162889 ≤ x 0) (hmono : ∀ j < n, x j ≤ x (j + 1)) (hend : ∀ j ≤ n, NotPrime3 (x j))
    (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∑ j ∈ range n, cellCharge (cellList (x j) (x (j + 1))) (nc j) a s ≤
      ∑ j ∈ range n, cellPi a x nc j * x j ^ (-s) +
        (1 / 2 + 2411 / (5000000 * Real.log (x 0))) *
          ∑ j ∈ range n, cellG a x nc j * cellIntegral s (x j) (x (j + 1)) +
        2411 / (5000000 * Real.log (x 0)) * cellEdge n x (cellG a x nc) s :=
  cell_charge hn x (by linarith) hmono hend nc hnc ha hs fun t ht _ => bmor_eta_le hB hx0 ht

theorem cell_charge_thetaSmall (hT : Target.ThetaSmall) {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ)
    (hx0 : 1 < x 0) (hxn : x n ≤ 10 ^ 10) (hmono : ∀ j < n, x j ≤ x (j + 1))
    (hend : ∀ j ≤ n, NotPrime3 (x j)) (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∑ j ∈ range n, cellCharge (cellList (x j) (x (j + 1))) (nc j) a s ≤
      ∑ j ∈ range n, cellPi a x nc j * x j ^ (-s) +
        (1 / 2 + 2072 / 1000 / Real.sqrt (x 0)) *
          ∑ j ∈ range n, cellG a x nc j * cellIntegral s (x j) (x (j + 1)) +
        2072 / 1000 / Real.sqrt (x 0) * cellEdge n x (cellG a x nc) s :=
  cell_charge hn x hx0 hmono hend nc hnc ha hs fun _ ht ht' =>
    thetaSmall_eta_le hT hx0.le ht (ht'.trans hxn)

/-- **`eq:record:cell-charge` below `X_Ch`, with `Target.ThetaSmallTable` (H2′)**: cells in
`[1, 10¹⁰]`, `𝖾 = 1.034832/√x_0` (the constant of R1's F1′ evaluation, which uses
`1.034832/⌊√X_i⌋ ≥ 1.034832/√X_i`). -/
theorem cell_charge_thetaSmallTable (hT : Target.ThetaSmallTable) {n : ℕ} (hn : 1 ≤ n)
    (x : ℕ → ℝ) (hx0 : 1 < x 0) (hxn : x n ≤ 10 ^ 10) (hmono : ∀ j < n, x j ≤ x (j + 1))
    (hend : ∀ j ≤ n, NotPrime3 (x j)) (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∑ j ∈ range n, cellCharge (cellList (x j) (x (j + 1))) (nc j) a s ≤
      ∑ j ∈ range n, cellPi a x nc j * x j ^ (-s) +
        (1 / 2 + 1034832 / 1000000 / Real.sqrt (x 0)) *
          ∑ j ∈ range n, cellG a x nc j * cellIntegral s (x j) (x (j + 1)) +
        1034832 / 1000000 / Real.sqrt (x 0) * cellEdge n x (cellG a x nc) s :=
  cell_charge hn x hx0 hmono hend nc hnc ha hs fun _ ht ht' =>
    thetaSmallTable_eta_le hT hx0.le ht (ht'.trans hxn)

/-! ## The paper's geometric cells -/

theorem cellPoint_zero (x Y : ℝ) (n : ℕ) : cellPoint x Y n 0 = x := by
  unfold cellPoint
  simp

theorem cellPoint_self {x Y : ℝ} {n : ℕ} (hn : 1 ≤ n) : cellPoint x Y n n = Y := by
  unfold cellPoint
  have : (n : ℝ) / n = 1 := div_self (by positivity)
  rw [this, sub_self, Real.rpow_zero, Real.rpow_one, one_mul]

/-- `x_j = x (Y/x)^{j/𝗇}`. -/
theorem cellPoint_eq {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) (n j : ℕ) :
    cellPoint x Y n j = x * (Y / x) ^ ((j : ℝ) / n) := by
  unfold cellPoint
  rw [Real.rpow_sub hx, Real.rpow_one, Real.div_rpow hY.le hx.le]
  field_simp

/-- The cell points increase when `0 < x ≤ Y`. -/
theorem cellPoint_mono {x Y : ℝ} (hx : 0 < x) (hxY : x ≤ Y) (n j : ℕ) :
    cellPoint x Y n j ≤ cellPoint x Y n (j + 1) := by
  have hY : 0 < Y := lt_of_lt_of_le hx hxY
  rw [cellPoint_eq hx hY, cellPoint_eq hx hY]
  apply mul_le_mul_of_nonneg_left _ hx.le
  apply Real.rpow_le_rpow_of_exponent_le
  · rw [le_div_iff₀ hx, one_mul]
    exact hxY
  · push_cast
    apply div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- `x_j^𝗇 = x^{𝗇-j} Y^j`. -/
theorem cellPoint_pow {x Y : ℝ} (hx : 0 ≤ x) (hY : 0 ≤ Y) {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ n) :
    cellPoint x Y n j ^ n = x ^ (n - j) * Y ^ j := by
  unfold cellPoint
  have hnR : (n : ℝ) ≠ 0 := by positivity
  rw [mul_pow, ← Real.rpow_natCast (x ^ (1 - (j : ℝ) / n)) n, ← Real.rpow_mul hx,
    ← Real.rpow_natCast (Y ^ ((j : ℝ) / n)) n, ← Real.rpow_mul hY]
  have e1 : (1 - (j : ℝ) / n) * n = ((n - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj]
    field_simp
  have e2 : (j : ℝ) / n * n = (j : ℝ) := by field_simp
  rw [e1, e2, Real.rpow_natCast, Real.rpow_natCast]

/-- **No cell point is a prime `≡ 3 (mod 4)` when `x`, `Y` are even** (the remark after
`def:record:exact-blocks`): `p = x_j` would give `p^𝗇 = x^{𝗇-j} Y^j`, which is even. -/
theorem notPrime3_cellPoint {X Y : ℕ} (hX : Even X) (hY : Even Y) {n j : ℕ} (hn : 1 ≤ n)
    (hj : j ≤ n) : NotPrime3 (cellPoint X Y n j) := by
  intro p hp h3 hpx
  have hpow : ((p ^ n : ℕ) : ℝ) = ((X ^ (n - j) * Y ^ j : ℕ) : ℝ) := by
    push_cast
    rw [hpx, cellPoint_pow (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn hj]
  have hpow' : p ^ n = X ^ (n - j) * Y ^ j := by exact_mod_cast hpow
  have h2 : 2 ∣ p ^ n := by
    rw [hpow']
    rcases Nat.lt_or_ge j n with hjn | hjn
    · exact Dvd.dvd.mul_right (dvd_pow (even_iff_two_dvd.mp hX) (by omega)) _
    · exact Dvd.dvd.mul_left (dvd_pow (even_iff_two_dvd.mp hY) (by omega)) _
  have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2
  have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
  omega

/-- **`lem:record:block-charge`(i) as stated in the paper**: an interval `[x, Y)` with
`x ≥ X_Ch - 1 = 4 800 162 889` and `x ≤ Y` even, the cell points `x_j = x^{1-j/𝗇} Y^{j/𝗇}`
(`0 ≤ j ≤ 𝗇`, V1's `cellPoint`), integers `n_0, …, n_{𝗇-1} ≥ 1`, and the blocks of `n_j` consecutive
primes `p ≡ 3 (mod 4)` of each cell: `eq:record:cell-charge` holds with
`𝖾 = 𝖾_x = 2411/(5·10⁶ log x)`,
from `thm:bmor` (`Target.BMOR`). Here `a, s ≥ 0` (the paper has `a, s > 0`). -/
theorem cell_charge_geometric_bmor (hB : Target.BMOR) {X Y : ℕ} (hX : Even X) (hY : Even Y)
    (hXch : (4800162889 : ℝ) ≤ X) (hXY : X ≤ Y) {n : ℕ} (hn : 1 ≤ n) (nc : ℕ → ℕ)
    (hnc : ∀ j < n, 1 ≤ nc j) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∑ j ∈ range n, cellCharge (cellList (cellPoint X Y n j) (cellPoint X Y n (j + 1))) (nc j) a s ≤
      ∑ j ∈ range n, cellPi a (cellPoint X Y n) nc j * cellPoint X Y n j ^ (-s) +
        (1 / 2 + 2411 / (5000000 * Real.log X)) *
          ∑ j ∈ range n, cellG a (cellPoint X Y n) nc j *
            cellIntegral s (cellPoint X Y n j) (cellPoint X Y n (j + 1)) +
        2411 / (5000000 * Real.log X) *
          cellEdge n (cellPoint X Y n) (cellG a (cellPoint X Y n) nc) s := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXY' : (X : ℝ) ≤ Y := by exact_mod_cast hXY
  have h := cell_charge_bmor hB hn (cellPoint X Y n) (by rw [cellPoint_zero]; exact hXch)
    (fun j _ => cellPoint_mono hX0 hXY' n j) (fun j hj => notPrime3_cellPoint hX hY hn hj) nc hnc
    ha hs
  rw [cellPoint_zero] at h
  exact h

theorem cell_charge_geometric_thetaSmallTable (hT : Target.ThetaSmallTable) {X Y : ℕ}
    (hX : Even X) (hY : Even Y) (hX1 : 1 < X) (hXY : X ≤ Y) (hY10 : (Y : ℝ) ≤ 10 ^ 10) {n : ℕ}
    (hn : 1 ≤ n) (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∑ j ∈ range n, cellCharge (cellList (cellPoint X Y n j) (cellPoint X Y n (j + 1))) (nc j) a s ≤
      ∑ j ∈ range n, cellPi a (cellPoint X Y n) nc j * cellPoint X Y n j ^ (-s) +
        (1 / 2 + 1034832 / 1000000 / Real.sqrt X) *
          ∑ j ∈ range n, cellG a (cellPoint X Y n) nc j *
            cellIntegral s (cellPoint X Y n j) (cellPoint X Y n (j + 1)) +
        1034832 / 1000000 / Real.sqrt X *
          cellEdge n (cellPoint X Y n) (cellG a (cellPoint X Y n) nc) s := by
  have hX1' : (1 : ℝ) < X := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) < X := by linarith
  have hXY' : (X : ℝ) ≤ Y := by exact_mod_cast hXY
  have h := cell_charge_thetaSmallTable hT hn (cellPoint X Y n) (by rw [cellPoint_zero]; exact hX1')
    (by rw [cellPoint_self hn]; exact hY10) (fun j _ => cellPoint_mono hX0 hXY' n j)
    (fun j hj => notPrime3_cellPoint hX hY hn hj) nc hnc ha hs
  rw [cellPoint_zero] at h
  exact h

/-- **`eq:record:cell-charge` for the geometric cells below `X_Ch`, with `Target.ThetaSmall`
(H2″)**: as `cell_charge_geometric_thetaSmallTable`, with `𝖾 = 2.072/√x`. -/
theorem cell_charge_geometric_thetaSmall (hT : Target.ThetaSmall) {X Y : ℕ}
    (hX : Even X) (hY : Even Y) (hX1 : 1 < X) (hXY : X ≤ Y) (hY10 : (Y : ℝ) ≤ 10 ^ 10) {n : ℕ}
    (hn : 1 ≤ n) (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) :
    ∑ j ∈ range n, cellCharge (cellList (cellPoint X Y n j) (cellPoint X Y n (j + 1))) (nc j) a s ≤
      ∑ j ∈ range n, cellPi a (cellPoint X Y n) nc j * cellPoint X Y n j ^ (-s) +
        (1 / 2 + 2072 / 1000 / Real.sqrt X) *
          ∑ j ∈ range n, cellG a (cellPoint X Y n) nc j *
            cellIntegral s (cellPoint X Y n j) (cellPoint X Y n (j + 1)) +
        2072 / 1000 / Real.sqrt X *
          cellEdge n (cellPoint X Y n) (cellG a (cellPoint X Y n) nc) s := by
  have hX1' : (1 : ℝ) < X := by exact_mod_cast hX1
  have hX0 : (0 : ℝ) < X := by linarith
  have hXY' : (X : ℝ) ≤ Y := by exact_mod_cast hXY
  have h := cell_charge_thetaSmall hT hn (cellPoint X Y n) (by rw [cellPoint_zero]; exact hX1')
    (by rw [cellPoint_self hn]; exact hY10) (fun j _ => cellPoint_mono hX0 hXY' n j)
    (fun j hj => notPrime3_cellPoint hX hY hn hj) nc hnc ha hs
  rw [cellPoint_zero] at h
  exact h

end Sarkozy.Misc
