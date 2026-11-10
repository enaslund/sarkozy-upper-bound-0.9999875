module

public import Sarkozy.Misc.BlockCharge

@[expose] public section

/-!
# Lower start sums (`lem:record:lower-start-sums`)

`paper/sections/20_middle_reference.tex`, `lem:record:lower-start-sums`.

* (i) (`lower_start_sums_cells`, and `lower_start_sums_cells_bmor` with `thm:bmor`): in the
  setting of `lem:record:block-charge`(i),
  `∑_𝔅 b_𝔅^{-1} ≥ (½ - 𝖾) ∑_j n_j^{-1} log(log x_{j+1}/log x_j)
  - 2𝖾 (1/(n_0 log x) + ∑_{0<j<𝗇} (1/n_j - 1/n_{j-1})_+ / log x_j)`.
  The proof is the paper's: a block has at most `n_j` primes, all at least its start, so
  `∑_𝔅 b_𝔅^{-1} ≥ ∑_j n_j^{-1} ∑_{p ∈ cell j} p^{-1}` (`cellStartSum_ge`), and the partial summation
  of `lem:record:block-charge`(i) with `s = 1` and `g_j = 1/n_j`, the error subtracted
  (`cells_sum_lower`), with `I_j(1) = log(log x_{j+1}/log x_j)` (`cellIntegral_one`).
* (ii) (`lower_start_sums_exact`): for any list of blocks with positive starts `b_𝔅` (in particular
  the exact blocks `Sarkozy.PartV.greedyBlocks` of a part, `def:record:exact-blocks`(c)),
  `∑_𝔅 b_𝔅^{-1} ≥ (∑_𝔅 w₂(𝔅) - #𝔅)/2⁹⁵` with `w₂(𝔅) = ⌈2⁹⁵/b_𝔅⌉`, since `w₂ < 2⁹⁵/b + 1`.
-/

open Finset

namespace Sarkozy.Misc

open Sarkozy.PartV

/-- **`lem:record:lower-start-sums`(i), for any error constant `𝖾`** with `|θ(t; 4, 3) - t/2| ≤ 𝖾 t`
on `[x_0, x_𝗇]`: cell points `x_0 ≤ … ≤ x_𝗇` (`𝗇 ≥ 1`, `x_0 > 1`), none a prime `≡ 3 (mod 4)`, and
blocks of `n_j ≥ 1` consecutive primes `p ≡ 3 (mod 4)` of each cell. -/
theorem lower_start_sums_cells {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ) (hx0 : 1 < x 0)
    (hmono : ∀ j < n, x j ≤ x (j + 1)) (hend : ∀ j ≤ n, NotPrime3 (x j)) (nc : ℕ → ℕ)
    (hnc : ∀ j < n, 1 ≤ nc j) {e : ℝ}
    (hθ : ∀ t, x 0 ≤ t → t ≤ x n → |Target.theta4 t 3 - t / 2| ≤ e * t) :
    (1 / 2 - e) * ∑ j ∈ range n, 1 / (nc j : ℝ) * Real.log (Real.log (x (j + 1)) / Real.log (x j)) -
        2 * e * (1 / ((nc 0 : ℝ) * Real.log (x 0)) +
          ∑ j ∈ Ico 1 n, max (1 / (nc j : ℝ) - 1 / (nc (j - 1) : ℝ)) 0 / Real.log (x j)) ≤
      ∑ j ∈ range n, cellStartSum (cellList (x j) (x (j + 1))) (nc j) := by
  have hx1 : ∀ j ≤ n, 1 < x j := fun j hj => lt_of_lt_of_le hx0 (chain_le hmono (Nat.zero_le j) hj)
  set g : ℕ → ℝ := fun j => 1 / (nc j : ℝ) with hgdef
  have hg : ∀ j < n, 0 ≤ g j := fun j _ => by positivity
  have hlow := cells_sum_lower hn x hx0 hmono hend g hg zero_le_one hθ
  -- the main term
  have hI : ∑ j ∈ range n, g j * cellIntegral 1 (x j) (x (j + 1)) =
      ∑ j ∈ range n, 1 / (nc j : ℝ) * Real.log (Real.log (x (j + 1)) / Real.log (x j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [cellIntegral_one (hx1 j hj'.le) (hmono j hj')]
  -- the edge terms
  have hE : cellEdge n x g 1 = 2 * (1 / ((nc 0 : ℝ) * Real.log (x 0)) +
      ∑ j ∈ Ico 1 n, max (1 / (nc j : ℝ) - 1 / (nc (j - 1) : ℝ)) 0 / Real.log (x j)) := by
    unfold cellEdge
    simp only [sub_self, Real.rpow_zero, hgdef]
    rw [mul_add]
    congr 1
    · ring
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
  -- the block step
  have hB : ∑ j ∈ range n, g j * ∑ p ∈ cellPrimes (x j) (x (j + 1)), (p : ℝ) ^ (-(1 : ℝ)) ≤
      ∑ j ∈ range n, cellStartSum (cellList (x j) (x (j + 1))) (nc j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    have h := cellStartSum_ge (ps := cellList (x j) (x (j + 1))) (hnc j hj') (cellList_sorted _ _)
      (fun p hp => (mem_cellPrimes.mp (mem_cellList.mp hp)).1.pos)
    rw [sum_cellList] at h
    simp only [Real.rpow_neg_one]
    exact h
  rw [hI, hE] at hlow
  linarith

/-- **`lem:record:lower-start-sums`(i) with `thm:bmor`**: cells above `X_Ch - 1 = 4 800 162 889`,
`𝖾 = 𝖾_x = 2411/(5·10⁶ log x)`. -/
theorem lower_start_sums_cells_bmor (hB : Target.BMOR) {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ)
    (hx0 : 4800162889 ≤ x 0) (hmono : ∀ j < n, x j ≤ x (j + 1)) (hend : ∀ j ≤ n, NotPrime3 (x j))
    (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) :
    (1 / 2 - 2411 / (5000000 * Real.log (x 0))) *
        ∑ j ∈ range n, 1 / (nc j : ℝ) * Real.log (Real.log (x (j + 1)) / Real.log (x j)) -
        2 * (2411 / (5000000 * Real.log (x 0))) * (1 / ((nc 0 : ℝ) * Real.log (x 0)) +
          ∑ j ∈ Ico 1 n, max (1 / (nc j : ℝ) - 1 / (nc (j - 1) : ℝ)) 0 / Real.log (x j)) ≤
      ∑ j ∈ range n, cellStartSum (cellList (x j) (x (j + 1))) (nc j) :=
  lower_start_sums_cells hn x (by linarith) hmono hend nc hnc fun _ ht _ => bmor_eta_le hB hx0 ht

/-- **`lem:record:lower-start-sums`(i) below `X_Ch` with `Target.ThetaSmallTable` (H2′)**: cells in
`[1, 10¹⁰]`, `𝖾 = 1.034832/√x_0` (R1's F1′ lower start sums). -/
theorem lower_start_sums_cells_thetaSmallTable (hT : Target.ThetaSmallTable) {n : ℕ} (hn : 1 ≤ n)
    (x : ℕ → ℝ) (hx0 : 1 < x 0) (hxn : x n ≤ 10 ^ 10) (hmono : ∀ j < n, x j ≤ x (j + 1))
    (hend : ∀ j ≤ n, NotPrime3 (x j)) (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) :
    (1 / 2 - 1034832 / 1000000 / Real.sqrt (x 0)) *
        ∑ j ∈ range n, 1 / (nc j : ℝ) * Real.log (Real.log (x (j + 1)) / Real.log (x j)) -
        2 * (1034832 / 1000000 / Real.sqrt (x 0)) * (1 / ((nc 0 : ℝ) * Real.log (x 0)) +
          ∑ j ∈ Ico 1 n, max (1 / (nc j : ℝ) - 1 / (nc (j - 1) : ℝ)) 0 / Real.log (x j)) ≤
      ∑ j ∈ range n, cellStartSum (cellList (x j) (x (j + 1))) (nc j) :=
  lower_start_sums_cells hn x hx0 hmono hend nc hnc fun _ ht ht' =>
    thetaSmallTable_eta_le hT hx0.le ht (ht'.trans hxn)

/-- **`lem:record:lower-start-sums`(i) below `X_Ch` with `Target.ThetaSmall` (H2″)**: cells in
`[1, 10¹⁰]`, `𝖾 = 2.072/√x_0`. -/
theorem lower_start_sums_cells_thetaSmall (hT : Target.ThetaSmall) {n : ℕ} (hn : 1 ≤ n)
    (x : ℕ → ℝ) (hx0 : 1 < x 0) (hxn : x n ≤ 10 ^ 10) (hmono : ∀ j < n, x j ≤ x (j + 1))
    (hend : ∀ j ≤ n, NotPrime3 (x j)) (nc : ℕ → ℕ) (hnc : ∀ j < n, 1 ≤ nc j) :
    (1 / 2 - 2072 / 1000 / Real.sqrt (x 0)) *
        ∑ j ∈ range n, 1 / (nc j : ℝ) * Real.log (Real.log (x (j + 1)) / Real.log (x j)) -
        2 * (2072 / 1000 / Real.sqrt (x 0)) * (1 / ((nc 0 : ℝ) * Real.log (x 0)) +
          ∑ j ∈ Ico 1 n, max (1 / (nc j : ℝ) - 1 / (nc (j - 1) : ℝ)) 0 / Real.log (x j)) ≤
      ∑ j ∈ range n, cellStartSum (cellList (x j) (x (j + 1))) (nc j) :=
  lower_start_sums_cells hn x hx0 hmono hend nc hnc fun _ ht ht' =>
    thetaSmall_eta_le hT hx0.le ht (ht'.trans hxn)

/-! ## (ii) Exact blocks -/

/-- The rounded weight `w₂(𝔅) = ⌈2⁹⁵ / b_𝔅⌉` (`lem:record:block-charge`(ii)). -/
noncomputable def w2 (b : ℕ) : ℕ := ⌈(2 : ℝ) ^ 95 / b⌉₊

/-- **`lem:record:lower-start-sums`(ii)**: for blocks with positive starts `b_𝔅 = 𝔅.headD 0` (the
first prime of the block), `∑_𝔅 b_𝔅^{-1} ≥ (∑_𝔅 w₂(𝔅) - #𝔅)/2⁹⁵`. -/
theorem lower_start_sums_exact (blocks : List (List ℕ)) (hpos : ∀ B ∈ blocks, 0 < B.headD 0) :
    ((blocks.map fun B => (w2 (B.headD 0) : ℝ)).sum - blocks.length) / 2 ^ 95 ≤
      (blocks.map fun B => ((B.headD 0 : ℕ) : ℝ)⁻¹).sum := by
  induction blocks with
  | nil => simp
  | cons B bs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hB := hpos B List.mem_cons_self
    have ih' := ih (fun B' hB' => hpos B' (List.mem_cons_of_mem B hB'))
    have hb : (0 : ℝ) < (B.headD 0 : ℕ) := by exact_mod_cast hB
    have hc : (w2 (B.headD 0) : ℝ) < 2 ^ 95 / (B.headD 0 : ℕ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h1 : (w2 (B.headD 0) : ℝ) - 1 ≤ 2 ^ 95 * ((B.headD 0 : ℕ) : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv]
      linarith
    rw [div_le_iff₀ (by positivity)] at ih' ⊢
    nlinarith

/-- The greedy blocks of a nonempty list are nonempty when every single `𝔲(p) ≤ 𝔲_*`. -/
theorem greedyAux_ne_nil (u : ℕ → ℕ) (U : ℕ) (hu : ∀ p, u p ≤ U) :
    ∀ (ps cur : List ℕ) (s : ℕ), (cur.map u).sum = s → (cur ≠ [] ∨ ps ≠ []) →
      ∀ B ∈ greedyAux u U ps cur s, B ≠ []
  | [], cur, s, _, hne => by
      intro B hB
      simp only [greedyAux, List.mem_singleton] at hB
      subst hB
      rcases hne with h | h
      · exact List.reverse_ne_nil_iff.mpr h
      · exact absurd rfl h
  | p :: ps, cur, s, hs, _ => by
      intro B hB
      unfold greedyAux at hB
      split_ifs at hB with h
      · exact greedyAux_ne_nil u U hu ps (p :: cur) (s + u p) (by simp [hs, add_comm])
          (Or.inl (List.cons_ne_nil p cur)) B hB
      · rcases List.mem_cons.mp hB with rfl | hB
        · intro hnil
          have hc : cur = [] := List.reverse_eq_nil_iff.mp hnil
          subst hc
          simp only [List.map_nil, List.sum_nil] at hs
          subst hs
          exact h (by simpa using hu p)
        · exact greedyAux_ne_nil u U hu ps [p] (u p) (by simp) (Or.inl (List.cons_ne_nil p []))
            B hB

theorem greedyBlocks_ne_nil (u : ℕ → ℕ) (U : ℕ) (hu : ∀ p, u p ≤ U) {ps : List ℕ}
    (hps : ps ≠ []) : ∀ B ∈ greedyBlocks u U ps, B ≠ [] :=
  greedyAux_ne_nil u U hu ps [] 0 (by simp) (Or.inr hps)

/-- **`lem:record:lower-start-sums`(ii) for the exact blocks of a part** (V1's greedy blocks
`Sarkozy.PartV.greedyBlocks u U ps` of `def:record:exact-blocks`(c), for a nonempty list `ps` of
positive integers, when every single `𝔲(p) ≤ 𝔲_*`). -/
theorem lower_start_sums_greedy (u : ℕ → ℕ) (U : ℕ) (hu : ∀ p, u p ≤ U) (ps : List ℕ)
    (hps0 : ps ≠ []) (hps : ∀ p ∈ ps, 0 < p) :
    (((Sarkozy.PartV.greedyBlocks u U ps).map fun B => (w2 (B.headD 0) : ℝ)).sum -
        (Sarkozy.PartV.greedyBlocks u U ps).length) / 2 ^ 95 ≤
      ((Sarkozy.PartV.greedyBlocks u U ps).map fun B => ((B.headD 0 : ℕ) : ℝ)⁻¹).sum := by
  apply lower_start_sums_exact
  intro B hB
  have hne := greedyBlocks_ne_nil u U hu hps0 B hB
  obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hmem : b ∈ ps := by
    rw [← Sarkozy.PartV.greedyBlocks_flatten u U ps]
    exact List.mem_flatten.mpr ⟨b :: B', hB, List.mem_cons_self⟩
  simpa using hps b hmem

end Sarkozy.Misc
