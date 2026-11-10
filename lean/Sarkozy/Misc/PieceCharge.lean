module

public import Sarkozy.Misc.BlockChargeExact

@[expose] public section

/-!
# The charges of a middle piece (`lem:record:block-charge`, closing sentence)

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`: "In particular, for every
middle piece `[X,Y)` and `d ∈ {2,3,4}`, `b_d(X,Y)` is at most the sum of (ii) over the parts of the
piece below `X_Ch` and of `eq:record:cell-charge` with `s = d/2` over its cells above `X_Ch`",
where `b_d(X,Y) = ∑_{𝔅 ⊆ [X,Y)} q_𝔅^{2a} b_𝔅^{-d/2}` is the sum over the middle blocks of the
piece (`subsec:record:middle_blocks`).

A piece is given by its partition data (`MiddlePiece`, `def:record:exact-blocks`):
* the parts below `X_Ch`, each as the list of its primes `≡ 3 (mod 4)` in increasing order; their
  blocks are V1's greedy blocks (`PartV.greedyBlocks`, `def:record:exact-blocks`(c));
* the cells above `X_Ch`, by their points `x_0 ≤ … ≤ x_𝗇` and cardinalities `n_j`; their blocks are
  V1's `PartV.cellBlock`s of the cell's primes (`def:record:exact-blocks`(d)); `𝗇 = 0` if the
  piece has no cell.

`pieceCharge u P a d` is `b_d(X,Y)` for this partition. **`piece_charge_le`** is the sentence for
any error constant `𝖾` on the cells, **`piece_charge_le_bmor`** with `Target.BMOR` (H2) and
`𝖾 = 𝖾_{x_0}`. The bounds are the fork's `block_charge_greedy` (part (ii)) and `cell_charge`
(part (i)), added over the parts and the cells.
-/

namespace Sarkozy.Misc

open Finset Sarkozy.PartV Sarkozy.PartVLaws

/-- The partition data of a middle piece. -/
structure MiddlePiece where
  /-- the primes `≡ 3 (mod 4)` of each part below `X_Ch`, in increasing order -/
  parts : List (List ℕ)
  /-- the number of cells above `X_Ch` (`0` if there is none) -/
  n : ℕ
  /-- the cell points `x_0 ≤ … ≤ x_𝗇` -/
  x : ℕ → ℝ
  /-- the block cardinalities `n_j` of the cells -/
  nc : ℕ → ℕ

/-- The charge `q_𝔅^{2a} b_𝔅^{-d/2}` of one exact block. -/
noncomputable def exactTerm (a : ℝ) (d : ℕ) (B : List ℕ) : ℝ :=
  ((B.prod : ℕ) : ℝ) ^ (2 * a) * ((B.headD 0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2)

/-- **`b_d(X,Y)`** for the partition of a piece: the charges of the exact blocks of its parts
and of the blocks of its cells. -/
noncomputable def pieceCharge (u : ℕ → ℕ) (P : MiddlePiece) (a : ℝ) (d : ℕ) : ℝ :=
  (P.parts.map fun ps => ((greedyBlocks u integerBudget ps).map (exactTerm a d)).sum).sum +
    ∑ j ∈ range P.n, cellCharge (cellList (P.x j) (P.x (j + 1))) (P.nc j) a ((d : ℝ) / 2)

/-- The bound (ii) of one part:
`∑_{k=1}^{2¹⁶} exp(2a 𝔲_* k/2⁵⁶) w_d(𝔭, k)/2⁹⁵`. -/
noncomputable def exactBound (u : ℕ → ℕ) (a : ℝ) (d : ℕ) (ps : List ℕ) : ℝ :=
  ∑ k ∈ Icc (1 : ℕ) (2 ^ 16), Real.exp (2 * a * integerBudget * (k : ℝ) / 2 ^ 56) *
    ((((greedyBlocks u integerBudget ps).filter fun B => blockBin u B = k).map
      fun B => (wd d (B.headD 0) : ℝ)).sum / 2 ^ 95)

/-- The right side of `eq:record:cell-charge` for the cells of the piece, with error constant
`𝖾`; `0` if the piece has no cell. -/
noncomputable def cellBound (P : MiddlePiece) (a s e : ℝ) : ℝ :=
  if P.n = 0 then 0 else
    ∑ j ∈ range P.n, cellPi a P.x P.nc j * P.x j ^ (-s) +
      (1 / 2 + e) * ∑ j ∈ range P.n, cellG a P.x P.nc j * cellIntegral s (P.x j) (P.x (j + 1)) +
      e * cellEdge P.n P.x (cellG a P.x P.nc) s

/-- The hypotheses of (ii) on the parts of a piece. -/
def PartsOK (u : ℕ → ℕ) (P : MiddlePiece) : Prop :=
  ∀ ps ∈ P.parts, ps ≠ [] ∧ (∀ p ∈ ps, 0 < p) ∧ (∀ p ∈ ps, 1 ≤ u p) ∧
    ∀ p ∈ ps, Real.log p < (u p : ℝ) / 2 ^ 40

/-- The hypotheses of (i) on the cells of a piece. -/
def CellsOK (P : MiddlePiece) : Prop :=
  1 < P.x 0 ∧ (∀ j < P.n, P.x j ≤ P.x (j + 1)) ∧ (∀ j ≤ P.n, NotPrime3 (P.x j)) ∧
    ∀ j < P.n, 1 ≤ P.nc j

/-- **`lem:record:block-charge`, closing sentence, for any error constant on the cells**: for a
piece with parts satisfying the hypotheses of (ii) and cells satisfying those of (i) with
`|θ(t; 4, 3) - t/2| ≤ 𝖾 t` on `[x_0, x_𝗇]`, and `d ∈ {2, 3, 4}`,
`b_d(X,Y) ≤ ∑_{parts} (ii) + eq:record:cell-charge` with `s = d/2`. -/
theorem piece_charge_le (u : ℕ → ℕ) (hu : ∀ p, u p ≤ integerBudget) (P : MiddlePiece)
    (hparts : PartsOK u P) (hcells : 1 ≤ P.n → CellsOK P) {a e : ℝ} (ha : 0 ≤ a) {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4)
    (hθ : 1 ≤ P.n → ∀ t, P.x 0 ≤ t → t ≤ P.x P.n → |Target.theta4 t 3 - t / 2| ≤ e * t) :
    pieceCharge u P a d ≤ (P.parts.map (exactBound u a d)).sum + cellBound P a ((d : ℝ) / 2) e := by
  unfold pieceCharge
  apply add_le_add
  · apply List.sum_le_sum
    intro ps hps
    obtain ⟨hne, hpos, hu1, hlog⟩ := hparts ps hps
    exact block_charge_greedy u hu ps hne hpos hu1 hlog ha hd
  · unfold cellBound
    split_ifs with h0
    · simp [h0]
    · have hn : 1 ≤ P.n := Nat.one_le_iff_ne_zero.mpr h0
      obtain ⟨hx0, hmono, hend, hnc⟩ := hcells hn
      exact cell_charge hn P.x hx0 hmono hend P.nc hnc ha (by positivity) (hθ hn)

/-- **`lem:record:block-charge`, closing sentence, with `thm:bmor`** (`Target.BMOR`, H2): for a
piece whose cells start at `x_0 ≥ 4800162889` (above `X_Ch - 1`), with
`𝖾 = 2411/(5000000 log x_0)`. -/
theorem piece_charge_le_bmor (hB : Target.BMOR) (u : ℕ → ℕ) (hu : ∀ p, u p ≤ integerBudget)
    (P : MiddlePiece) (hparts : PartsOK u P) (hcells : 1 ≤ P.n → CellsOK P)
    (hXCh : 1 ≤ P.n → 4800162889 ≤ P.x 0) {a : ℝ} (ha : 0 ≤ a) {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4) :
    pieceCharge u P a d ≤ (P.parts.map (exactBound u a d)).sum +
      cellBound P a ((d : ℝ) / 2) (2411 / (5000000 * Real.log (P.x 0))) :=
  piece_charge_le u hu P hparts hcells ha hd fun hn _ ht _ => bmor_eta_le hB (hXCh hn) ht

/-- Non-vacuity: a piece with the one-prime part `[3]` (`𝔲 ≡ 2⁴¹`) and no cell. -/
example :=
  piece_charge_le (fun _ => 2 ^ 41) (fun _ => by unfold integerBudget middleBudget; norm_num)
    ⟨[[3]], 0, fun _ => 2, fun _ => 1⟩
    (by
      intro ps hps
      simp only [List.mem_singleton] at hps
      subst hps
      refine ⟨by simp, by simp, by simp, ?_⟩
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      have h3 : Real.log 3 < 2 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        have := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
        linarith
      have he : ((2 ^ 41 : ℕ) : ℝ) / 2 ^ 40 = 2 := by norm_num
      rw [he]
      exact_mod_cast h3)
    (fun h => absurd h (by norm_num)) (a := 1) (e := 0) zero_le_one (d := 2) (Or.inl rfl)
    (fun h => absurd h (by norm_num))

end Sarkozy.Misc
