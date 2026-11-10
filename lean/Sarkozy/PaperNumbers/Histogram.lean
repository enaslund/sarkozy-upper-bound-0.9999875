module

public import Sarkozy.PaperNumbers.Costs
public import Sarkozy.PaperNumbers.HistData

@[expose] public section

/-!
# The 66 charge bounds from the histogram certificate and the cell bounds

`paper/sections/D_certificates.tex`, `cert:record:middle-price`(b), (c);
`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`.

`main_target_paper_joint_N1_final` takes the 66 bounds `pieceBound a_T d i ≤ c_d(i)`. Here they are
derived, at `a_T` directly (no repricing), from two precisely stated inputs. (Since RG's rebase of
7 November 2026, `a_T` here is the ledger's exponent `TargetLedger.targetDecay = a_G = 71/10⁵`, and
`deltaQ`, `expDeltaWitness`, `cellC₂`, `cellC₃` are regenerated there.)

* **`HistogramClaim`** (`cert:record:middle-price`(b), the sieve certificate): for each of the 35
  parts, each `d ∈ {2, 3}` and each price bucket `b`, the sum of M2's `w_d(b_𝔅)` over the greedy
  blocks of the part in bucket `b` is at most the recorded value `histAt p d b` (the C++ sieve's
  `exact_block_histogram.csv`, budget `570`; the sieve computes exactly M2's `blockBin`, `w2`,
  `w3`). This is a statement about the primes `≡ 3 (mod 4)` below `X_Ch`; it is not checked here.
* **`CellClaim`**: the cell part `cellBound` (`eq:record:cell-charge` with `thm:bmor`'s error) of
  each of the five pieces above `X_Ch`, `d ∈ {2, 3}`, at `a_T`, is at most the recorded `cellC_d(i)`
  (the pipeline's certified `fixed_count_charge`). This is a statement about explicit integrals and
  exponentials of the cell points; it is not checked here.

**Proved** (`exactBound_le_hist`, `pieceBound_le_charge`): for each part, M2's `exactBound` at `a_T`
is at most `∑_buckets exp(2 a_T 𝔲_* b/2⁵⁶) histAt/2⁹⁵`, with `exp(2 a_T 𝔲_* b/2⁵⁶) = exp(δ)^b`
bounded by a Taylor witness and a rounded-up fixed-point power (`powUp`); then the 66 bounds
`exact part + cellC_d(i) ≤ c_d(i)` by `decide +kernel` (10737 buckets). The repricing factor and the
under-full last blocks play no role: every block, full or not, is priced at `a_T` in its own bucket.

**`main_target_paper_joint_N1_hist`**: the main statement with `HistogramClaim` and `CellClaim` in
place of the 66 numerical hypotheses.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.PaperNumbers

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.Certificates Sarkozy.PartVLaws
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-! ## Fixed-point powers rounded up -/

/-- The fixed-point unit `10³⁰`. -/
def unitD : ℕ := 10 ^ 30

/-- `x y / D`, rounded up. -/
def mulUp (D x y : ℕ) : ℕ := (x * y + D - 1) / D

/-- One step of the binary power: square, and multiply by `E` if `odd`. -/
def sqMul (D h E : ℕ) (odd : Bool) : ℕ := if odd then mulUp D (mulUp D h h) E else mulUp D h h

/-- **An upper bound of `(E/D)^b · D`** by binary powering with upward rounding (`f` is fuel). -/
def powUp (D : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => D
  | f + 1, E, b => if b = 0 then D else sqMul D (powUp D f E (b / 2)) E (b % 2 == 1)

theorem unitD_pos : (0 : ℝ) < unitD := by unfold unitD; positivity

theorem mulUp_spec {D : ℕ} (hD : 0 < D) (x y : ℕ) :
    (x : ℝ) / D * ((y : ℝ) / D) ≤ (mulUp D x y : ℝ) / D := by
  have hn : x * y ≤ D * mulUp D x y := by
    unfold mulUp
    have hdm := Nat.div_add_mod (x * y + D - 1) D
    have hlt := Nat.mod_lt (x * y + D - 1) hD
    omega
  have hnR : (x : ℝ) * y ≤ D * (mulUp D x y : ℝ) := by exact_mod_cast hn
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hD' hD') hD']
  calc (x : ℝ) * y * D ≤ D * (mulUp D x y : ℝ) * D := mul_le_mul_of_nonneg_right hnR hD'.le
    _ = (mulUp D x y : ℝ) * (D * D) := by ring

theorem list_sum_div_const {α : Type} (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map fun e => f e / c).sum = (L.map f).sum / c := by
  induction L with
  | nil => simp
  | cons e L ih => simp only [List.map_cons, List.sum_cons, ih, add_div]

/-- **`(E/D)^b ≤ powUp D f E b / D`** for `b < 2^f`. -/
theorem powUp_spec {D : ℕ} (hD : 0 < D) (E : ℕ) : ∀ (f b : ℕ), b < 2 ^ f →
    ((E : ℝ) / D) ^ b ≤ (powUp D f E b : ℝ) / D
  | 0, b, hb => by
      have : b = 0 := by simpa using hb
      subst this
      have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      simp [powUp, div_self hD']
  | f + 1, b, hb => by
      have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      by_cases h0 : b = 0
      · subst h0
        simp [powUp, div_self hD']
      · have hb2 : b / 2 < 2 ^ f := by
          rw [pow_succ] at hb
          omega
        have ih := powUp_spec hD E f (b / 2) hb2
        have hE0 : (0 : ℝ) ≤ (E : ℝ) / D := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hpow0 : (0 : ℝ) ≤ ((E : ℝ) / D) ^ (b / 2) := pow_nonneg hE0 _
        have hsq : (((E : ℝ) / D) ^ (b / 2)) ^ 2 ≤
            (mulUp D (powUp D f E (b / 2)) (powUp D f E (b / 2)) : ℝ) / D := by
          rw [sq]
          exact (mul_le_mul ih ih hpow0 (hpow0.trans ih)).trans (mulUp_spec hD _ _)
        simp only [powUp, h0, ↓reduceIte, sqMul]
        rcases Nat.mod_two_eq_zero_or_one b with h | h
        · have hb' : ((E : ℝ) / D) ^ b = (((E : ℝ) / D) ^ (b / 2)) ^ 2 := by
            rw [← pow_mul]
            congr 1
            omega
          simp only [h]
          rw [hb']
          exact hsq
        · have hb' : ((E : ℝ) / D) ^ b = (((E : ℝ) / D) ^ (b / 2)) ^ 2 * ((E : ℝ) / D) := by
            rw [← pow_mul, ← pow_succ]
            congr 1
            omega
          simp only [h]
          rw [hb']
          exact (mul_le_mul_of_nonneg_right hsq hE0).trans (mulUp_spec hD _ _)

/-! ## The exponential of a bucket -/

/-- `δ = 2 a_T 𝔲_*/2⁵⁶`. -/
def deltaQ : ℚ := 2 * (71 / 100000) * (2 ^ 40 * 570) / 2 ^ 56

theorem expDelta_valid : expDeltaWitness.Valid deltaQ ⟨0, expUpper expDeltaWitness⟩ := by
  unfold ExpWitness.Valid
  decide +kernel

theorem expDelta_le_E : expUpper expDeltaWitness ≤ (expDeltaE : ℚ) / (10 ^ 30 : ℚ) := by
  decide +kernel

/-- **`exp(2 a_T 𝔲_* b/2⁵⁶) ≤ powUp 20 E b / 10³⁰`** for `b ≤ 2¹⁶`. -/
theorem exp_bucket_le {b : ℕ} (hb : b ≤ 2 ^ 16) :
    Real.exp (2 * targetDecay * integerBudget * (b : ℝ) / 2 ^ 56) ≤
      (powUp unitD 20 expDeltaE b : ℝ) / unitD := by
  have hδ : (2 * targetDecay * integerBudget * (b : ℝ) / 2 ^ 56) = b * (deltaQ : ℝ) := by
    unfold targetDecay deltaQ integerBudget middleBudget
    push_cast
    ring
  have h1 : Real.exp (deltaQ : ℝ) ≤ (expDeltaE : ℝ) / unitD := by
    have h : Real.exp (deltaQ : ℝ) ≤ (expUpper expDeltaWitness : ℝ) :=
      (ExpWitness.sound expDelta_valid).2
    have h2 : ((expUpper expDeltaWitness : ℚ) : ℝ) ≤
        (((expDeltaE : ℚ) / (10 ^ 30 : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast expDelta_le_E
    have hD : (unitD : ℝ) = 10 ^ 30 := by unfold unitD; norm_num
    rw [hD]
    push_cast at h2
    exact h.trans h2
  rw [hδ, Real.exp_nat_mul]
  calc Real.exp (deltaQ : ℝ) ^ b ≤ ((expDeltaE : ℝ) / unitD) ^ b :=
        pow_le_pow_left₀ (Real.exp_pos _).le h1 b
    _ ≤ _ := powUp_spec (by unfold unitD; positivity) expDeltaE 20 b (by omega)

/-! ## The histogram and the claims -/

/-- The recorded `w_d` sum of an entry `(bucket, w₂, w₃)`. -/
def wsel (d : ℕ) (e : ℕ × ℕ × ℕ) : ℕ := if d = 2 then e.2.1 else e.2.2

/-- The histogram of part `k` (empty for `k ≥ 35`). -/
def histN (k : ℕ) : List (ℕ × ℕ × ℕ) := if h : k < 35 then hist ⟨k, h⟩ else []

/-- The recorded `w_d` sum of part `k` in bucket `b`. -/
def histAt (k d b : ℕ) : ℕ := ((histN k).map fun e => if e.1 = b then wsel d e else 0).sum

/-- **The histogram certificate** (`cert:record:middle-price`(b), *hypothesis*): for every part
`k < 35`, `d ∈ {2, 3}` and bucket `b ∈ [1, 2¹⁶]`, the sum of `w_d(b_𝔅)` over the greedy blocks of
part `k` with price bucket `b` is at most the recorded `histAt k d b`. -/
def HistogramClaim : Prop :=
  ∀ k < 35, ∀ d : ℕ, (d = 2 ∨ d = 3) → ∀ b ∈ Icc 1 (2 ^ 16),
    (((greedyOf k).filter fun B => blockBin binU B = b).map fun B => Misc.wd d (B.headD 0)).sum ≤
      histAt k d b

/-- The recorded cell bounds. -/
def cellC (d : ℕ) (i : Fin 33) : ℚ := if d = 2 then cellC2 i else cellC3 i

/-- **The cell bounds** (`eq:record:cell-charge` with `thm:bmor`'s error, at `a_T`; *hypothesis*,
numerical): on each of the five pieces above `X_Ch` and for `d ∈ {2, 3}`, the cell part of M2's
bound is at most the recorded `cellC d i`. -/
def CellClaim : Prop :=
  ∀ i : Fin 33, 28 ≤ i.val → ∀ d : ℕ, (d = 2 ∨ d = 3) →
    Misc.cellBound (paperPiece i) targetDecay ((d : ℝ) / 2)
      (2411 / (5000000 * Real.log ((paperPiece i).x 0))) ≤ (cellC d i : ℝ)

/-! ## The exact part of a piece -/

/-- The fixed-point sum `∑_buckets powUp(b) w_d` of part `k`. -/
def partSumN (k d : ℕ) : ℕ := ((histN k).map fun e => powUp unitD 20 expDeltaE e.1 * wsel d e).sum

/-- The fixed-point exact part of piece `i`. -/
def exPieceN (i : Fin 33) (d : ℕ) : ℕ := ((partsIn i).map fun k => partSumN k d).sum

theorem histN_buckets : ∀ k < 35, ∀ e ∈ histN k, e.1 ∈ Icc 1 (2 ^ 16) := by
  intro k hk e he
  have h : ∀ k : Fin 35, (hist k).all (fun e => decide (1 ≤ e.1 ∧ e.1 ≤ 2 ^ 16)) = true := by
    decide +kernel
  unfold histN at he
  simp only [hk, ↓reduceDIte] at he
  have := List.all_eq_true.mp (h ⟨k, hk⟩) e he
  simpa using this

theorem sum_regroup (s : Finset ℕ) (g : ℕ → ℝ) (w : ℕ × ℕ × ℕ → ℕ) :
    ∀ L : List (ℕ × ℕ × ℕ), (∀ e ∈ L, e.1 ∈ s) →
      ∑ k ∈ s, g k * (((L.map fun e => if e.1 = k then w e else 0).sum : ℕ) : ℝ) =
        (L.map fun e => g e.1 * (w e : ℝ)).sum
  | [], _ => by simp
  | e :: L, hL => by
      have ih := sum_regroup s g w L fun e' he' => hL e' (List.mem_cons_of_mem _ he')
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add, sum_add_distrib, ih]
      congr 1
      have he : e.1 ∈ s := hL e List.mem_cons_self
      simp only [Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq s e.1]
      simp [he]

theorem exactBound_nonneg (a : ℝ) (d : ℕ) (ps : List ℕ) : 0 ≤ Misc.exactBound binU a d ps := by
  unfold Misc.exactBound
  exact sum_nonneg fun k _ => mul_nonneg (Real.exp_pos _).le
    (div_nonneg (List.sum_nonneg fun x hx => by
      obtain ⟨B, -, rfl⟩ := List.mem_map.mp hx
      exact Nat.cast_nonneg _) (by positivity))

/-- **M2's exact bound of a part at `a_T` from the histogram.** -/
theorem exactBound_le_hist (hH : HistogramClaim) {k : ℕ} (hk : k < 35) {d : ℕ}
    (hd : d = 2 ∨ d = 3) :
    Misc.exactBound binU targetDecay d (partList k) ≤
      (partSumN k d : ℝ) / ((unitD : ℝ) * 2 ^ 95) := by
  unfold Misc.exactBound
  have hS : ∀ b ∈ Icc 1 (2 ^ 16),
      (((greedyBlocks binU integerBudget (partList k)).filter fun B => blockBin binU B = b).map
        fun B => (Misc.wd d (B.headD 0) : ℝ)).sum ≤ (histAt k d b : ℝ) := by
    intro b hb
    have h := hH k hk d hd b hb
    have hc : (((greedyBlocks binU integerBudget (partList k)).filter fun B =>
        blockBin binU B = b).map fun B => (Misc.wd d (B.headD 0) : ℝ)).sum =
        (((((greedyOf k).filter fun B => blockBin binU B = b).map fun B =>
          Misc.wd d (B.headD 0)).sum : ℕ) : ℝ) := by
      rw [Nat.cast_list_sum, List.map_map]
      rfl
    rw [hc]
    exact_mod_cast h
  calc ∑ b ∈ Icc (1 : ℕ) (2 ^ 16), Real.exp (2 * targetDecay * integerBudget * (b : ℝ) / 2 ^ 56) *
        ((((greedyBlocks binU integerBudget (partList k)).filter fun B => blockBin binU B = b).map
          fun B => (Misc.wd d (B.headD 0) : ℝ)).sum / 2 ^ 95)
      ≤ ∑ b ∈ Icc (1 : ℕ) (2 ^ 16), Real.exp (2 * targetDecay * integerBudget * (b : ℝ) / 2 ^ 56) *
          ((histAt k d b : ℝ) / 2 ^ 95) :=
        sum_le_sum fun b hb => mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (hS b hb) (by positivity)) (Real.exp_pos _).le
    _ = (∑ b ∈ Icc (1 : ℕ) (2 ^ 16), Real.exp (2 * targetDecay * integerBudget * (b : ℝ) / 2 ^ 56) *
          (histAt k d b : ℝ)) / 2 ^ 95 := by
        rw [Finset.sum_div]
        exact sum_congr rfl fun b _ => by ring
    _ = ((histN k).map fun e => Real.exp (2 * targetDecay * integerBudget * (e.1 : ℝ) / 2 ^ 56) *
          (wsel d e : ℝ)).sum / 2 ^ 95 := by
        unfold histAt
        rw [sum_regroup _ (fun b => Real.exp (2 * targetDecay * integerBudget * (b : ℝ) / 2 ^ 56))
          (wsel d) (histN k) (histN_buckets k hk)]
    _ ≤ ((histN k).map fun e => (powUp unitD 20 expDeltaE e.1 : ℝ) / unitD * (wsel d e : ℝ)).sum /
          2 ^ 95 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply List.sum_le_sum
        intro e he
        have hb := mem_Icc.mp (histN_buckets k hk e he)
        exact mul_le_mul_of_nonneg_right (exp_bucket_le hb.2) (Nat.cast_nonneg _)
    _ = (partSumN k d : ℝ) / ((unitD : ℝ) * 2 ^ 95) := by
        unfold partSumN
        rw [Nat.cast_list_sum, List.map_map]
        have he : ∀ e : ℕ × ℕ × ℕ, (powUp unitD 20 expDeltaE e.1 : ℝ) / unitD * (wsel d e : ℝ) =
            ((Nat.cast ∘ fun e : ℕ × ℕ × ℕ => powUp unitD 20 expDeltaE e.1 * wsel d e) e : ℝ) /
              unitD :=
          fun e => by
            simp only [Function.comp_apply, Nat.cast_mul]
            ring
        simp only [he]
        rw [list_sum_div_const, div_div]

/-! ## The 66 bounds -/

theorem pieceStop_le_XCh : ∀ i : Fin 33, i.val < 28 → pieceStop i ≤ XCh := by decide +kernel

theorem cellBound_low {i : Fin 33} (hi : i.val < 28) (a s e : ℝ) :
    Misc.cellBound (paperPiece i) a s e = 0 := by
  have h := pieceStop_le_XCh i hi
  have hn : (paperPiece i).n = 0 := by
    simp only [paperPiece, cellNum, show ¬ XCh < pieceStop i by omega, ↓reduceIte]
  simp [Misc.cellBound, hn]

theorem cellC_nonneg : ∀ d i, 0 ≤ cellC d i := by
  intro d i
  have h : ∀ i : Fin 33, 0 ≤ cellC2 i ∧ 0 ≤ cellC3 i := by decide +kernel
  unfold cellC
  split_ifs
  · exact (h i).1
  · exact (h i).2

/-- **The 66 rational checks** (`decide +kernel`, 10737 buckets): the exact part of every piece
from the histogram, plus the recorded cell bound, is at most `c_d(i)`. -/
theorem exact_cell_le_charge : ∀ i : Fin 33,
    (exPieceN i 2 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellC 2 i ≤ chargeC2 i ∧
      (exPieceN i 3 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellC 3 i ≤ chargeC3 i := by
  decide +kernel

theorem pieceBound_le_aux (hH : HistogramClaim) (hC : CellClaim) (i : Fin 33) {d : ℕ}
    (hd : d = 2 ∨ d = 3) :
    pieceBound targetDecay d i ≤ (exPieceN i d : ℝ) / ((unitD : ℝ) * 2 ^ 95) + (cellC d i : ℝ) := by
  unfold pieceBound
  apply add_le_add
  · have h1 : ((paperPiece i).parts.map (Misc.exactBound binU targetDecay d)).sum =
        ((partsOf i).map fun k => Misc.exactBound binU targetDecay d (partList k)).sum := by
      simp only [paperPiece, List.map_map]
      rfl
    have h2 : ((partsOf i).map fun k => Misc.exactBound binU targetDecay d (partList k)).sum ≤
        ((partsIn i).map fun k => Misc.exactBound binU targetDecay d (partList k)).sum := by
      apply List.Sublist.sum_le_sum ((List.filter_sublist).map _)
      intro x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact exactBound_nonneg _ _ _
    have h3 : ((partsIn i).map fun k => Misc.exactBound binU targetDecay d (partList k)).sum ≤
        ((partsIn i).map fun k => (partSumN k d : ℝ) / ((unitD : ℝ) * 2 ^ 95)).sum := by
      apply List.sum_le_sum
      intro k hk
      have hk35 : k < 35 := by
        unfold partsIn at hk
        exact List.mem_range.mp (List.mem_filter.mp hk).1
      exact exactBound_le_hist hH hk35 hd
    have h4 : ((partsIn i).map fun k => (partSumN k d : ℝ) / ((unitD : ℝ) * 2 ^ 95)).sum =
        (exPieceN i d : ℝ) / ((unitD : ℝ) * 2 ^ 95) := by
      unfold exPieceN
      rw [list_sum_div_const, Nat.cast_list_sum, List.map_map]
      rfl
    rw [h1]
    exact h2.trans (h3.trans h4.le)
  · rcases Nat.lt_or_ge i.val 28 with hi | hi
    · rw [cellBound_low hi]
      exact_mod_cast cellC_nonneg d i
    · exact hC i hi d hd

/-- **The 66 charge bounds** `pieceBound a_T d i ≤ c_d(i)` from the histogram certificate and the
cell bounds. -/
theorem pieceBound_le_charge (hH : HistogramClaim) (hC : CellClaim) (i : Fin 33) :
    pieceBound targetDecay 2 i ≤ chargeC2 i ∧ pieceBound targetDecay 3 i ≤ chargeC3 i := by
  have hD : ((unitD : ℚ) : ℝ) = (unitD : ℝ) := by push_cast; rfl
  obtain ⟨h2, h3⟩ := exact_cell_le_charge i
  have h2' : ((((exPieceN i 2 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellC 2 i : ℚ)) : ℝ) ≤
      ((chargeC2 i : ℚ) : ℝ) := by exact_mod_cast h2
  have h3' : ((((exPieceN i 3 : ℚ) / ((unitD : ℚ) * 2 ^ 95) + cellC 3 i : ℚ)) : ℝ) ≤
      ((chargeC3 i : ℚ) : ℝ) := by exact_mod_cast h3
  push_cast at h2' h3'
  exact ⟨(pieceBound_le_aux hH hC i (Or.inl rfl)).trans h2',
    (pieceBound_le_aux hH hC i (Or.inr rfl)).trans h3'⟩

open Sarkozy.JointClosing Sarkozy.FirstStagePaper in
/-- **The main statement at `ε = a_T/71` at the paper's partition, with `hB` and `hL₀` from the
histogram certificate and the cell bounds** (`thm:main` at `ε = a_T/71`, `cor:joint-closing`,
`def:construction`(b), `lem:record:block-charge`, `cert:record:middle-price`(b), (c)): the
hypotheses H1, H2, H4, H5, `thm:dl:K`, H2″, the lemma families `hU`, `hM`, `hI`, the
**histogram certificate** `HistogramClaim` (the sieve's bucket sums of the greedy blocks below
`X_Ch`), the **cell bounds** `CellClaim` (10 explicit analytic inequalities on the five pieces above
`X_Ch`), and the 9 fields `Dv` (`CL`, `ME`, `SM`), `hT`, `hSA`, `JB`, `SF`, `fix`, `env`. -/
theorem main_target_paper_joint_N1_hist (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : N1JointBlockData hWeil hMovingRoot hFourCycle hU hM hI)
    (hHist : HistogramClaim) (hCell : CellClaim)
    (hT : Dv.toJoint.data.ME.T ≤ targetLedger.T)
    (hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A)
    (JB : JointBound Dv.toJoint.data targetLedger.jointConstant)
    (SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data)
    (fix : EnvelopeInputsBlock.FixedIntervalInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data)
    (env : EnvelopeInputsBlock.EnvelopeEnergyInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_joint_N1_final hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR
    hU hM hI Dv (fun i => (pieceBound_le_charge hHist hCell i).1)
    (fun i => (pieceBound_le_charge hHist hCell i).2) hT hSA JB SF fix env

end Sarkozy.PaperNumbers
