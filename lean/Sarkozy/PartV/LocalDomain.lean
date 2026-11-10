module

public import Sarkozy.PartV.MiddleReference

@[expose] public section

/-!
# The domain of the middle local laws (`lem:record:local-domain`(i),(ii))

`paper/sections/20_middle_reference.tex`, `lem:record:local-domain`. For a middle block `𝔅` of the
piece `[X, Y)`:
* (i) every prime is `≡ 3 (mod 4)` and `X ≤ b_𝔅 ≤ p < Y` (`MiddleBlock.local_domain_i`);
* (ii) `|𝔅| log X ≤ log q_𝔅 ≤ L`, `|𝔅| ≤ ⌊L / log X⌋ ≤ n_X = ⌊L_loc / log X⌋`,
  `∑_{p ∈ 𝔅} 1/p ≤ L/(X log X)` (`MiddleBlock.local_domain_ii`) and `q_𝔅^{2a} ≤ e^{2aL}`
  (`MiddleBlock.selection_le`).

Part (iii), that the recorded bounds evaluated at `(X, L_loc)` hold for the block, concerns the
caps and constants, and is not formalized.
-/

namespace Sarkozy.PartV

open Finset

theorem pieceStart_ge_Q3 (i : Fin 33) : Q3 ≤ pieceStart i := by
  revert i
  unfold pieceStart pieceEnds Q3
  decide +kernel

/-- **`lem:record:local-domain`(i)**: every prime of a middle block is `≡ 3 (mod 4)` and lies in
`[X, Y)`, with `X ≤ b_𝔅 ≤ p`. -/
theorem MiddleBlock.local_domain_i (B : MiddleBlock) {p : ℕ} (hp : p ∈ B.primes) :
    p % 4 = 3 ∧ pieceStart B.piece ≤ B.least ∧ B.least ≤ p ∧ p < pieceStop B.piece :=
  ⟨B.class3 p hp, (B.inPiece _ (min'_mem _ _)).1, min'_le _ _ hp, (B.inPiece p hp).2⟩

/-- The logarithm of the piece start is positive. -/
theorem log_pieceStart_pos (i : Fin 33) : 0 < Real.log (pieceStart i) := by
  apply Real.log_pos
  have h := pieceStart_ge_Q3 i
  have : (1 : ℝ) < Q3 := by norm_num [Q3]
  exact lt_of_lt_of_le this (by exact_mod_cast h)

/-- **`lem:record:local-domain`(ii)**: `|𝔅| log X ≤ log q_𝔅 ≤ L`, hence `|𝔅| ≤ ⌊L / log X⌋ ≤
`⌊L_loc / log X⌋ = n_X`, and `∑_{p ∈ 𝔅} 1/p ≤ L/(X log X)`. -/
theorem MiddleBlock.local_domain_ii (B : MiddleBlock) :
    (B.primes.card : ℝ) * Real.log (pieceStart B.piece) ≤ middleBudget ∧
      B.primes.card ≤ ⌊(middleBudget : ℝ) / Real.log (pieceStart B.piece)⌋₊ ∧
      ⌊(middleBudget : ℝ) / Real.log (pieceStart B.piece)⌋₊ ≤
        ⌊(localCap : ℝ) / Real.log (pieceStart B.piece)⌋₊ ∧
      ∑ p ∈ B.primes, (1 : ℝ) / p ≤
        middleBudget / (pieceStart B.piece * Real.log (pieceStart B.piece)) := by
  set X : ℝ := (pieceStart B.piece : ℝ) with hX
  have hlog := log_pieceStart_pos B.piece
  have hXpos : (0 : ℝ) < X := by
    have h := pieceStart_ge_Q3 B.piece
    have : (0 : ℝ) < Q3 := by norm_num [Q3]
    rw [hX]
    exact lt_of_lt_of_le this (by exact_mod_cast h)
  have hpX : ∀ p ∈ B.primes, X ≤ (p : ℝ) := fun p hp => by
    rw [hX]
    exact_mod_cast (B.inPiece p hp).1
  have h1 : (B.primes.card : ℝ) * Real.log X ≤ middleBudget := by
    calc (B.primes.card : ℝ) * Real.log X = ∑ _p ∈ B.primes, Real.log X := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ B.primes, Real.log p :=
          sum_le_sum fun p hp => Real.log_le_log hXpos (hpX p hp)
      _ ≤ middleBudget := B.budget
  have h2 : B.primes.card ≤ ⌊(middleBudget : ℝ) / Real.log X⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ hlog]
    exact h1
  have h3 : ⌊(middleBudget : ℝ) / Real.log X⌋₊ ≤ ⌊(localCap : ℝ) / Real.log X⌋₊ := by
    apply Nat.floor_le_floor
    apply div_le_div_of_nonneg_right _ hlog.le
    norm_num [middleBudget, localCap]
  have h4 : ∑ p ∈ B.primes, (1 : ℝ) / p ≤ middleBudget / (X * Real.log X) := by
    calc ∑ p ∈ B.primes, (1 : ℝ) / p ≤ ∑ _p ∈ B.primes, 1 / X :=
          sum_le_sum fun p hp => one_div_le_one_div_of_le hXpos (hpX p hp)
      _ = (B.primes.card : ℝ) / X := by rw [sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ middleBudget / (X * Real.log X) := by
          rw [div_le_div_iff₀ hXpos (mul_pos hXpos hlog)]
          nlinarith [h1]
  exact ⟨h1, h2, h3, h4⟩

/-- **`lem:record:local-domain`(ii), the selection factor**: `q_𝔅^{2a} ≤ e^{2aL}` for `a ≥ 0`. -/
theorem MiddleBlock.selection_le (B : MiddleBlock) {a : ℝ} (ha : 0 ≤ a) :
    ((∏ p ∈ B.primes, (p : ℝ)) ^ (2 * a)) ≤ Real.exp (2 * a * middleBudget) := by
  have hpos : ∀ p ∈ B.primes, (0 : ℝ) < p := fun p hp => by exact_mod_cast (B.prime p hp).pos
  have hq : 0 < ∏ p ∈ B.primes, (p : ℝ) := prod_pos hpos
  rw [Real.rpow_def_of_pos hq, Real.log_prod (fun p hp => (hpos p hp).ne')]
  apply Real.exp_le_exp.mpr
  calc (∑ p ∈ B.primes, Real.log (p : ℝ)) * (2 * a) ≤ (middleBudget : ℝ) * (2 * a) :=
        mul_le_mul_of_nonneg_right B.budget (by linarith)
    _ = 2 * a * middleBudget := by ring

end Sarkozy.PartV
