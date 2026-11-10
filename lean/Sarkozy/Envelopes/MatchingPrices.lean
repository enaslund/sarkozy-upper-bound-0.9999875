module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The price of the dominators (`prop:record:matching`(ii), (iii), partly)

`paper/sections/24_matching_mean.tex`, `prop:record:matching`(ii): the price of `M_{s,𝔅} - Ñ_𝔅`
summed over the atoms is at most the matching exponent `T`, and (iii): the random-inclusion
energies are at most `(2⁶ J + o(1)) Y` with `J = B e^T (R_I/2)⁶`.

**Form (abstract).** The prices per block are real numbers; the record-level facts of the proof
are hypotheses: the chosen side diagonal of a block of the piece `i` costs at most
`t (k_{L,i} + k_{R,i}) r_𝔅² q_𝔅^{2a₀}` (mass times `q^{2a} ≤ t q^{2a₀}`, `lem:record:repricing`),
the chosen matching diagonal at most `t · 2 q_i r_𝔅² q_𝔅^{2a₀}`, and the other norm envelopes have
totals `S_oth + A_oth` (middle) and `S_u + A_u` plus the prefix allowance (outside the middle).

**Proved.**
* `side_diagonal_price`: the chosen side diagonals cost at most `t T'_K = T_K`, given the degree-two
  charges `Ī_{2,i} ≥ ∑_𝔅 r_𝔅² q_𝔅^{2a₀}` and `∑_i (k_{L,i} + k_{R,i}) Ī_{2,i} ≤ T'_K`
  (`prop:signed-sides`(iii));
* `matching_diagonal_price`: the chosen matching diagonals cost at most `T_QE = t ∑_i (A_{E,i} +
  S_{E,i})` under the gate `2 q_i Ī_{2,i} ≤ A_{E,i} + S_{E,i}`;
* `dominator_price_le`: the total is at most `T`;
* `inclusion_energy_constant`: `B e^T R_I⁶ = 2⁶ J` for `J = B e^T (R_I/2)⁶`.
-/

namespace Sarkozy.Envelopes

open Finset

/-- **`prop:record:matching`(ii), the chosen side diagonals.** Over the pieces `i` with blocks
`blocks i`, if each block's side diagonal costs at most `t (k_L + k_R)_i c_𝔅` (with
`c_𝔅 = r_𝔅² q_𝔅^{2a₀} ≥ 0`), the charges satisfy `∑_{𝔅 ∈ i} c_𝔅 ≤ Ī_{2,i}`, `t ≥ 0`,
`(k_L + k_R)_i ≥ 0`, and `∑_i (k_L + k_R)_i Ī_{2,i} ≤ T'_K`, then the total price is at most
`t T'_K = T_K`. -/
theorem side_diagonal_price {ι β : Type*} (pieces : Finset ι) (blocks : ι → Finset β)
    (price c : β → ℝ) (k I : ι → ℝ) {t TK' : ℝ} (ht : 0 ≤ t) (hk : ∀ i ∈ pieces, 0 ≤ k i)
    (hprice : ∀ i ∈ pieces, ∀ B ∈ blocks i, price B ≤ t * k i * c B)
    (hI : ∀ i ∈ pieces, ∑ B ∈ blocks i, c B ≤ I i)
    (hT : ∑ i ∈ pieces, k i * I i ≤ TK') :
    ∑ i ∈ pieces, ∑ B ∈ blocks i, price B ≤ t * TK' := by
  have h1 : ∀ i ∈ pieces, ∑ B ∈ blocks i, price B ≤ t * (k i * I i) := by
    intro i hi
    calc ∑ B ∈ blocks i, price B ≤ ∑ B ∈ blocks i, t * k i * c B :=
          sum_le_sum fun B hB => hprice i hi B hB
      _ = t * k i * ∑ B ∈ blocks i, c B := by rw [mul_sum]
      _ ≤ t * k i * I i := mul_le_mul_of_nonneg_left (hI i hi) (mul_nonneg ht (hk i hi))
      _ = t * (k i * I i) := by ring
  calc ∑ i ∈ pieces, ∑ B ∈ blocks i, price B ≤ ∑ i ∈ pieces, t * (k i * I i) := sum_le_sum h1
    _ = t * ∑ i ∈ pieces, k i * I i := by rw [mul_sum]
    _ ≤ t * TK' := mul_le_mul_of_nonneg_left hT ht

/-- **`prop:record:matching`(ii), the chosen matching diagonals.** If each block's matching
diagonal costs at most `t · 2q_i c_𝔅`, `∑_{𝔅 ∈ i} c_𝔅 ≤ Ī_{2,i}`, `q_i ≥ 0`, and the gate
`2 q_i Ī_{2,i} ≤ A_{E,i} + S_{E,i}` holds in every piece, then the total is at most
`t ∑_i (A_{E,i} + S_{E,i}) = T_QE`. -/
theorem matching_diagonal_price {ι β : Type*} (pieces : Finset ι) (blocks : ι → Finset β)
    (price c : β → ℝ) (q I AE SE : ι → ℝ) {t : ℝ} (ht : 0 ≤ t) (hq : ∀ i ∈ pieces, 0 ≤ q i)
    (hprice : ∀ i ∈ pieces, ∀ B ∈ blocks i, price B ≤ t * (2 * q i) * c B)
    (hI : ∀ i ∈ pieces, ∑ B ∈ blocks i, c B ≤ I i)
    (hgate : ∀ i ∈ pieces, 2 * q i * I i ≤ AE i + SE i) :
    ∑ i ∈ pieces, ∑ B ∈ blocks i, price B ≤ t * ∑ i ∈ pieces, (AE i + SE i) := by
  have h := side_diagonal_price pieces blocks price c (fun i => 2 * q i) I ht
    (fun i hi => by have := hq i hi; positivity) hprice hI
    (sum_le_sum fun i hi => hgate i hi)
  exact h

/-- **`prop:record:matching`(ii), the total.** The price of `M_{s,𝔅} - Ñ_𝔅` summed over the atoms
is at most `T = T_QE + (S_oth + A_oth) + T_K + (S_u + A_u) + 10⁻¹²` when the four parts are bounded
by their totals. -/
theorem dominator_price_le {pK pQ pOth pU TK TQE Soth Su allow : ℝ} (hK : pK ≤ TK)
    (hQ : pQ ≤ TQE) (hOth : pOth ≤ Soth) (hU : pU ≤ Su + allow) :
    pK + pQ + pOth + pU ≤ TQE + Soth + TK + Su + allow := by
  linarith

/-- **`prop:record:matching`(iii), the constant.** `B e^T R_I⁶ = 2⁶ J` for
`J = B e^T (R_I/2)⁶`. -/
theorem inclusion_energy_constant (B T RI : ℝ) :
    B * Real.exp T * RI ^ 6 = 2 ^ 6 * (B * Real.exp T * (RI / 2) ^ 6) := by
  ring

end Sarkozy.Envelopes
