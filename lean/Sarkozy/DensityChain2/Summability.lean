module

public import Sarkozy.DensityChain2.Atoms

@[expose] public section

/-!
# The `q^{1/4}`-weighted price summability `_hW` from (CP8)(c)

DC1's reductions of fields 28–31 ask `∑_𝔟 q_𝔟^{1/4}(2 u_𝔟 + u'_𝔟) ≤ W` uniformly in the scale
(`def:cp8`(c), used for Rankin's trick in `lem:record:density-lp`), with `u_𝔟` the increment price
(`envPriceL/R`, or `wrapPrice` for `fixC`) and `u'_𝔟` the record price. The data's
`Summability.summable` bounds the larger sum
`∑_𝔟 q_𝔟^{1/4}(p_𝔟 + v_𝔟 + d_𝔟 + u'_𝔟 + s_𝔟 + a_𝔟 + T_{L,𝔟} + T_{R,𝔟}) ≤ bound`, with
`q_𝔟 = oneWeight` (the primes of `𝔟` with `e_p = 1`). Every price is nonnegative, so:

* `atomQ_cast`: `(q_𝔟 : ℝ) = oneWeight` (`atomQ` of `Factorization` is the data's weight);
* **`hW_envL_of_summable`**, `hW_envR_of_summable`, **`hW_fix_of_summable`**: `_hW` with
  `W = 2 · bound`.
-/

namespace Sarkozy.DensityChain2

open Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeEnergiesPaper Sarkozy.BlockFrame
  Sarkozy.TheoremC Sarkozy.RecordExpansion

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq J₀] [Fintype Bk] [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
  [∀ L j, NeZero (p L j)] in
/-- `q_𝔟` is the data's weight `oneWeight` (`def:cp8`(c)). -/
theorem atomQ_cast (pp ep : J₀ → ℕ) (L : ℕ) (b : BlockAtom Bk J L) :
    ((atomQ blk p pp ep L b : ℕ) : ℝ) = TheoremCBlock.oneWeight blk p pp ep L b := by
  cases b with
  | inl β =>
    unfold atomQ TheoremCBlock.oneWeight
    rw [Nat.cast_prod]
  | inr j => rfl

omit [DecidableEq P] in
/-- The summand of `Summability.summable` is nonnegative termwise, and dominates `x + y` for
any two of its prices. -/
theorem summand_ge (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) :
    0 ≤ D.FS.pvar L b ∧ 0 ≤ ∑ i, D.FS.vprice L b i ∧ 0 ≤ ∑ i, D.FS.dprice L b i ∧
      0 ≤ D.GB.uprice L b ∧ 0 ≤ symTotal (D.CL.π L) b ∧ 0 ≤ skewTotal (D.CL.π L) b ∧
      0 ≤ ∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b ∧
      0 ≤ ∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b := by
  have hπ : ∀ t e, 0 ≤ D.CL.π L b t e := fun t e =>
    mul_nonneg (D.CL.πt_nonneg L b t e) (D.selectionFactor_nonneg L b)
  refine ⟨D.pvar_nonneg L b, sum_nonneg fun i _ => D.vprice_nonneg L b i,
    sum_nonneg fun i _ => D.dprice_nonneg L b i, TheoremCBlock.Structured.uprice_nonneg D L b,
    sum_nonneg fun t _ => hπ t _, sum_nonneg fun t _ => hπ t _,
    TheoremCBlock.Structured.envPriceL_nonneg D L b,
    TheoremCBlock.Structured.envPriceR_nonneg D L b⟩

omit [DecidableEq P] in
/-- **`_hW` for field 30** from (CP8)(c): `∑_𝔟 q_𝔟^{1/4}(2 u_{L,𝔟} + u'_𝔟) ≤ 2 · bound`. -/
theorem hW_envL_of_summable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) :
    ∑ b, ((atomQ blk p D.S.pp D.S.ep L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
      (2 * TheoremCBlock.Structured.envPriceL D L b + D.GB.uprice L b) ≤ 2 * D.SM.bound := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (D.SM.summable L) zero_le_two)
  rw [mul_sum]
  refine sum_le_sum fun b _ => ?_
  rw [atomQ_cast]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := summand_ge D L b
  have hw : 0 ≤ TheoremCBlock.oneWeight blk p D.S.pp D.S.ep L b ^ ((1 : ℝ) / 4) := by
    rw [← atomQ_cast]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold TheoremCBlock.Structured.envPriceL
  nlinarith [mul_le_mul_of_nonneg_left (show 2 * (∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) *
    TheoremCBlock.selectionFactor a p D.S.selPre L b) + D.GB.uprice L b ≤
    2 * (D.FS.pvar L b + ∑ i, D.FS.vprice L b i + ∑ i, D.FS.dprice L b i + D.GB.uprice L b +
      symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b +
      ∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b +
      ∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b) by linarith) hw]

omit [DecidableEq P] in
/-- **`_hW` for field 31** from (CP8)(c): `∑_𝔟 q_𝔟^{1/4}(2 u_{R,𝔟} + u'_𝔟) ≤ 2 · bound`. -/
theorem hW_envR_of_summable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) :
    ∑ b, ((atomQ blk p D.S.pp D.S.ep L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
      (2 * TheoremCBlock.Structured.envPriceR D L b + D.GB.uprice L b) ≤ 2 * D.SM.bound := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (D.SM.summable L) zero_le_two)
  rw [mul_sum]
  refine sum_le_sum fun b _ => ?_
  rw [atomQ_cast]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := summand_ge D L b
  have hw : 0 ≤ TheoremCBlock.oneWeight blk p D.S.pp D.S.ep L b ^ ((1 : ℝ) / 4) := by
    rw [← atomQ_cast]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  unfold TheoremCBlock.Structured.envPriceR
  nlinarith [mul_le_mul_of_nonneg_left (show 2 * (∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) *
    TheoremCBlock.selectionFactor a p D.S.selPre L b) + D.GB.uprice L b ≤
    2 * (D.FS.pvar L b + ∑ i, D.FS.vprice L b i + ∑ i, D.FS.dprice L b i + D.GB.uprice L b +
      symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b +
      ∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b +
      ∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b) by linarith) hw]

omit [DecidableEq P] in
/-- The wrapping price is the sum of the symmetric and skew totals. -/
theorem wrapPrice_eq (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) :
    TheoremCBlock.Structured.wrapPrice D L b = symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b := by
  unfold TheoremCBlock.Structured.wrapPrice symTotal skewTotal
  rw [sum_add_distrib]

omit [DecidableEq P] in
/-- **`_hW` for fields 28–29** from (CP8)(c): `∑_𝔟 q_𝔟^{1/4}(2 wrapPrice_𝔟 + u'_𝔟) ≤ 2 · bound`. -/
theorem hW_fix_of_summable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) :
    ∑ b, ((atomQ blk p D.S.pp D.S.ep L b : ℕ) : ℝ) ^ ((1 : ℝ) / 4) *
      (2 * TheoremCBlock.Structured.wrapPrice D L b + D.GB.uprice L b) ≤ 2 * D.SM.bound := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (D.SM.summable L) zero_le_two)
  rw [mul_sum]
  refine sum_le_sum fun b _ => ?_
  rw [atomQ_cast, wrapPrice_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := summand_ge D L b
  have hw : 0 ≤ TheoremCBlock.oneWeight blk p D.S.pp D.S.ep L b ^ ((1 : ℝ) / 4) := by
    rw [← atomQ_cast]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  nlinarith [mul_le_mul_of_nonneg_left (show 2 * (symTotal (D.CL.π L) b +
    skewTotal (D.CL.π L) b) + D.GB.uprice L b ≤
    2 * (D.FS.pvar L b + ∑ i, D.FS.vprice L b i + ∑ i, D.FS.dprice L b i + D.GB.uprice L b +
      symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b +
      ∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b +
      ∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) * TheoremCBlock.selectionFactor a p
        D.S.selPre L b) by linarith) hw]

end Sarkozy.DensityChain2
