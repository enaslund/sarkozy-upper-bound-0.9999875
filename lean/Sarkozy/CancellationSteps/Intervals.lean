module

public import Sarkozy.Cancellation.PaperEncoding

/-!
# The intervals `I_b`, `I_{b+1}` of a density-cancellation query

`paper/sections/06_lifts_sectors.tex`, `def:record:functional`(f): `I_b = ((b − 1)L, bL] ∩ ℤ`
for `b ∈ ℤ/Kℤ` identified with `{1, …, K}` (`Functional.blockInterval`, `leastPosRep`). In
`lem:record:density-can` the query pair is `G_u = g^{I_b, M₀, s}`, `G_v = g^{I_{b+1}, M₀, s+r}`
with `1 ≤ b ≤ K − 1` (`b ≠ 0`). Then, with `c = b.val`:

* `blockInterval_eq_Icc`: `I_b = [(c − 1)L + 1, cL]` and `I_{b+1} = [cL + 1, (c + 1)L]`;
* `queryIntervals_ok`: `v₁ < u₂ ≤ v₂` and `v₂ − u₂ + 1 = L` for these endpoints (`L ≥ 1`), the
  interval conditions of `PairLawForm`; `card_queryInterval`: `|I_b| = L`.

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset Sarkozy.Functional

/-- For `b ≠ 0` in `ℤ/Kℤ` the least positive representative is `b.val`. -/
theorem leastPosRep_of_ne_zero {K : ℕ} [NeZero K] {b : ZMod K} (hb : b ≠ 0) :
    leastPosRep b = b.val := by
  unfold leastPosRep
  have : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
  simp only [this, ↓reduceIte]

/-- For `b ∈ ℤ/Kℤ` (`K ≥ 2`) the least positive representative of `b + 1` is `b.val + 1` (for
`b = K − 1` it is `K`, the interval `I_K`). -/
theorem leastPosRep_add_one {K : ℕ} [NeZero K] (hK : 2 ≤ K) (b : ZMod K) :
    leastPosRep (b + 1) = b.val + 1 := by
  have hlt := ZMod.val_lt b
  unfold leastPosRep
  have hK1 : Fact (1 < K) := ⟨by omega⟩
  by_cases h : b.val + 1 < K
  · have hv : (b + 1).val = b.val + 1 := by
      rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; exact h), ZMod.val_one]
    simp only [hv, Nat.add_one_ne_zero, ↓reduceIte]
  · have hbv : b.val + 1 = K := by omega
    have h0 : b + 1 = 0 := by
      rw [← ZMod.natCast_zmod_val b, ← Nat.cast_one (R := ZMod K), ← Nat.cast_add, hbv,
        ZMod.natCast_self]
    simp only [h0, ZMod.val_zero, ↓reduceIte, hbv]

theorem Ioc_eq_Icc_int (a b : ℤ) : Ioc a b = Icc (a + 1) b := by
  ext x
  simp only [mem_Ioc, mem_Icc]
  omega

/-- **The query intervals** (`def:record:functional`(f)): for `b ≠ 0` in `ℤ/Kℤ`, `K ≥ 2`, and
`c = b.val`, `I_b = [(c − 1)L + 1, cL]` and `I_{b+1} = [cL + 1, (c + 1)L]`. -/
theorem blockInterval_eq_Icc {K : ℕ} [NeZero K] (hK : 2 ≤ K) (L : ℕ) {b : ZMod K} (hb : b ≠ 0) :
    blockInterval K L b = Icc (((b.val : ℤ) - 1) * L + 1) ((b.val : ℤ) * L) ∧
      blockInterval K L (b + 1) = Icc ((b.val : ℤ) * L + 1) (((b.val : ℤ) + 1) * L) := by
  unfold blockInterval
  rw [leastPosRep_of_ne_zero hb, leastPosRep_add_one hK b, Ioc_eq_Icc_int, Ioc_eq_Icc_int]
  push_cast
  constructor
  · rfl
  · congr 1
    ring

/-- The interval conditions of `PairLawForm` for the query intervals: `v₁ < u₂ ≤ v₂` and
`v₂ − u₂ + 1 = L` (`L ≥ 1`). -/
theorem queryIntervals_ok (c L : ℕ) (hL : 1 ≤ L) :
    (c : ℤ) * L < (c : ℤ) * L + 1 ∧ (c : ℤ) * L + 1 ≤ ((c : ℤ) + 1) * L ∧
      ((((c : ℤ) + 1) * L - ((c : ℤ) * L + 1) + 1 : ℤ) : ℝ) ≤ (L : ℝ) := by
  refine ⟨by omega, by nlinarith, ?_⟩
  have : (((c : ℤ) + 1) * L - ((c : ℤ) * L + 1) + 1 : ℤ) = (L : ℤ) := by ring
  rw [this]
  push_cast
  exact le_rfl

/-- `|I| = L` for `I = [aL + 1, (a + 1)L]`. -/
theorem card_queryInterval (a : ℤ) (L : ℕ) :
    ((Icc (a * L + 1) ((a + 1) * L)).card : ℝ) = L := by
  rw [Int.card_Icc]
  have : (a + 1) * L + 1 - (a * L + 1) = (L : ℤ) := by ring
  rw [this, Int.toNat_natCast]

end Sarkozy.CancellationSteps
