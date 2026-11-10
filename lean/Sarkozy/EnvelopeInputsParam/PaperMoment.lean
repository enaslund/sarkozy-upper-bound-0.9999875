module

public import Sarkozy.EnvelopeInputsParam.ConductorPrice
public import Sarkozy.MainAnchor.Paper

@[expose] public section

/-!
# `IndexMomentBound` for the paper's index law at `a₀`

I1's reductions of the two envelope energies (`envelopeEnergies_of_inputs`,
`fixedIntervalEnvelopeEnergies_of_inputs`) take `IndexMomentBound D`: the conductor moment
`E_J (K sq(D_J))^{2a/d}` of every query, in the closed form `K^w ∏_q momentFactor(…)` of
`lem:hyb:moment` (`expect_queryPrice`), is at most `R_I`. For the paper's data at `a₀`
(`MainAnchor.PaperData.toData`) this holds with equality, with no hypothesis:
* the index law's moment is `R_I = PaperData.paperRI = M_pad(K)` at `a₀` (`prop:imp:padic-price`,
  V2-A's `PartVLaws.Mpad`), which `PartVLaws.Mpad_eq_oneQueryMoment` and
  `Functional.conductorMoment_eq` write as `K^{a₀/36} ∏_i momentFactor` over V2-A's index
  coordinates `Option (indexPrimes Q₃)`: the prime `2` with depth bound `2m + 2` and the 2-adic
  tails, the primes `p ≡ 3 (mod 4)` below `Q₃` with depth bound `2m` and the odd tails, `m = 64`;
* the paper's index primes `paperSmallPrimes` are `2` and the same odd primes
  (`PartV.smallModulusOddPrimes` is `indexPrimes Q₃` by definition), with the same tails
  (`PaperData.paperDepthTail`) and the depth bounds `paperH`: `2m + 1 = 129` at `2`, `2m` at the
  odd primes;
* `momentFactor` depends on the depth bound `h` only through `⌊(h + 1)/2⌋`, which is `65` for
  both `129` and `130`;
* the price exponent is `2a₀/72 = a₀/36`.
-/

open Finset

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.Functional Sarkozy.PartVLaws Sarkozy.CancellationSteps
open Sarkozy.Param (Params)

/-- The paper's moment factor at an index prime, as a function of the prime. -/
noncomputable def paperMomentFactor (w : ℝ) (q : ℕ) : ℝ :=
  momentFactor q (if q = 2 then 2 * PartV.mExt + 1 else 2 * PartV.mExt)
    (if q = 2 then twoTail 64 else oddTail q 64) w

/-- **`IndexMomentBound` for the paper's index law at `a₀`** (`lem:hyb:moment`,
`prop:imp:padic-price`, `cert:index-moment` for the value of `R_I`): the conductor moment of every
query is exactly `R_I = M_pad(K)`. This discharges the hypothesis `hRI` of I1's reductions of the
envelope energies for the paper's data, with no assumption. -/
theorem paper_indexMomentBound {hW : Target.Weil} (Dp : MainAnchor.PaperData hW) :
    IndexMomentBound Dp.toData := by
  intro e
  have hw : priceExponent Params.anchorDecay = Params.anchorDecay / 36 := by
    unfold priceExponent
    ring
  have hK : (0 : ℝ) ≤ (blockScale : ℝ) := Nat.cast_nonneg _
  -- the left side, as a product over the paper's index primes
  have hL : ∏ q, momentFactor (paperPr q) (paperH q) (Dp.toData.S.index.t e q).tail
      (priceExponent Params.anchorDecay) =
      ∏ q ∈ paperSmallPrimes, paperMomentFactor (Params.anchorDecay / 36) q := by
    rw [hw, ← Finset.prod_coe_sort paperSmallPrimes]
    refine Fintype.prod_congr _ _ fun q => ?_
    show momentFactor q.1 (paperH q) (Sarkozy.PaperData.paperDepthTail q) _ = _
    unfold paperMomentFactor paperH Sarkozy.PaperData.paperDepthTail paperPr
    rfl
  -- the right side, `M_pad(K)` as the one-query moment
  have hR : Sarkozy.PaperData.paperRI = (blockScale : ℝ) ^ (Params.anchorDecay / 36) *
      ∏ q ∈ paperSmallPrimes, paperMomentFactor (Params.anchorDecay / 36) q := by
    unfold Sarkozy.PaperData.paperRI
    rw [Mpad_eq_oneQueryMoment (by unfold Params.anchorDecay; norm_num) (by norm_num) _ hK]
    unfold oneQueryMoment
    rw [conductorMoment_eq indexPrime indexPrime_prime indexPrime_injective _ _ _ hK,
      Fintype.prod_option]
    have h2 : (2 : ℕ) ∉ PartV.smallModulusOddPrimes := by
      rw [PartV.mem_smallModulusOddPrimes]
      omega
    have htwo : momentFactor (indexPrime (none : IndexCoord PartV.Q3))
        (indexDepth 64 (none : IndexCoord PartV.Q3)) (indexTail 64 (none : IndexCoord PartV.Q3))
        (Params.anchorDecay / 36) = paperMomentFactor (Params.anchorDecay / 36) 2 := by
      show momentFactor 2 (2 * 64 + 2) (twoTail 64) _ = _
      unfold paperMomentFactor PartV.mExt
      rfl
    have hodd : ∏ p : indexPrimes PartV.Q3, momentFactor (indexPrime (some p : IndexCoord PartV.Q3))
        (indexDepth 64 (some p : IndexCoord PartV.Q3)) (indexTail 64 (some p : IndexCoord PartV.Q3))
        (Params.anchorDecay / 36) =
        ∏ q ∈ PartV.smallModulusOddPrimes, paperMomentFactor (Params.anchorDecay / 36) q := by
      have hset : indexPrimes PartV.Q3 = PartV.smallModulusOddPrimes := by
        unfold indexPrimes PartV.smallModulusOddPrimes
        rfl
      rw [← hset, ← Finset.prod_coe_sort (indexPrimes PartV.Q3)]
      refine Fintype.prod_congr _ _ fun p => ?_
      have hp2 : p.1 ≠ 2 := by
        have := three_le_of_mem_indexPrimes p.2
        omega
      show momentFactor p.1 (2 * 64) (oddTail p.1 64) _ = _
      unfold paperMomentFactor PartV.mExt
      simp only [hp2, ↓reduceIte]
    rw [htwo, hodd]
    unfold paperSmallPrimes
    rw [Finset.prod_insert h2]
  show (blockScale : ℝ) ^ priceExponent Params.anchorDecay *
      ∏ q, momentFactor (paperPr q) (paperH q) (Dp.toData.S.index.t e q).tail
        (priceExponent Params.anchorDecay) ≤ Sarkozy.PaperData.paperRI
  rw [hL, hR, hw]

end Sarkozy.EnvelopeInputsParam
