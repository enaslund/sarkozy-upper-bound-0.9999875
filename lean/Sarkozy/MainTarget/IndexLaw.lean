module

public import Sarkozy.EnvelopeInputsBlock.PaperMoment

@[expose] public section

/-!
# The paper's index law at a free price exponent (`def:cp0`(d), `prop:imp:padic-price`)

`Sarkozy.PaperData.IndexLaw` fixes the conductor moment of the paper's index law at the anchor:
`R_I = paperRI = M_pad(K)` at `a₀`. At another price exponent `a` the moment of
`def:hyb:coupled`(g) is `M_pad(K)` at `a` (V2-A's `PartVLaws.Mpad a 64 Q₃ K`,
`prop:imp:padic-price`); the increments and the depth tails do not depend on `a`.

* `paperRIAt a`: `M_pad(K)` at `a`; `paperRIAt_anchor` checks that it is D1's `paperRI` at `a₀`.
* `paperRIAt_eq_prod`: for `a < 18`, the closed form `K^{a/36} ∏_q momentFactor` over the paper's
  index primes (`lem:hyb:moment`), from `PartVLaws.Mpad_eq_oneQueryMoment`; this is G1's
  computation in `EnvelopeInputsBlock.paper_indexMomentBound_block`, with `a` free.
* `paperIndexEnvelopeAt a`: the paper's depth envelope with the moment `paperRIAt a`, given
  `lem:imp:padic-envelope` (`PaperData.PaperIndexBound`, proved by CERT1 as
  `IndexCert.paperIndexBound`).
-/

open Finset

namespace Sarkozy.MainTarget

open Sarkozy.Functional Sarkozy.PartVLaws Sarkozy.CancellationSteps
open Sarkozy.Param (Params)
open Sarkozy.EnvelopeInputsParam (paperMomentFactor)

/-- **The paper's conductor moment at the price exponent `a`**: `R_I = M_pad(K)`
(`prop:imp:padic-price`, V2-A's `PartVLaws.Mpad`, with `m = 64`, `Q = Q₃`, `K = blockScale`). Its
numeric bound is `cert:index-moment` at `a`. -/
noncomputable def paperRIAt (a : ℝ) : ℝ := PartVLaws.Mpad a 64 PartV.Q3 blockScale

/-- At `a₀` this is D1's `PaperData.paperRI`. -/
theorem paperRIAt_anchor : paperRIAt Params.anchorDecay = Sarkozy.PaperData.paperRI := rfl

theorem paperRIAt_nonneg {a : ℝ} (ha : a < 18) : 0 ≤ paperRIAt a := by
  unfold paperRIAt
  rw [PartVLaws.Mpad_eq_oneQueryMoment ha (by norm_num) _ (by unfold blockScale; norm_num)]
  unfold Functional.oneQueryMoment
  exact FiniteLaw.expect_nonneg _ fun J => Real.rpow_nonneg (by unfold blockScale; positivity) _

/-- **`M_pad(K)` at `a` as the one-query moment in closed form** (`lem:hyb:moment`,
`prop:imp:padic-price`): `K^{a/36} ∏_{q ∈ {2} ∪ 𝒫_{Q₃}} momentFactor`. G1's computation in
`paper_indexMomentBound_block`, at a free `a < 18`. -/
theorem paperRIAt_eq_prod {a : ℝ} (ha : a < 18) :
    paperRIAt a = (blockScale : ℝ) ^ (a / 36) *
      ∏ q ∈ paperSmallPrimes, paperMomentFactor (a / 36) q := by
  have hK : (0 : ℝ) ≤ (blockScale : ℝ) := Nat.cast_nonneg _
  unfold paperRIAt
  rw [Mpad_eq_oneQueryMoment ha (by norm_num) _ hK]
  unfold oneQueryMoment
  rw [conductorMoment_eq indexPrime indexPrime_prime indexPrime_injective _ _ _ hK,
    Fintype.prod_option]
  have h2 : (2 : ℕ) ∉ PartV.smallModulusOddPrimes := by
    rw [PartV.mem_smallModulusOddPrimes]
    omega
  have htwo : momentFactor (indexPrime (none : IndexCoord PartV.Q3))
      (indexDepth 64 (none : IndexCoord PartV.Q3)) (indexTail 64 (none : IndexCoord PartV.Q3))
      (a / 36) = paperMomentFactor (a / 36) 2 := by
    show momentFactor 2 (2 * 64 + 2) (twoTail 64) _ = _
    unfold paperMomentFactor PartV.mExt
    rfl
  have hodd : ∏ p : indexPrimes PartV.Q3, momentFactor (indexPrime (some p : IndexCoord PartV.Q3))
      (indexDepth 64 (some p : IndexCoord PartV.Q3)) (indexTail 64 (some p : IndexCoord PartV.Q3))
      (a / 36) =
      ∏ q ∈ PartV.smallModulusOddPrimes, paperMomentFactor (a / 36) q := by
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

/-- **The paper's depth envelope at the price exponent `a`**: the depth tails of
`lem:imp:padic-envelope` (given its transition bound `hb`) and the moment `M_pad(K)` at `a`. -/
noncomputable def paperIndexEnvelopeAt (a : ℝ) (ha : a < 18)
    (hb : Sarkozy.PaperData.PaperIndexBound) : Sarkozy.PaperData.PaperIndexEnvelope where
  t _ q := Sarkozy.PaperData.paperTails q
  hnorm _ q l f h := hb q l f h
  R_I := paperRIAt a
  hR_I := paperRIAt_nonneg ha

end Sarkozy.MainTarget
