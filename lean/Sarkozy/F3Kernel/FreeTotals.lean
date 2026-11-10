module

public import Sarkozy.F3Kernel.LaneTotals
public import Sarkozy.F3Kernel.RunMaskBounds

/-!
# The checker counts exactly the free edges

The SWAR row degrees sum to the mathematical free-edge cardinality. This applies both
to accepted leaf records and to the root cylinders whose masses are accumulated.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

def horizontalSum (x : ℕ) : ℕ := Nat.land (Nat.shiftRight (x * LANE0) 2240) FULL64

set_option exponentiation.threshold 4096 in
theorem horizontalSum_eq_lane64 (x : ℕ) : horizontalSum x = lane64 (x * LANE0) 35 := by
  change ((x * LANE0) >>> 2240) &&& (2 ^ 64 - 1) = (x * LANE0) / 2 ^ (64 * 35) % 2 ^ 64
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem sum_cmpHx_lt_lane (Fr : Finset (Fin 36 × Fin 36)) : ∑ i, cmpHx Fr i < 2 ^ 64 := by
  have hb : ∑ i, cmpHx Fr i ≤ ∑ _ : Fin 36, 36 :=
    sum_le_sum (fun i _ => cmpHx_le_36 Fr i)
  norm_num at hb ⊢
  omega

theorem horizontalSum_freeRows {G : Consts} {c : Cyl} (hf : FreeDegreeCounts G c) :
    horizontalSum (freeRows G c) = #(freePairs G c) := by
  rw [hf.1, horizontalSum_eq_lane64, lane64_mul_LANE0 _ (sum_cmpHx_lt_lane _)]
  simpa using sum_cmpHx (freePairs G c) univ

theorem LeafTrace.free_eq_card {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) (hf : FreeDegreeCounts G c) :
    free = #(freePairs G c) := t.freeCount.trans (horizontalSum_freeRows hf)

theorem classRoot_freeDegreeCounts {G : Consts} (hM : MatrixWord G.EM)
    (hT : G.WellFormedT) (hG : G.Coherent) {key : ℕ} {c : Cyl}
    (h : classRoot G key = some c) : FreeDegreeCounts G c := by
  have hc := classRoot_coherent hT hG h
  exact freeDegreeCounts_of_matrixWords hM hT hG (classRoot_matrixWords hM hT h) hc
    (classDatum_M_of_T hG hc (classRoot_compressed hT h).1)

theorem classRoot_freeCount {G : Consts} (hM : MatrixWord G.EM)
    (hT : G.WellFormedT) (hG : G.Coherent) {key : ℕ} {c : Cyl}
    (h : classRoot G key = some c) :
    horizontalSum (freeRows G c) = #(freePairs G c) :=
  horizontalSum_freeRows (classRoot_freeDegreeCounts hM hT hG h)

theorem freePairs_eq_T {G : Consts} (hG : G.Coherent) {c : Cyl} (hc : c.Coherent) :
    freePairs G c = decT G.ET \ ((dec c).1 ∪ (dec c).2) := by
  unfold freePairs dec
  rw [hG, hc.1, hc.2]

end Sarkozy.F3Kernel
