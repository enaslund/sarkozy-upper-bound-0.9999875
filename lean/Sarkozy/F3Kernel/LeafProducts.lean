module

public import Sarkozy.F3Kernel.PackedProducts
public import Sarkozy.F3Kernel.FreeDegrees

/-!
# Equality with the paper's four factor products

The two checker-side products are exactly the four cover/integrated products of the
constructed extraction record, for arbitrary scalar factor functions.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

noncomputable def recordProduct (H : OrientedGraph (Fin 36))
    (Fr : Finset (Fin 36 × Fin 36)) (R : LeafRecordData (Fin 36)) (m rho : ℕ → ℝ) : ℝ :=
  (∏ v ∈ univ \ (witV R.w ∪ R.Cx), m (intS H R.ordX Fr v)) *
    (∏ v ∈ R.Cz, rho (coverRowS H R.Cz R.ordZ (Fr.filter (fun e => e.2 ∈ R.Cz)) v)) *
    (∏ v ∈ univ \ (witW R.w ∪ R.Cz), m (intS H R.ordZ (Fr.image Prod.swap) v)) *
    ∏ v ∈ R.Cx, rho (coverRowS H R.Cx R.ordX
      ((Fr.image Prod.swap).filter (fun e => e.2 ∈ R.Cx)) v)

theorem rowProduct_counts (H : OrientedGraph (Fin 36)) (Fr : Finset (Fin 36 × Fin 36))
    (V C : Finset (Fin 36)) (ord : Fin 36 → ℕ) (m rho : ℕ → ℝ) :
    (∏ v ∈ C, rho (cmpHx Fr v + coverRowT H C ord v)) *
        (∏ v ∈ univ \ (V ∪ C), m (cmpHx Fr v + ordT H ord v)) =
      (∏ v ∈ C, rho (coverRowS H C ord
        ((Fr.image Prod.swap).filter (fun e => e.2 ∈ C)) v)) *
        ∏ v ∈ univ \ (V ∪ C), m (intS H ord Fr v) := by
  congr 1
  · apply prod_congr rfl
    intro v hv
    rw [coverRowS, cmp_coverRowH_swap_card Fr C hv, Nat.add_comm]
  · apply prod_congr rfl
    intro v _
    rw [intS, cmp_intH_card, Nat.add_comm]

theorem colProduct_counts (H : OrientedGraph (Fin 36)) (Fr : Finset (Fin 36 × Fin 36))
    (W C : Finset (Fin 36)) (ord : Fin 36 → ℕ) (m rho : ℕ → ℝ) :
    (∏ v ∈ C, rho (cmpHz Fr v + coverRowT H C ord v)) *
        (∏ v ∈ univ \ (W ∪ C), m (cmpHz Fr v + ordT H ord v)) =
      (∏ v ∈ C, rho (coverRowS H C ord (Fr.filter (fun e => e.2 ∈ C)) v)) *
        ∏ v ∈ univ \ (W ∪ C), m (intS H ord (Fr.image Prod.swap) v) := by
  congr 1
  · apply prod_congr rfl
    intro v hv
    rw [coverRowS, cmp_coverRowH_card Fr C hv, Nat.add_comm]
  · apply prod_congr rfl
    intro v _
    rw [intS, cmp_intH_swap_card, Nat.add_comm]

theorem LeafTrace.product_eq_recordProduct {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) (hf : FreeDegreeCounts G c) (m rho : ℕ → ℝ) :
    t.product m rho = recordProduct H (freePairs G c) t.record m rho := by
  have hlen : 36 - k + k ≤ 36 := by have := t.size_le; omega
  unfold product
  rw [hf.1, hf.2,
    sideProd_ordered H hG m rho (cmpHx_le_36 _) hlen t.maskX t.orderX_vmask
      t.orderX_cover_prefix t.disjX,
    sideProd_ordered H hG m rho (cmpHz_le_36 _) hlen t.maskY t.orderY_vmask
      t.orderY_cover_prefix t.disjY,
    rowProduct_counts, colProduct_counts]
  unfold recordProduct record
  rw [t.witV_eq, t.witW_eq]
  unfold ordX ordY
  change (_ * _) * (_ * _) = _ * _ * _ * _
  ring

end Sarkozy.F3Kernel
