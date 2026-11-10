module

public import Sarkozy.F3Kernel.SideProducts

/-!
# Accepted packed scans compute the paper's ordered factors
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem sideProd_ordered {G : Consts} (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) (m rho : ℕ → ℝ)
    {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36) {k n wl r V C hw : ℕ}
    (hlen : n + k ≤ 36) (hx : vmask k wl 0 = some V)
    (hs : vmask n r (Nat.lor V (FULL64 - FULL36)) = some FULL64)
    (hp : (packedList n r).Pairwise (fun u v => bit C v = true → bit C u = true))
    (hd : Nat.land C V = 0) :
    sideProd G m rho C wl k hw n r (packCounts h) =
      (∏ v ∈ decV C, rho (h v + coverRowT H (decV C)
        (orderRank (packedList k wl) (packedList n r) (decV C)) v)) *
      ∏ v ∈ univ \ (decV V ∪ decV C), m (h v + ordT H
        (orderRank (packedList k wl) (packedList n r) (decV C)) v) := by
  have hwv := vmask_sound hx
  have hsv := vmask_sound hs
  have hwb : ∀ u ∈ packedList k wl, u < 36 := fun u hu => (hwv.2.1 u hu).1
  have hsb : ∀ u ∈ packedList n r, u < 36 := fun u hu => (hsv.2.1 u hu).1
  have hc : ∀ v : Fin 36, v.val ∈ packedList n r ↔ v.val ∉ packedList k wl := by
    intro v
    rw [vmask_order_mem hs, vmask_zero_bit hx]
    simp
  have ho := recordOrder_of_masks (by omega) (by omega) hx hs hd
  rw [← listVertices_witness hx] at ho
  have hr : ∀ a ∈ listVertices (packedList n r), ∀ b ∈ listVertices (packedList n r),
      orderRank (packedList k wl) (packedList n r) (decV C) a <
        orderRank (packedList k wl) (packedList n r) (decV C) b ↔
      (packedList n r).idxOf a.val < (packedList n r).idxOf b.val := by
    intro a ha b hb
    exact rank_scan_of_masks (by omega) (by omega) hx hs hp
      ((vmask_order_mem hs a).mp ((mem_listVertices _ _).mp ha))
      ((vmask_order_mem hs b).mp ((mem_listVertices _ _).mp hb))
  change sideProd G m rho C wl k hw n r
    (packCounts (countState (graphAdj H) h [])) = _
  rw [sideProd_counts (graphAdj H) hG m rho hh (by simpa using hlen) hwb hsb]
  rw [sideCountProd_ordered H m rho h C _ hwv.1 hsv.1 hwb hsb hc
    (listVertices_coverScan hp (vmask_order_mem hs) hd) ho hr, listVertices_witness hx]

end Sarkozy.F3Kernel
