module

public import Sarkozy.F3Kernel.LoopExponents
public import Sarkozy.ExtractionK.Compressed

/-!
# Witness exponents as edge counts

Internal adjacency sums count each oriented graph edge twice. For disjoint vertex sets,
the adjacency sum across the sets counts each edge once. These identities connect the
checker's division by two to the paper's witness contribution to `recordExp`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

def graphAdj (H : OrientedGraph (Fin 36)) (u v : Fin 36) : Prop :=
  (u, v) ∈ H.E ∨ (v, u) ∈ H.E

instance graphAdj_decidable (H : OrientedGraph (Fin 36)) : DecidableRel (graphAdj H) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem sum_nbrCount_internal (H : OrientedGraph (Fin 36)) (V : Finset (Fin 36)) :
    ∑ v ∈ V, nbrCount H V v = 2 * edgesIn H V := by
  have ht (v : Fin 36) : nbrCount H V v =
      (V.filter (fun u => (u, v) ∈ H.E ∧ True)).card +
        (V.filter (fun u => (v, u) ∈ H.E ∧ True)).card := by
    simpa only [true_and, nbrCount] using cmp_nbrCount_split H V v (fun _ => True)
  simp_rw [ht]
  rw [sum_add_distrib, cmp_sum_card_in, cmp_sum_card_out]
  simp only [and_true, edgesIn]
  omega

theorem sum_nbrCount_between (H : OrientedGraph (Fin 36)) (V C : Finset (Fin 36))
    (hd : Disjoint V C) : ∑ v ∈ V, nbrCount H C v = edgesBetween H V C := by
  have ht (v : Fin 36) : nbrCount H C v =
      (C.filter (fun u => (u, v) ∈ H.E ∧ True)).card +
        (C.filter (fun u => (v, u) ∈ H.E ∧ True)).card := by
    simpa only [true_and, nbrCount] using cmp_nbrCount_split H C v (fun _ => True)
  simp_rw [ht]
  rw [sum_add_distrib, cmp_sum_card_in, cmp_sum_card_out, ← card_union_of_disjoint]
  · unfold edgesBetween
    congr 1
    ext e
    simp only [mem_union, mem_filter, and_true]
    tauto
  · rw [disjoint_left]
    intro e he hf
    exact disjoint_left.mp hd (mem_filter.mp he).2.2.1 (mem_filter.mp hf).2.2.1

theorem sumVertices_neighbourSum (H : OrientedGraph (Fin 36))
    {s w : List ℕ} (hsn : s.Nodup) (hwn : w.Nodup)
    (hs : ∀ u ∈ s, u < 36) (hw : ∀ u ∈ w, u < 36) :
    sumVertices (neighbourSum (graphAdj H) s) w =
      ∑ v ∈ listVertices w, nbrCount H (listVertices s) v := by
  rw [sumVertices_eq_sum _ hwn hw]
  apply sum_congr rfl
  intro v _
  exact neighbourSum_eq_card (graphAdj H) hsn hs v

theorem listVertices_witness {k wl V : ℕ} (hm : vmask k wl 0 = some V) :
    listVertices (packedList k wl) = decV V := by
  ext v
  rw [mem_listVertices, mem_decV, vmask_zero_bit hm, decide_eq_true_eq]

theorem RecordOrder.sum_ordT {V C : Finset (Fin 36)} {ord : Fin 36 → ℕ}
    (ho : RecordOrder V C ord) (hd : Disjoint V C) (H : OrientedGraph (Fin 36)) :
    ∑ v ∈ V, ordT H ord v = edgesIn H V + edgesBetween H V C := by
  apply cmp_sum_ordT H V C ord ho.injective
  · exact fun v hv hc => disjoint_left.mp hd hv hc
  · exact fun a ha v hv => ho.coverFirst a ha v (fun hc => disjoint_left.mp hd hv hc)
  · intro u huV huC v hv
    refine ho.integratedLast v ?_ u ?_
    · simp only [mem_sdiff, mem_univ, true_and, mem_union, not_not]
      exact Or.inl hv
    · simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or]
      exact ⟨huV, huC⟩

theorem witness_exponent_eq_edges (H : OrientedGraph (Fin 36))
    {s w : List ℕ} (hsn : s.Nodup) (hwn : w.Nodup)
    (hs : ∀ u ∈ s, u < 36) (hw : ∀ u ∈ w, u < 36)
    (hd : Disjoint (listVertices w) (listVertices s)) :
    sumVertices (neighbourSum (graphAdj H) s) w +
        sumVertices (neighbourSum (graphAdj H) w) w / 2 =
      edgesIn H (listVertices w) + edgesBetween H (listVertices w) (listVertices s) := by
  rw [sumVertices_neighbourSum H hsn hwn hs hw, sumVertices_neighbourSum H hwn hwn hw hw,
    sum_nbrCount_between H _ _ hd, sum_nbrCount_internal]
  omega

theorem coverScan_nodup {C : ℕ} {s : List ℕ} (hn : s.Nodup)
    (hp : s.Pairwise (fun u v => bit C v = true → bit C u = true)) :
    (coverScan C s).Nodup := by
  rw [coverScan_eq_filter hp]
  exact hn.filter _

theorem coverScan_lt {C : ℕ} {s : List ℕ} (hs : ∀ u ∈ s, u < 36)
    (hp : s.Pairwise (fun u v => bit C v = true → bit C u = true)) :
    ∀ u ∈ coverScan C s, u < 36 := by
  rw [coverScan_eq_filter hp]
  exact fun u hu => hs u (List.mem_filter.mp hu).1

theorem LeafTrace.eX_eq_ordT {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) {h : Fin 36 → ℕ}
    (hh : ∀ v, h v ≤ 36) (hfree : freeRows G c = packCounts h) :
    t.eX = ∑ v ∈ witV t.witness, ordT H t.ordX v := by
  have hd : Disjoint (witV t.witness) (decV (Record.cx rec)) := by
    rw [t.witV_eq]
    exact (decV_disjoint t.disjX).symm
  rw [t.orderX_valid.sum_ordT hd H, t.eX_eq_counts (graphAdj H) hG hh hfree]
  have ho := vmask_sound t.orderX_vmask
  have hw := vmask_sound t.maskX
  have he := witness_exponent_eq_edges H
    (coverScan_nodup ho.1 t.orderX_cover_prefix) hw.1
    (coverScan_lt (fun u hu => (ho.2.1 u hu).1) t.orderX_cover_prefix)
    (fun u hu => (hw.2.1 u hu).1)
  rw [listVertices_witness t.maskX, t.coverScanX_vertices, ← t.witV_eq] at he
  exact he hd

theorem LeafTrace.eY_eq_ordT {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) {h : Fin 36 → ℕ}
    (hh : ∀ v, h v ≤ 36) (hfree : freeCols G c = packCounts h) :
    t.eZ = ∑ v ∈ witW t.witness, ordT H t.ordY v := by
  have hd : Disjoint (witW t.witness) (decV (Record.cy rec)) := by
    rw [t.witW_eq]
    exact (decV_disjoint t.disjY).symm
  rw [t.orderY_valid.sum_ordT hd H, t.eY_eq_counts (graphAdj H) hG hh hfree]
  have ho := vmask_sound t.orderY_vmask
  have hw := vmask_sound t.maskY
  have he := witness_exponent_eq_edges H
    (coverScan_nodup ho.1 t.orderY_cover_prefix) hw.1
    (coverScan_lt (fun u hu => (ho.2.1 u hu).1) t.orderY_cover_prefix)
    (fun u hu => (hw.2.1 u hu).1)
  rw [listVertices_witness t.maskY, t.coverScanY_vertices, ← t.witW_eq] at he
  exact he hd

end Sarkozy.F3Kernel
