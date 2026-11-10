module

public import Sarkozy.F3Kernel.NeighbourCounts

/-!
# The initial cover scan enumerates precisely the cover

The accepted phase-order check identifies the initial `takeWhile` segment with filtering
the full scan by cover membership. Completeness of the scan and disjointness from the
witness then identify this list with the mathematical cover set.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem takeWhile_eq_filter_of_prefix {p : ℕ → Bool} {s : List ℕ}
    (hp : s.Pairwise (fun u v => p v = true → p u = true)) :
    s.takeWhile p = s.filter p := by
  induction s with
  | nil => rfl
  | cons u s ih =>
      obtain ⟨hu, hs⟩ := List.pairwise_cons.mp hp
      by_cases hpu : p u = true
      · simp only [List.takeWhile_cons_of_pos hpu, List.filter_cons_of_pos hpu, ih hs]
      · rw [List.takeWhile_cons_of_neg hpu, List.filter_cons_of_neg hpu]
        exact (List.filter_eq_nil_iff.mpr (fun v hv hpv => hpu (hu v hv hpv))).symm

def coverScan (C : ℕ) (s : List ℕ) : List ℕ := s.takeWhile (bit C)

theorem coverScan_eq_filter {C : ℕ} {s : List ℕ}
    (hp : s.Pairwise (fun u v => bit C v = true → bit C u = true)) :
    coverScan C s = s.filter (bit C) := takeWhile_eq_filter_of_prefix hp

theorem listVertices_coverScan {C V : ℕ} {s : List ℕ}
    (hp : s.Pairwise (fun u v => bit C v = true → bit C u = true))
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ bit V v = false)
    (hd : Nat.land C V = 0) : listVertices (coverScan C s) = decV C := by
  rw [coverScan_eq_filter hp]
  ext v
  rw [mem_listVertices, List.mem_filter, hcomplete, mem_decV]
  constructor
  · exact And.right
  · intro hc
    refine ⟨?_, hc⟩
    have hdisj := decV_disjoint hd
    have hv : bit V v ≠ true := fun hv =>
      Finset.disjoint_left.mp hdisj ((mem_decV _ _).mpr hc) ((mem_decV _ _).mpr hv)
    exact Bool.eq_false_iff.mpr hv

theorem LeafTrace.coverScanX_vertices {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) :
    listVertices (coverScan (Record.cx rec) (packedList (36 - k) (Record.order rec))) =
      decV (Record.cx rec) :=
  listVertices_coverScan t.orderX_cover_prefix (vmask_order_mem t.orderX_vmask) t.disjX

theorem LeafTrace.coverScanY_vertices {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) :
    listVertices (coverScan (Record.cy rec) (packedList (36 - k) t.rest)) =
      decV (Record.cy rec) :=
  listVertices_coverScan t.orderY_cover_prefix (vmask_order_mem t.orderY_vmask) t.disjY

end Sarkozy.F3Kernel
