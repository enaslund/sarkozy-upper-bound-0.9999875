module

public import Sarkozy.F3Kernel.OrderBlocks
public import Sarkozy.F3Kernel.LeafRecords

/-!
# The record order agrees with the checker's scan

For non-witness vertices, comparison of the constructed record ranks is exactly comparison
of their positions in the packed scan. The accepted cover-prefix condition supplies the
only possible cross-phase comparison.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem coverPrefix_of_idxOf_lt {s : List ℕ} {C a b : ℕ}
    (hp : s.Pairwise (fun u v => bit C v = true → bit C u = true))
    (ha : a ∈ s) (hb : b ∈ s) (hlt : s.idxOf a < s.idxOf b) :
    bit C b = true → bit C a = true := by
  have hrel := hp.rel_getElem_of_lt (List.idxOf_lt_length_of_mem ha)
    (List.idxOf_lt_length_of_mem hb) hlt
  simpa only [List.getElem_idxOf] using hrel

theorem orderRank_lt_of_scan_lt {w s : List ℕ} {C : ℕ}
    (hw : w.length ≤ 36) (hs : s.length ≤ 36)
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w)
    (hp : s.Pairwise (fun u v => bit C v = true → bit C u = true))
    {a b : Fin 36} (ha : a.val ∉ w) (hb : b.val ∉ w)
    (hlt : s.idxOf a.val < s.idxOf b.val) :
    orderRank w s (decV C) a < orderRank w s (decV C) b := by
  by_cases hac : a ∈ decV C <;> by_cases hbc : b ∈ decV C
  · simp only [orderRank, orderBlock, orderPosition, hac, hbc, ha, hb,
      ite_true, ite_false, mul_zero, zero_add]
    exact hlt
  · exact orderRank_cover_first hw hs hcomplete hac hbc
  · have hm := coverPrefix_of_idxOf_lt hp ((hcomplete a).mpr ha)
      ((hcomplete b).mpr hb) hlt ((mem_decV _ _).mp hbc)
    exact False.elim (hac ((mem_decV _ _).mpr hm))
  · simp only [orderRank, orderBlock, orderPosition, hac, hbc, ha, hb, ite_false]
    omega

theorem orderRank_lt_iff_scan_lt {w s : List ℕ} {C : ℕ}
    (hw : w.length ≤ 36) (hs : s.length ≤ 36)
    (hcomplete : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w)
    (hp : s.Pairwise (fun u v => bit C v = true → bit C u = true))
    {a b : Fin 36} (ha : a.val ∉ w) (hb : b.val ∉ w) :
    orderRank w s (decV C) a < orderRank w s (decV C) b ↔ s.idxOf a.val < s.idxOf b.val := by
  refine ⟨?_, orderRank_lt_of_scan_lt hw hs hcomplete hp ha hb⟩
  intro hr
  rcases lt_trichotomy (s.idxOf a.val) (s.idxOf b.val) with hlt | heq | hgt
  · exact hlt
  · have hab : a = b := Fin.ext ((List.idxOf_inj ((hcomplete a).mpr ha)).mp heq)
    subst b
    exact False.elim ((lt_irrefl _) hr)
  · have hrev := orderRank_lt_of_scan_lt hw hs hcomplete hp hb ha hgt
    exact False.elim ((not_lt_of_ge hrev.le) hr)

theorem rank_scan_of_masks {k n xs r V C : ℕ} (hk : k ≤ 36) (hn : n ≤ 36)
    (hx : vmask k xs 0 = some V)
    (ho : vmask n r (Nat.lor V (FULL64 - FULL36)) = some FULL64)
    (hp : (packedList n r).Pairwise (fun u v => bit C v = true → bit C u = true))
    {a b : Fin 36} (ha : bit V a = false) (hb : bit V b = false) :
    orderRank (packedList k xs) (packedList n r) (decV C) a <
      orderRank (packedList k xs) (packedList n r) (decV C) b ↔
      (packedList n r).idxOf a.val < (packedList n r).idxOf b.val := by
  have hcomplete : ∀ v : Fin 36, v.val ∈ packedList n r ↔ v.val ∉ packedList k xs := by
    intro v
    rw [vmask_order_mem ho, vmask_zero_bit hx]
    simp
  apply orderRank_lt_iff_scan_lt (by simpa only [packedList_length] using hk)
    (by simpa only [packedList_length] using hn) hcomplete hp
  · rw [vmask_zero_bit hx] at ha
    exact of_decide_eq_false ha
  · rw [vmask_zero_bit hx] at hb
    exact of_decide_eq_false hb

theorem LeafTrace.ordX_lt_iff_scan {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) {a b : Fin 36}
    (ha : bit t.V a = false) (hb : bit t.V b = false) :
    t.ordX a < t.ordX b ↔ (packedList (36 - k) (Record.order rec)).idxOf a.val <
      (packedList (36 - k) (Record.order rec)).idxOf b.val :=
  rank_scan_of_masks t.size_le (Nat.sub_le _ _) t.maskX t.orderX_vmask
    t.orderX_cover_prefix ha hb

theorem LeafTrace.ordY_lt_iff_scan {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) {a b : Fin 36}
    (ha : bit t.W a = false) (hb : bit t.W b = false) :
    t.ordY a < t.ordY b ↔ (packedList (36 - k) t.rest).idxOf a.val <
      (packedList (36 - k) t.rest).idxOf b.val :=
  rank_scan_of_masks t.size_le (Nat.sub_le _ _) t.maskY t.orderY_vmask
    t.orderY_cover_prefix ha hb

end Sarkozy.F3Kernel
