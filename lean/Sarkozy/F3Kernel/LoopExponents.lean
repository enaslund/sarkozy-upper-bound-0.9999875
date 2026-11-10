module

public import Sarkozy.F3Kernel.CoverScan

/-!
# Accepted loops compute the cover and witness exponent

The returned exponent is the witness-switch exponent after exactly the initial cover
scan. Combining the control-flow identity with count-vector arithmetic gives its graph
interpretation, conditional only on the initial free-degree encoding.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem cLoop_exponent {G : Consts} {FTr C wl k hw n r mask T acc rest ex out : ℕ}
    (hc : cLoop G FTr C wl k hw n r mask T acc = some (rest, ex, out)) :
    ex = (witSwitch G k wl hw
      (T + ((coverScan C (packedList n r)).map (adj64 G)).sum)).1 := by
  induction n generalizing r mask T acc with
  | zero =>
      change (bif Nat.beq mask FULL64 then some (r, (witSwitch G k wl hw T).1, acc)
        else none) = some (rest, ex, out) at hc
      simp only [Bool.cond_eq_ite] at hc
      split at hc
      · cases hc
        simp only [packedList, coverScan, List.takeWhile_nil, List.map_nil,
          List.sum_nil, Nat.add_zero]
      · cases hc
  | succ n ih =>
      rw [cLoop_succ] at hc
      simp only [Bool.cond_eq_ite] at hc
      split at hc
      next hcover =>
        split at hc
        · cases hc
        next =>
          split at hc
          next =>
            have he := ih hc
            change ex = (witSwitch G k wl hw
              (T + (((firstVertex r :: packedList n (Nat.shiftRight r 6)).takeWhile
                (bit C)).map (adj64 G)).sum)).1
            rw [List.takeWhile_cons_of_pos hcover, List.map_cons, List.sum_cons,
              ← Nat.add_assoc]
            exact he
          next => cases hc
      next hcover =>
        split at hc
        next =>
          split at hc
          · cases hc
          next =>
            cases hc
            change (witSwitch G k wl hw T).1 = (witSwitch G k wl hw
              (T + (((firstVertex r :: packedList n (Nat.shiftRight r 6)).takeWhile
                (bit C)).map (adj64 G)).sum)).1
            rw [List.takeWhile_cons_of_neg hcover]
            rfl
        next => cases hc

variable (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]

theorem cLoop_exponent_counts {G : Consts} (hG : AdjacencyCounts G E)
    {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36)
    {FTr C wl k n r mask acc rest ex out : ℕ} (hlen : n + k ≤ 36)
    (hw : ∀ u ∈ packedList k wl, u < 36) (hhi : HighMask mask)
    (hc : cLoop G FTr C wl k (hSum (packCounts h) k wl) n r mask (packCounts h) acc =
      some (rest, ex, out)) :
    ex = sumVertices (neighbourSum E (coverScan C (packedList n r))) (packedList k wl) +
      sumVertices (neighbourSum E (packedList k wl)) (packedList k wl) / 2 := by
  have hscan := (vmask_sound (cLoop_vmask G hhi hc)).2.1
  have hcover := coverScan_eq_filter (cLoop_cover_prefix G hhi hc)
  have hp : ∀ u ∈ coverScan C (packedList n r), u < 36 := by
    intro u hu
    rw [hcover] at hu
    exact (hscan u (List.mem_filter.mp hu).1).1
  have hl : (coverScan C (packedList n r)).length + k ≤ 36 := by
    rw [hcover]
    have ht := List.length_filter_le (bit C) (packedList n r)
    rw [packedList_length] at ht
    omega
  rw [cLoop_exponent hc, adjacency_list_sum E hG hp, ← packCounts_add]
  exact witSwitch_exponent E hG hh hl hw

theorem LeafTrace.eX_eq_counts {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) (hG : AdjacencyCounts G E)
    {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36) (hfree : freeRows G c = packCounts h) :
    t.eX = sumVertices
        (neighbourSum E (coverScan (Record.cx rec) (packedList (36 - k) (Record.order rec))))
        (packedList k (Record.xs rec)) +
      sumVertices (neighbourSum E (packedList k (Record.xs rec)))
        (packedList k (Record.xs rec)) / 2 := by
  have hc := t.loopX
  rw [hfree] at hc
  exact cLoop_exponent_counts E hG hh (by have := t.size_le; omega)
    (fun u hu => ((vmask_sound t.maskX).2.1 u hu).1) (highMask_initial _) hc

theorem LeafTrace.eY_eq_counts {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) (hG : AdjacencyCounts G E)
    {h : Fin 36 → ℕ} (hh : ∀ v, h v ≤ 36) (hfree : freeCols G c = packCounts h) :
    t.eZ = sumVertices
        (neighbourSum E (coverScan (Record.cy rec) (packedList (36 - k) t.rest)))
        (packedList k (Record.ys rec)) +
      sumVertices (neighbourSum E (packedList k (Record.ys rec)))
        (packedList k (Record.ys rec)) / 2 := by
  have hc := t.loopY
  rw [hfree] at hc
  exact cLoop_exponent_counts E hG hh (by have := t.size_le; omega)
    (fun u hu => ((vmask_sound t.maskY).2.1 u hu).1) (highMask_initial _) hc

end Sarkozy.F3Kernel
