module

public import Sarkozy.F3Kernel.OrderLoops

/-!
# The computed order places every cover vertex before every integrated vertex

At the switch to `uLoop`, the checker requires that the whole cover mask is already labelled.
The remaining scan avoids the labelled mask. This proves the phase ordering of the actual
packed sequence, needed to identify its computed signatures with the record's graph counts.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem bit_of_land_eq {a b : ℕ} (h : Nat.land a b = a) {v : ℕ}
    (hv : bit a v = true) : bit b v = true := by
  have hs : bits a ⊆ bits b := by
    rw [← h, bits_land]
    exact Finset.inter_subset_right
  exact (mem_bits _ _).mp (hs ((mem_bits _ _).mpr hv))

theorem vmask_avoids_submask {n r mask out cmask : ℕ}
    (h : vmask n r mask = some out) (hsub : Nat.land cmask mask = cmask) :
    ∀ v ∈ packedList n r, bit cmask v ≠ true := by
  intro v hv hc
  have hm := ((vmask_sound h).2.1 v hv).2
  have hm' := bit_of_land_eq hsub hc
  rw [hm'] at hm
  cases hm

theorem cLoop_cover_prefix (G : Consts) {FTr cmask wl k hw n r mask T acc rest ex out : ℕ}
    (hhi : HighMask mask) (h : cLoop G FTr cmask wl k hw n r mask T acc = some (rest, ex, out)) :
    (packedList n r).Pairwise (fun u v => bit cmask v = true → bit cmask u = true) := by
  induction n generalizing r mask T acc with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [cLoop_succ] at h
    simp only [Bool.cond_eq_ite] at h
    split at h
    next hc =>
      split at h
      · cases h
      next =>
        split at h
        next =>
          change (firstVertex r :: packedList n (Nat.shiftRight r 6)).Pairwise _
          exact List.pairwise_cons.mpr ⟨fun _ _ _ => hc, ih (hhi.insert _) h⟩
        next => cases h
    next =>
      split at h
      next hsub =>
        have hsub' : Nat.land cmask mask = cmask := Nat.eq_of_beq_eq_true hsub
        split at h
        · cases h
        next rest' out' hu =>
          have hn := vmask_avoids_submask (uLoop_vmask G hhi hu) hsub'
          apply List.pairwise_of_forall_mem_list
          intro u _ v hv hc
          exact False.elim (hn v hv hc)
      next => cases h

theorem LeafTrace.orderX_cover_prefix {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) :
    (packedList (36 - k) (Record.order rec)).Pairwise
      (fun u v => bit (Record.cx rec) v = true → bit (Record.cx rec) u = true) :=
  cLoop_cover_prefix G (highMask_initial _) t.loopX

theorem LeafTrace.orderY_cover_prefix {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) :
    (packedList (36 - k) t.rest).Pairwise
      (fun u v => bit (Record.cy rec) v = true → bit (Record.cy rec) u = true) :=
  cLoop_cover_prefix G (highMask_initial _) t.loopY

end Sarkozy.F3Kernel
