module

public import Sarkozy.F3Kernel.LeafTrace

/-!
# The order loops enumerate distinct non-witness vertices

Bits 36 through 63 are initially occupied, so successful loops cannot read a vertex outside
`Fin 36`. Their mask updates are exactly the verified `vmask` scan. Reaching `FULL64` therefore
certifies a complete enumeration, with no repetition or already-occupied vertex.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def HighMask (m : ℕ) : Prop := ∀ u, 36 ≤ u → u < 64 → bit m u = true

theorem firstVertex_lt (r : ℕ) : firstVertex r < 64 := by
  change r &&& (2 ^ 6 - 1) < 64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem HighMask.insert {m : ℕ} (h : HighMask m) (v : ℕ) :
    HighMask (Nat.lor m (Nat.shiftLeft 1 v)) := by
  intro u hu hu'
  rw [bit_lor_bit, h u hu hu', Bool.true_or]

theorem highMask_initial (V : ℕ) : HighMask (Nat.lor V (FULL64 - FULL36)) := by
  have hb : ∀ u : Fin 64, 36 ≤ u.val → bit (FULL64 - FULL36) u = true := by decide +kernel
  intro u hu hu'
  rw [bit_eq_testBit,
    show Nat.lor V (FULL64 - FULL36) = V ||| (FULL64 - FULL36) from rfl, Nat.testBit_or,
    ← bit_eq_testBit (FULL64 - FULL36) u, hb ⟨u, hu'⟩ hu, Bool.or_true]

/-- Acceptance of the integrated loop implies acceptance by the distinct-vertex scanner. -/
theorem uLoop_vmask (G : Consts) {n r mask T acc rest out : ℕ}
    (hhi : HighMask mask) (h : uLoop G n r mask T acc = some (rest, out)) :
    vmask n r mask = some FULL64 := by
  induction n generalizing r mask T acc with
  | zero =>
      change (bif Nat.beq mask FULL64 then some (r, acc) else none) = some (rest, out) at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      next hm =>
        have hm' : mask = FULL64 := by simpa using hm
        simp only [vmask, hm']
      next => cases h
  | succ n ih =>
      rw [uLoop_succ] at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      · cases h
      next hn =>
        split at h
        next =>
          have hu : firstVertex r < 36 := by
            by_contra hn36
            exact hn (hhi _ (by omega) (firstVertex_lt r))
          have hg : (Nat.blt (firstVertex r) 36 && Bool.not (bit mask (firstVertex r))) = true := by
            simp [hu, hn]
          change (bif Nat.blt (firstVertex r) 36 && !(bit mask (firstVertex r)) then
            vmask n (Nat.shiftRight r 6) (Nat.lor mask (Nat.shiftLeft 1 (firstVertex r)))
            else none) = some FULL64
          rw [hg, Bool.cond_true]
          exact ih (hhi.insert _) h
        next => cases h

/-- The cover-to-integrated transition leaves the same distinct-vertex invariant. -/
theorem cLoop_vmask (G : Consts) {FTr cmask wl k hw n r mask T acc rest ex out : ℕ}
    (hhi : HighMask mask) (h : cLoop G FTr cmask wl k hw n r mask T acc = some (rest, ex, out)) :
    vmask n r mask = some FULL64 := by
  induction n generalizing r mask T acc with
  | zero =>
      change (bif Nat.beq mask FULL64 then some (r, (witSwitch G k wl hw T).1, acc)
        else none) = some (rest, ex, out) at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      next hm =>
        have hm' : mask = FULL64 := by simpa using hm
        simp only [vmask, hm']
      next => cases h
  | succ n ih =>
      rw [cLoop_succ] at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      next =>
        split at h
        · cases h
        next hn =>
          split at h
          next =>
            have hu : firstVertex r < 36 := by
              by_contra hn36
              exact hn (hhi _ (by omega) (firstVertex_lt r))
            have hg : (Nat.blt (firstVertex r) 36 && Bool.not (bit mask (firstVertex r))) =
                true := by
              simp [hu, hn]
            change (bif Nat.blt (firstVertex r) 36 && !(bit mask (firstVertex r)) then
              vmask n (Nat.shiftRight r 6) (Nat.lor mask (Nat.shiftLeft 1 (firstVertex r)))
              else none) = some FULL64
            rw [hg, Bool.cond_true]
            exact ih (hhi.insert _) h
          next => cases h
      next =>
        split at h
        next =>
          split at h
          · cases h
          next rest' out' hu => exact uLoop_vmask G hhi hu
        next => cases h

theorem LeafTrace.orderX_vmask {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) :
    vmask (36 - k) (Record.order rec) (Nat.lor t.V (FULL64 - FULL36)) = some FULL64 :=
  cLoop_vmask G (highMask_initial _) t.loopX

theorem LeafTrace.orderY_vmask {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) :
    vmask (36 - k) t.rest (Nat.lor t.W (FULL64 - FULL36)) = some FULL64 :=
  cLoop_vmask G (highMask_initial _) t.loopY

theorem bit_initial_low (V : ℕ) (v : Fin 36) :
    bit (Nat.lor V (FULL64 - FULL36)) v = bit V v := by
  have hb : ∀ u : Fin 36, bit (FULL64 - FULL36) u = false := by decide +kernel
  rw [bit_eq_testBit,
    show Nat.lor V (FULL64 - FULL36) = V ||| (FULL64 - FULL36) from rfl,
    Nat.testBit_or, ← bit_eq_testBit (FULL64 - FULL36) v, hb, Bool.or_false,
    bit_eq_testBit]

/-- The completed order lists precisely the vertices outside the initial witness mask. -/
theorem vmask_order_mem {n r V : ℕ}
    (h : vmask n r (Nat.lor V (FULL64 - FULL36)) = some FULL64) (v : Fin 36) :
    v.val ∈ packedList n r ↔ bit V v = false := by
  have hb := (vmask_sound h).2.2 v.val
  have hfull : ∀ u : Fin 36, bit FULL64 u = true := by decide +kernel
  rw [bit_initial_low, hfull] at hb
  constructor
  · intro hv
    have he := ((vmask_sound h).2.1 v.val hv).2
    rwa [bit_initial_low] at he
  · intro hv
    rw [hv, Bool.false_or] at hb
    exact of_decide_eq_true hb.symm

end Sarkozy.F3Kernel
