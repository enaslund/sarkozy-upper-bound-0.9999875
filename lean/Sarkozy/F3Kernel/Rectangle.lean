module

public import Sarkozy.F3Kernel.PackedList
public import Sarkozy.F3Kernel.Components

/-!
# Soundness of the witness-rectangle checker

`rectPat` verifies each diagonal entry and records exactly the off-diagonal presence pattern.
These facts connect its output to the witness digraph, including the bit bounds required by
the finite component-table checks.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def vertexAt (l i : ℕ) : ℕ := Nat.land (Nat.shiftRight l (6 * i)) 63

theorem vertexAt_shift (l i : ℕ) :
    vertexAt (Nat.shiftRight l 6) i = vertexAt l (i + 1) := by
  change ((l >>> 6) >>> (6 * i)) &&& 63 = (l >>> (6 * (i + 1))) &&& 63
  rw [← Nat.shiftRight_add, show 6 + 6 * i = 6 * (i + 1) by omega]

theorem packedList_get (n l : ℕ) (i : Fin n) :
    (packedList n l).get (i.cast (packedList_length n l).symm) = vertexAt l i.val := by
  induction n generalizing l with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change (packedList n (Nat.shiftRight l 6)).get
          (j.cast (packedList_length n (Nat.shiftRight l 6)).symm) = vertexAt l (j.val + 1)
        rw [ih, vertexAt_shift]

theorem witnessVertex_val {n l out : ℕ} (h : vmask n l 0 = some out) (i : Fin n) :
    (witnessVertex h i).val = vertexAt l i.val := packedList_get n l i

def rectBit (PR xs ys k idx : ℕ) : Bool :=
  bit PR (64 * vertexAt xs (idx / k) + vertexAt ys (idx % k))

theorem rectPat_succ (PR xs ys k n pat : ℕ) :
    rectPat PR xs ys k (n + 1) pat =
      (bif Nat.beq (n / k) (n % k) then
        bif rectBit PR xs ys k n then rectPat PR xs ys k n pat else none
      else rectPat PR xs ys k n
        (bif rectBit PR xs ys k n then Nat.lor pat (Nat.shiftLeft 1 n) else pat)) := rfl

/-- The exact meaning of an accepted partial rectangle scan, for an arbitrary initial mask. -/
theorem rectPat_spec {PR xs ys k n pat out : ℕ}
    (h : rectPat PR xs ys k n pat = some out) :
    (∀ i < n, i / k = i % k → rectBit PR xs ys k i = true) ∧
    ∀ i, bit out i = (bit pat i ||
      (decide (i < n ∧ i / k ≠ i % k) && rectBit PR xs ys k i)) := by
  induction n generalizing pat with
  | zero =>
      simp only [rectPat, Option.some.injEq] at h
      subst out
      simp
  | succ n ih =>
      rw [rectPat_succ] at h
      simp only [Bool.cond_eq_ite] at h
      split at h
      next hd =>
        have hd' : n / k = n % k := by simpa using hd
        split at h
        next hb =>
          obtain ⟨hdiag, hbits⟩ := ih h
          refine ⟨?_, ?_⟩
          · intro i hi he
            by_cases hin : i < n
            · exact hdiag i hin he
            · have : i = n := by omega
              simpa only [this] using hb
          · intro i
            rw [hbits]
            by_cases hin : i = n
            · simp [hin, hd']
            · have he : (i < n + 1) = (i < n) := propext (by omega)
              simp only [he]
        next => cases h
      next hd =>
        have hd' : n / k ≠ n % k := by simpa using hd
        split at h
        next hb =>
          obtain ⟨hdiag, hbits⟩ := ih h
          refine ⟨?_, ?_⟩
          · intro i hi he
            apply hdiag i _ he
            have : i ≠ n := by rintro rfl; exact hd' he
            omega
          · intro i
            rw [hbits, bit_lor_bit]
            by_cases hin : i = n
            · simp [hin, hd', hb]
            · have he : (i < n + 1) = (i < n) := propext (by omega)
              simp [Ne.symm hin, he]
        next hb =>
          obtain ⟨hdiag, hbits⟩ := ih h
          refine ⟨?_, ?_⟩
          · intro i hi he
            apply hdiag i _ he
            have : i ≠ n := by rintro rfl; exact hd' he
            omega
          · intro i
            rw [hbits]
            by_cases hin : i = n
            · simp [hin, hd', hb]
            · have he : (i < n + 1) = (i < n) := propext (by omega)
              simp only [he]

/-- No output bit lies beyond the portion of the rectangle scanned. -/
theorem rectPat_lt {PR xs ys k n out : ℕ} (h : rectPat PR xs ys k n 0 = some out) :
    out < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hb := (rectPat_spec h).2 i
  simpa only [bit_eq_testBit, Nat.zero_testBit, Bool.false_or,
    show ¬ i < n from by omega, false_and, decide_false, Bool.false_and] using hb

/-- A row-major position has the specified quotient and remainder. -/
theorem rectPosition {k : ℕ} (i j : Fin k) :
    (k * i.val + j.val) / k = i.val ∧ (k * i.val + j.val) % k = j.val := by
  have hk : 0 < k := i.pos
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt j.isLt]
    simp
  · simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

theorem rectPosition_lt {k : ℕ} (i j : Fin k) : k * i.val + j.val < k * k := by
  have hi := i.isLt
  have hj := j.isLt
  have hh := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hi)
  nlinarith

theorem rectPat_diagonal_zero {PR xs ys k out : ℕ}
    (h : rectPat PR xs ys k (k * k) 0 = some out) (i : Fin k) :
    bit out (k * i.val + i.val) = false := by
  have hb := (rectPat_spec h).2 (k * i.val + i.val)
  rw [(rectPosition i i).1, (rectPosition i i).2] at hb
  simpa only [ne_eq, not_true_eq_false, and_false, decide_false, Bool.false_and,
    bit_eq_testBit, Nat.zero_testBit, Bool.false_or] using hb

/-- Restoring the diagonal in the recorded pattern recovers precisely the present rectangle. -/
theorem rectPat_rectangle {PR xs ys k out : ℕ}
    (h : rectPat PR xs ys k (k * k) 0 = some out) (i j : Fin k) :
    (i, j) ∈ Components.rectangle k out ↔
      bit PR (64 * vertexAt xs i.val + vertexAt ys j.val) = true := by
  have hb := (rectPat_spec h).2 (k * i.val + j.val)
  have hd := (rectPat_spec h).1 (k * i.val + j.val) (rectPosition_lt i j)
  simp only [rectBit, (rectPosition i j).1, (rectPosition i j).2] at hb hd
  simp only [Components.rectangle, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases he : i = j
  · subst j
    simp only [true_or, true_iff]
    exact hd rfl
  · have hv : i.val ≠ j.val := fun heq => he (Fin.ext heq)
    have hc : k * i.val + j.val < k * k ∧ i.val ≠ j.val := ⟨rectPosition_lt i j, hv⟩
    have hdec : decide (k * i.val + j.val < k * k ∧ i.val ≠ j.val) = true :=
      decide_eq_true hc
    rw [hdec, Bool.true_and] at hb
    simp only [bit_eq_testBit, Nat.zero_testBit, Bool.false_or,
      ] at hb
    simp only [he, false_or, bit_eq_testBit, hb]

end Sarkozy.F3Kernel
