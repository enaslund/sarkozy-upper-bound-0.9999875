module

public import Sarkozy.F3Kernel.Split
public import Mathlib.Data.List.Nodup

/-!
# Decoding the certificate's witness lists

An accepted `vmask` contains exactly the listed vertices. They are distinct, below 36,
and disjoint from the initial mask. In particular, the two accepted witness lists determine
injective maps into the actual vertex type `Fin 36`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

/-- A packed sequence, read in the same order as the checker (six bits per vertex). -/
def packedList : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, l => Nat.land l 63 :: packedList n (Nat.shiftRight l 6)

@[simp] theorem packedList_length (n l : ℕ) : (packedList n l).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => simp [packedList, ih]

theorem bit_lor_bit (m v p : ℕ) :
    bit (Nat.lor m (Nat.shiftLeft 1 v)) p = (bit m p || decide (v = p)) := by
  simp only [bit_eq_testBit, testBit_lor_bit]

/-- Full soundness of the vertex-mask checker, including its accumulator. -/
theorem vmask_sound {n l m out : ℕ} (h : vmask n l m = some out) :
    (packedList n l).Nodup ∧
      (∀ v ∈ packedList n l, v < 36 ∧ bit m v = false) ∧
      ∀ p, bit out p = (bit m p || decide (p ∈ packedList n l)) := by
  induction n generalizing l m out with
  | zero =>
      simp only [vmask, Option.some.injEq] at h
      subst out
      simp [packedList]
  | succ n ih =>
      simp only [vmask] at h
      cases hg : (Nat.blt (Nat.land l 63) 36 && !(bit m (Nat.land l 63)))
      · simp only [hg, Bool.cond_false] at h
        cases h
      · rw [hg, Bool.cond_true] at h
        have hg' : Nat.land l 63 < 36 ∧ bit m (Nat.land l 63) = false := by
          simpa only [Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq,
            Bool.not_eq_true'] using hg
        obtain ⟨hn, hv, hm⟩ := ih h
        have hne : Nat.land l 63 ∉ packedList n (Nat.shiftRight l 6) := by
          intro hin
          have hb := (hv _ hin).2
          simp only [bit_lor_bit, decide_true, Bool.or_true] at hb
          cases hb
        refine ⟨List.nodup_cons.mpr ⟨hne, hn⟩, ?_, ?_⟩
        · intro v hv'
          rcases List.mem_cons.mp hv' with rfl | ht
          · exact hg'
          · have hh := hv v ht
            rw [bit_lor_bit, Bool.or_eq_false_iff] at hh
            exact ⟨hh.1, hh.2.1⟩
        · intro p
          rw [hm, bit_lor_bit]
          simp [packedList, eq_comm, Bool.or_assoc]

/-- The mask after a witness list starting from zero is precisely that list's support. -/
theorem vmask_zero_bit {n l out : ℕ} (h : vmask n l 0 = some out) (p : ℕ) :
    bit out p = decide (p ∈ packedList n l) := by
  simpa only [bit_eq_testBit, Nat.zero_testBit, Bool.false_or] using (vmask_sound h).2.2 p

/-- The indexed sequence decoded by an accepted witness mask. -/
def witnessVertex {n l out : ℕ} (h : vmask n l 0 = some out) (i : Fin n) : Fin 36 :=
  let j : Fin (packedList n l).length := i.cast (packedList_length n l).symm
  ⟨(packedList n l).get j, ((vmask_sound h).2.1 _ (List.get_mem _ _)).1⟩

theorem witnessVertex_injective {n l out : ℕ} (h : vmask n l 0 = some out) :
    Function.Injective (witnessVertex h) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  have he := (vmask_sound h).1.injective_get hv
  exact Fin.ext (congrArg (fun t : Fin (packedList n l).length => t.val) he)

theorem mem_packedList_iff {n l out : ℕ} (h : vmask n l 0 = some out) (v : ℕ) :
    v ∈ packedList n l ↔ ∃ i, (witnessVertex h i).val = v := by
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
    refine ⟨i.cast (packedList_length n l), ?_⟩
    exact hi
  · rintro ⟨i, rfl⟩
    exact List.get_mem _ _

/-- The accepted witness mask and the image of its injective enumeration agree. -/
theorem vmask_zero_mem {n l out : ℕ} (h : vmask n l 0 = some out) (v : Fin 36) :
    bit out v = true ↔ ∃ i, witnessVertex h i = v := by
  rw [vmask_zero_bit h, decide_eq_true_eq, mem_packedList_iff h]
  exact exists_congr fun i => Fin.ext_iff.symm

end Sarkozy.F3Kernel
