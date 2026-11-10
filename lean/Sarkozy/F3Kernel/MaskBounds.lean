module

public import Sarkozy.F3Kernel.LaneDecoding

/-!
# Matrix-word invariants and free-degree soundness

Mask operations preserve the absence of unused bits. For coherent class masks satisfying
this invariant, the SWAR outputs encode precisely the free degrees in both layouts.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem MatrixWord.land {a : ℕ} (ha : MatrixWord a) (b : ℕ) :
    MatrixWord (Nat.land a b) := by
  intro p hp
  change (a &&& b).testBit p = true at hp
  rw [Nat.testBit_and, Bool.and_eq_true] at hp
  exact ha p hp.1

theorem MatrixWord.lor {a b : ℕ} (ha : MatrixWord a) (hb : MatrixWord b) :
    MatrixWord (Nat.lor a b) := by
  intro p hp
  change (a ||| b).testBit p = true at hp
  rw [Nat.testBit_or, Bool.or_eq_true] at hp
  exact hp.elim (ha p) (hb p)

theorem MatrixWord.xor {a b : ℕ} (ha : MatrixWord a) (hb : MatrixWord b) :
    MatrixWord (Nat.xor a b) := by
  intro p hp
  change (a ^^^ b).testBit p = true at hp
  rw [Nat.testBit_xor] at hp
  cases hpa : a.testBit p <;> cases hpb : b.testBit p
  · simp [hpa, hpb] at hp
  · exact hb p hpb
  · exact ha p hpa
  · exact ha p hpa

theorem matrixWord_single (u v : Fin 36) :
    MatrixWord (Nat.shiftLeft 1 (64 * u.val + v.val)) := by
  intro p hp
  change (1 <<< (64 * u.val + v.val)).testBit p = true at hp
  simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_eq] at hp
  subst p
  have := u.isLt
  have := v.isLt
  constructor <;> omega

theorem matrixWord_of_bounded {m N : ℕ} (hm : m < 2 ^ N)
    (hb : ∀ p < N, m.testBit p = true → p % 64 < 36 ∧ p / 64 < 36) : MatrixWord m := by
  intro p hp
  by_cases h : p < N
  · exact hb p h hp
  · have hh : m < 2 ^ p := hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow hh] at hp
    cases hp

theorem LL20_matrixWordM : MatrixWord LL20.EM :=
  matrixWord_of_bounded (N := 2304) (by decide +kernel) (by decide +kernel)

theorem LL22_matrixWordM : MatrixWord LL22.EM :=
  matrixWord_of_bounded (N := 2304) (by decide +kernel) (by decide +kernel)

def Cyl.MatrixWords (c : Cyl) : Prop :=
  MatrixWord c.pm ∧ MatrixWord c.am ∧ MatrixWord c.pt ∧ MatrixWord c.qt

theorem Cyl.MatrixWords.present {c : Cyl} (hc : c.MatrixWords) (e : Fin 36 × Fin 36) :
    (c.present e).MatrixWords :=
  ⟨hc.1.lor (matrixWord_single _ _), hc.2.1,
    hc.2.2.1.lor (matrixWord_single _ _), hc.2.2.2⟩

theorem Cyl.MatrixWords.absent {c : Cyl} (hc : c.MatrixWords) (e : Fin 36 × Fin 36) :
    (c.absent e).MatrixWords :=
  ⟨hc.1, hc.2.1.lor (matrixWord_single _ _),
    hc.2.2.1, hc.2.2.2.lor (matrixWord_single _ _)⟩

theorem freeDegreeCounts_of_matrixWords {G : Consts} {c : Cyl}
    (hM : MatrixWord G.EM) (hT : G.WellFormedT) (hG : G.Coherent)
    (hc : c.MatrixWords) (hcoh : c.Coherent)
    (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am)) : FreeDegreeCounts G c := by
  have hm := hM.xor (hc.1.lor hc.2.1)
  have ht := MatrixWord.xor hT (hc.2.2.1.lor hc.2.2.2)
  have hsub : decM (Nat.lor c.pm c.am) ⊆ decM G.EM := by
    rw [decM_lor]
    exact union_subset hclass.1 hclass.2.1
  have hsubT : decT (Nat.lor c.pt c.qt) ⊆ decT G.ET := by
    rw [decT_lor, ← hcoh.1, ← hcoh.2, ← hG]
    exact union_subset hclass.1 hclass.2.1
  constructor
  · rw [freeRows, hm.swar_rows, decM_xor hsub, decM_lor]
    rfl
  · rw [freeCols, ht.swar_cols, decT_xor hsubT, decT_lor, ← hcoh.1, ← hcoh.2, ← hG]
    rfl

end Sarkozy.F3Kernel
