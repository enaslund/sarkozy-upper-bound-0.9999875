module

public import Sarkozy.F3Kernel.BitSets
public import Sarkozy.F3Kernel.GraphData

/-!
# The two layouts of a cylinder

The partition proof reads the transposed layout `T`, while the witness proof reads `M`.
Coherent cylinders represent the same present and absent sets in both layouts. Insertion of
a pair preserves this invariant, and the two generated graph masks are coherent.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

@[simp] theorem mem_decT (m : ℕ) (e : Fin 36 × Fin 36) :
    e ∈ decT m ↔ bit m (64 * e.2.val + e.1.val) = true := by
  simp only [decT, mem_filter, mem_univ, true_and, bit_eq_testBit]

theorem posM_injective : Function.Injective (fun e : Fin 36 × Fin 36 =>
    64 * e.1.val + e.2.val) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ he
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  apply Prod.ext <;> apply Fin.ext <;> dsimp at he ⊢ <;> omega

theorem decM_insert (m : ℕ) (e : Fin 36 × Fin 36) :
    decM (Nat.lor m (Nat.shiftLeft 1 (64 * e.1.val + e.2.val))) = insert e (decM m) := by
  ext q
  simp only [mem_decM, bit_lor_bit, Bool.or_eq_true, decide_eq_true_eq, mem_insert]
  have he : 64 * e.1.val + e.2.val = 64 * q.1.val + q.2.val ↔ e = q :=
    posM_injective.eq_iff
  rw [he]
  tauto

theorem decT_insert (m : ℕ) (e : Fin 36 × Fin 36) :
    decT (Nat.lor m (Nat.shiftLeft 1 (64 * e.2.val + e.1.val))) = insert e (decT m) := by
  ext q
  simp only [mem_decT, bit_lor_bit, Bool.or_eq_true, decide_eq_true_eq, mem_insert]
  have he : 64 * e.2.val + e.1.val = 64 * q.2.val + q.1.val ↔ e = q := by
    constructor
    · intro h
      have hs : e.swap = q.swap := posM_injective h
      exact Prod.swap_injective hs
    · rintro rfl
      rfl
  rw [he]
  tauto

def Consts.Coherent (G : Consts) : Prop := decM G.EM = decT G.ET

def Cyl.Coherent (c : Cyl) : Prop := decM c.pm = decT c.pt ∧ decM c.am = decT c.qt

theorem LL20_coherent : LL20.Coherent := by
  ext ⟨i, j⟩
  simp only [mem_decM, mem_decT, GraphData.layouts20]

theorem LL22_coherent : LL22.Coherent := by
  ext ⟨i, j⟩
  simp only [mem_decM, mem_decT, GraphData.layouts22]

def Cyl.present (c : Cyl) (e : Fin 36 × Fin 36) : Cyl :=
  ⟨Nat.lor c.pm (Nat.shiftLeft 1 (64 * e.1.val + e.2.val)), c.am,
    Nat.lor c.pt (Nat.shiftLeft 1 (64 * e.2.val + e.1.val)), c.qt⟩

def Cyl.absent (c : Cyl) (e : Fin 36 × Fin 36) : Cyl :=
  ⟨c.pm, Nat.lor c.am (Nat.shiftLeft 1 (64 * e.1.val + e.2.val)),
    c.pt, Nat.lor c.qt (Nat.shiftLeft 1 (64 * e.2.val + e.1.val))⟩

theorem Cyl.Coherent.present {c : Cyl} (h : c.Coherent) (e : Fin 36 × Fin 36) :
    (c.present e).Coherent := by
  change _ ∧ _
  simp only [Cyl.present, decM_insert, decT_insert, h.1, h.2, and_self]

theorem Cyl.Coherent.absent {c : Cyl} (h : c.Coherent) (e : Fin 36 × Fin 36) :
    (c.absent e).Coherent := by
  change _ ∧ _
  simp only [Cyl.absent, decM_insert, decT_insert, h.1, h.2, and_self]

/-- Masks in layout `T` obey the same finite-set Boolean operations. -/
theorem decT_land (a b : ℕ) : decT (Nat.land a b) = decT a ∩ decT b := by
  ext e
  simp only [mem_decT, ← mem_bits, bits_land, mem_inter]

theorem decT_lor (a b : ℕ) : decT (Nat.lor a b) = decT a ∪ decT b := by
  ext e
  simp only [mem_decT, ← mem_bits, bits_lor, mem_union]

theorem bits_shiftLeft (a p : ℕ) :
    bits (Nat.shiftLeft a p) = (bits a).image (· + p) := by
  change bits (a <<< p) = _
  rw [Nat.shiftLeft_eq, Nat.mul_comm]
  simp only [bits, Nat.bitIndices_two_pow_mul]
  ext i
  simp only [List.mem_toFinset, List.mem_map, mem_image]

theorem bits_two_pow_sub_one (p : ℕ) : bits (2 ^ p - 1) = range p := by
  ext i
  simp only [mem_bits, bit_eq_testBit, Nat.testBit_two_pow_sub_one,
    decide_eq_true_eq, mem_range]

theorem decT_before (G : Consts) (p : ℕ) :
    decT (beforeT G p) = (decT G.ET).filter (fun e => 64 * e.2.val + e.1.val < p) := by
  ext e
  change e ∈ decT (Nat.land G.ET (Nat.shiftLeft 1 p - 1)) ↔ _
  rw [decT_land]
  simp only [mem_inter, mem_filter, mem_decT, ← mem_bits]
  rw [show Nat.shiftLeft 1 p = 2 ^ p by
    change 1 <<< p = 2 ^ p
    rw [Nat.shiftLeft_eq, one_mul], bits_two_pow_sub_one, mem_range]

theorem bit_shifted_LANE0 {x : ℕ} (hx : x < 36) (i j : Fin 36) :
    bit (Nat.shiftLeft LANE0 x) (64 * j.val + i.val) = true ↔ i.val = x := by
  rw [← mem_bits, bits_shiftLeft, bits_LANE0]
  constructor
  · intro h
    obtain ⟨q, hq, he⟩ := mem_image.mp h
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hq
    have hi := i.isLt
    have hj := j.isLt
    simp only [mem_range] at hr
    omega
  · intro he
    exact mem_image.mpr ⟨64 * j.val, mem_image.mpr ⟨j.val, mem_range.mpr j.isLt, rfl⟩,
      by omega⟩

theorem bit_shifted_FULL64 (y : ℕ) (i j : Fin 36) :
    bit (Nat.shiftLeft FULL64 (64 * y)) (64 * j.val + i.val) = true ↔ j.val = y := by
  rw [← mem_bits, bits_shiftLeft, bits_FULL64]
  constructor
  · intro h
    obtain ⟨r, hr, he⟩ := mem_image.mp h
    have hi := i.isLt
    simp only [mem_range] at hr
    omega
  · intro he
    exact mem_image.mpr ⟨i.val, mem_range.mpr (by have := i.isLt; omega), by omega⟩

theorem decT_row (G : Consts) {x : ℕ} (hx : x < 36) :
    decT (rowT G x) = (decT G.ET).filter (fun e => e.1.val = x) := by
  rw [rowT, decT_land]
  ext e
  simp only [mem_inter, mem_filter, mem_decT, bit_shifted_LANE0 hx]

theorem decT_col (G : Consts) (y : ℕ) :
    decT (colT G y) = (decT G.ET).filter (fun e => e.2.val = y) := by
  rw [colT, decT_land]
  ext e
  simp only [mem_inter, mem_filter, mem_decT]
  exact and_congr Iff.rfl (bit_shifted_FULL64 y e.1 e.2)

theorem decT_xor {a b : ℕ} (hsub : decT b ⊆ decT a) :
    decT (Nat.xor a b) = decT a \ decT b := by
  ext e
  have hs : bit b (64 * e.2.val + e.1.val) = true →
      bit a (64 * e.2.val + e.1.val) = true := by
    intro hb
    exact (mem_decT a e).mp (hsub ((mem_decT b e).mpr hb))
  simp only [mem_decT, mem_sdiff, bit_eq_testBit] at hs ⊢
  change (a ^^^ b).testBit (64 * e.2.val + e.1.val) = true ↔ _
  rw [Nat.testBit_xor]
  cases ha : a.testBit (64 * e.2.val + e.1.val) <;>
    cases hb : b.testBit (64 * e.2.val + e.1.val) <;> simp_all

theorem decT_xor_land (a b : ℕ) :
    decT (Nat.xor a (Nat.land a b)) = decT a \ decT b := by
  rw [decT_xor (by rw [decT_land]; exact inter_subset_left), decT_land]
  ext e
  simp only [mem_sdiff, mem_inter]
  tauto

end Sarkozy.F3Kernel
