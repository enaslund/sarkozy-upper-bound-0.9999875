module

public import Sarkozy.F3Kernel.PackedList
public import Mathlib.Combinatorics.Colex

/-!
# Natural-number masks as finite sets of bit positions

The arithmetic bit-spreading operation in the checker is multiplication without carries:
the summand positions are distinct. This interface proves that property before interpreting
the result as a set, so no finite enumeration of the `2^36` possible vertex masks is needed.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

def bits (n : ℕ) : Finset ℕ := n.bitIndices.toFinset

def pack (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i

@[simp] theorem mem_bits (i n : ℕ) : i ∈ bits n ↔ bit n i = true := by
  simp only [bits, List.mem_toFinset, Nat.mem_bitIndices, bit_eq_testBit]

@[simp] theorem bits_pack (s : Finset ℕ) : bits (pack s) = s :=
  toFinset_bitIndices_sum_two_pow s

@[simp] theorem pack_bits (n : ℕ) : pack (bits n) = n :=
  sum_toFinset_bitIndices_two_pow n

theorem bits_land (a b : ℕ) : bits (Nat.land a b) = bits a ∩ bits b := by
  ext i
  simp only [mem_bits, mem_inter, bit_eq_testBit]
  change (a &&& b).testBit i = true ↔ _
  simp only [Nat.testBit_and, Bool.and_eq_true]

theorem bits_lor (a b : ℕ) : bits (Nat.lor a b) = bits a ∪ bits b := by
  ext i
  simp only [mem_bits, mem_union, bit_eq_testBit]
  change (a ||| b).testBit i = true ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]

theorem bit_lt_of_mem {a i n : ℕ} (ha : a < 2 ^ n) (hi : i ∈ bits a) : i < n := by
  by_contra hn
  have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
  have hb := Nat.testBit_lt_two_pow (ha.trans_le hp)
  have ht : a.testBit i = true := by simpa only [mem_bits, bit_eq_testBit] using hi
  rw [ht] at hb
  cases hb

/-- Multiplication is a carry-free convolution when the sums of bit positions are distinct. -/
theorem bits_mul {a b : ℕ}
    (hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (↑(bits a ×ˢ bits b))) :
    bits (a * b) = (bits a ×ˢ bits b).image (fun p => p.1 + p.2) := by
  have he : a * b = pack ((bits a ×ˢ bits b).image fun p => p.1 + p.2) := by
    unfold pack
    rw [sum_image hinj]
    simp only [pow_add, sum_product]
    simp_rw [← mul_sum]
    rw [← sum_mul]
    change a * b = pack (bits a) * pack (bits b)
    rw [pack_bits, pack_bits]
  rw [he, bits_pack]

theorem bits_LANE0 : bits LANE0 = (range 36).image (64 * ·) := by
  have he : LANE0 = pack ((range 36).image (64 * ·)) := by decide +kernel
  rw [he, bits_pack]

theorem bits_REP63 : bits REP63 = (range 36).image (63 * ·) := by
  have he : REP63 = pack ((range 36).image (63 * ·)) := by decide +kernel
  rw [he, bits_pack]

/-- Spread a 36-bit vertex mask to the lowest bit of each 64-bit lane. -/
def spread (v : ℕ) : ℕ := Nat.land (v * REP63) LANE0

theorem bits_spread {v : ℕ} (hv : v < 2 ^ 36) :
    bits (spread v) = (bits v).image (64 * ·) := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (↑(bits v ×ˢ bits REP63)) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    obtain ⟨hc, hd⟩ := mem_product.mp hcd
    rw [bits_REP63] at hb hd
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hb
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
    have ha' := bit_lt_of_mem hv ha
    have hc' := bit_lt_of_mem hv hc
    simp only [mem_range] at hi hj
    apply Prod.ext <;> dsimp at he ⊢ <;> omega
  rw [spread, bits_land, bits_mul hinj, bits_LANE0, bits_REP63]
  ext p
  constructor
  · rintro hp
    obtain ⟨hs, ht⟩ := mem_inter.mp hp
    obtain ⟨⟨a, b⟩, hab, hp⟩ := mem_image.mp hs
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hb
    obtain ⟨i, hi, hip⟩ := mem_image.mp ht
    have ha' := bit_lt_of_mem hv ha
    simp only [mem_range] at hi hj
    have hai : a = i := by dsimp at hp; omega
    exact mem_image.mpr ⟨a, ha, by omega⟩
  · intro hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    have hi' := bit_lt_of_mem hv hi
    refine mem_inter.mpr ⟨?_, mem_image.mpr ⟨i, mem_range.mpr hi', rfl⟩⟩
    refine mem_image.mpr ⟨(i, 63 * i), mem_product.mpr
      ⟨hi, mem_image.mpr ⟨i, mem_range.mpr hi', rfl⟩⟩, ?_⟩
    dsimp
    omega

/-- Multiplying a spread vertex mask by a single-lane mask forms their rectangle. -/
theorem bit_spread_mul {v w : ℕ} (hv : v < 2 ^ 36) (hw : w < 2 ^ 64)
    (i j : ℕ) (_hi : i < 36) (hj : j < 64) :
    bit (spread v * w) (64 * i + j) = true ↔ bit v i = true ∧ bit w j = true := by
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (↑(bits (spread v) ×ˢ bits w)) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    obtain ⟨hc, hd⟩ := mem_product.mp hcd
    rw [bits_spread hv] at ha hc
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
    obtain ⟨c', hc', rfl⟩ := mem_image.mp hc
    have hb' := bit_lt_of_mem hw hb
    have hd' := bit_lt_of_mem hw hd
    apply Prod.ext <;> dsimp at he ⊢ <;> omega
  rw [← mem_bits, bits_mul hinj, bits_spread hv, ← mem_bits, ← mem_bits]
  constructor
  · intro hp
    obtain ⟨⟨a, b⟩, hab, he⟩ := mem_image.mp hp
    obtain ⟨ha, hb⟩ := mem_product.mp hab
    obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
    have hb' := bit_lt_of_mem hw hb
    have hai : a' = i := by dsimp at he; omega
    have hbj : b = j := by dsimp at he; omega
    exact ⟨hai ▸ ha', hbj ▸ hb⟩
  · rintro ⟨hvi, hwj⟩
    exact mem_image.mpr ⟨(64 * i, j), mem_product.mpr
      ⟨mem_image.mpr ⟨i, hvi, rfl⟩, hwj⟩, rfl⟩

/-- Vertex-mask decoding. -/
def decV (m : ℕ) : Finset (Fin 36) := univ.filter fun v => bit m v = true

/-- Row-major pair-mask decoding, the `M` layout used by witness and cover checks. -/
def decM (m : ℕ) : Finset (Fin 36 × Fin 36) :=
  univ.filter fun e => bit m (64 * e.1.val + e.2.val) = true

@[simp] theorem mem_decV (m : ℕ) (v : Fin 36) : v ∈ decV m ↔ bit m v = true := by
  simp only [decV, mem_filter, mem_univ, true_and]

@[simp] theorem mem_decM (m : ℕ) (e : Fin 36 × Fin 36) :
    e ∈ decM m ↔ bit m (64 * e.1.val + e.2.val) = true := by
  simp only [decM, mem_filter, mem_univ, true_and]

theorem decM_land (a b : ℕ) : decM (Nat.land a b) = decM a ∩ decM b := by
  ext e
  simp only [mem_decM, ← mem_bits, bits_land, mem_inter]

theorem decM_lor (a b : ℕ) : decM (Nat.lor a b) = decM a ∪ decM b := by
  ext e
  simp only [mem_decM, ← mem_bits, bits_lor, mem_union]

@[simp] theorem decM_zero : decM 0 = ∅ := by
  ext e
  simp only [mem_decM, bit_eq_testBit, Nat.zero_testBit, Bool.false_eq_true, notMem_empty]

theorem decM_spread_mul {v w : ℕ} (hv : v < 2 ^ 36) (hw : w < 2 ^ 64) :
    decM (spread v * w) = decV v ×ˢ decV w := by
  ext e
  simp only [mem_decM, mem_product, mem_decV]
  exact bit_spread_mul hv hw e.1 e.2 e.1.isLt (by have := e.2.isLt; omega)

theorem bits_FULL64 : bits FULL64 = range 64 := by
  have he : FULL64 = pack (range 64) := by decide +kernel
  rw [he, bits_pack]

theorem decV_FULL64 : decV FULL64 = univ := by
  ext v
  simp only [mem_decV, ← mem_bits, bits_FULL64, mem_range, mem_univ, iff_true]
  have := v.isLt
  omega

/-- A vertex mask's cover rows occupy precisely the selected rows in the `M` layout. -/
theorem decM_cover_rows {v : ℕ} (hv : v < 2 ^ 36) :
    decM (spread v * FULL64) = decV v ×ˢ univ := by
  rw [decM_spread_mul hv (by decide +kernel), decV_FULL64]

theorem bits_FULL36 : bits FULL36 = range 36 := by
  have he : FULL36 = pack (range 36) := by decide +kernel
  rw [he, bits_pack]

theorem spread_FULL36 : spread FULL36 = LANE0 := by
  have he : bits (spread FULL36) = bits LANE0 := by
    rw [bits_spread (by decide +kernel), bits_FULL36, bits_LANE0]
  simpa only [pack_bits] using congrArg pack he

theorem decV_FULL36 : decV FULL36 = univ := by
  ext v
  simp only [mem_decV, ← mem_bits, bits_FULL36, mem_range, mem_univ, iff_true]
  exact v.isLt

/-- Cover columns in the `M` layout. -/
theorem decM_cover_cols {v : ℕ} (hv : v < 2 ^ 64) :
    decM (v * LANE0) = univ ×ˢ decV v := by
  rw [Nat.mul_comm, ← spread_FULL36,
    decM_spread_mul (by decide +kernel) hv, decV_FULL36]

theorem land_FULL36_lt (x : ℕ) : Nat.land x FULL36 < 2 ^ 36 := by
  change x &&& (2 ^ 36 - 1) < 2 ^ 36
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem vmask_zero_lt {n l out : ℕ} (h : vmask n l 0 = some out) : out < 2 ^ 36 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hnot : i ∉ packedList n l := fun hin => by
    have := ((vmask_sound h).2.1 i hin).1
    omega
  have hb := vmask_zero_bit h i
  simpa only [bit_eq_testBit, hnot, decide_false] using hb

theorem decV_land (a b : ℕ) : decV (Nat.land a b) = decV a ∩ decV b := by
  ext v
  simp only [mem_decV, ← mem_bits, bits_land, mem_inter]

@[simp] theorem decV_zero : decV 0 = ∅ := by
  ext v
  simp only [mem_decV, bit_eq_testBit, Nat.zero_testBit, Bool.false_eq_true, notMem_empty]

theorem decV_disjoint {a b : ℕ} (h : Nat.land a b = 0) : Disjoint (decV a) (decV b) := by
  rw [disjoint_iff_inter_eq_empty, ← decV_land, h, decV_zero]

theorem decM_disjoint {a b : ℕ} (h : Nat.land a b = 0) : Disjoint (decM a) (decM b) := by
  rw [disjoint_iff_inter_eq_empty, ← decM_land, h, decM_zero]

theorem decM_subset {a b : ℕ} (h : Nat.land a b = a) : decM a ⊆ decM b := by
  have he : decM a ∩ decM b = decM a := by rw [← decM_land, h]
  exact inter_eq_left.mp he

/-- For a submask, XOR is set difference on decoded pairs. -/
theorem decM_xor {a b : ℕ} (hsub : decM b ⊆ decM a) :
    decM (Nat.xor a b) = decM a \ decM b := by
  ext e
  have hs : bit b (64 * e.1.val + e.2.val) = true →
      bit a (64 * e.1.val + e.2.val) = true := by
    intro hb
    exact (mem_decM a e).mp (hsub ((mem_decM b e).mpr hb))
  simp only [mem_decM, mem_sdiff, bit_eq_testBit] at hs ⊢
  change (a ^^^ b).testBit (64 * e.1.val + e.2.val) = true ↔ _
  rw [Nat.testBit_xor]
  cases ha : a.testBit (64 * e.1.val + e.2.val) <;>
    cases hb : b.testBit (64 * e.1.val + e.2.val) <;> simp_all

end Sarkozy.F3Kernel
