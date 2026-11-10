module

public import Sarkozy.F3Kernel.SwarArithmetic

/-!
# The first three SWAR stages count each byte

The local eight-bit arithmetic is checked exhaustively by kernel reduction. The block
lemmas lift those 256 cases to the full 2304-bit word without trusting machine arithmetic.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def byteOne (a : ℕ) : ℕ := a - ((a / 2) &&& 85)
def byteTwo (a : ℕ) : ℕ := (byteOne a &&& 51) + ((byteOne a / 4) &&& 51)
def byteCount (a : ℕ) : ℕ := (bits a).card

theorem byteOne_le (a : ℕ) : byteOne a ≤ a := Nat.sub_le _ _

theorem byteTwo_sound : ∀ a : Fin 256,
    byteTwo a % 16 ≤ 4 ∧ byteTwo a / 16 ≤ 4 ∧
      byteTwo a % 16 + byteTwo a / 16 = byteCount a := by decide +kernel

theorem byteCount_le : ∀ a : Fin 256, byteCount a ≤ 8 := by decide +kernel

theorem MK1_bytes : MK1 = Nat.ofDigits 256 (List.replicate 288 85) := by decide +kernel
theorem MK2_bytes : MK2 = Nat.ofDigits 256 (List.replicate 288 51) := by decide +kernel
theorem MK4_bytes : MK4 = Nat.ofDigits 256 (List.replicate 288 15) := by decide +kernel

def swarByteStage (x : ℕ) : ℕ :=
  let x1 := x - ((x >>> 1) &&& MK1)
  let x2 := (x1 &&& MK2) + ((x1 >>> 2) &&& MK2)
  (x2 + (x2 >>> 4)) &&& MK4

theorem swar_first (l : List ℕ) (hlen : l.length = 288) (hl : ∀ a ∈ l, a < 256) :
    Nat.ofDigits 256 l - ((Nat.ofDigits 256 l >>> 1) &&& MK1) =
      Nat.ofDigits 256 (l.map byteOne) := by
  have hm := ofDigits_shift_and_replicate (w := 8) (s := 1) (m := 85)
    (by decide) (by decide) l hl
  norm_num only at hm
  rw [MK1_bytes, ← hlen, Nat.shiftRight_eq_div_pow]
  change Nat.ofDigits 256 l - (Nat.ofDigits 256 l / 2 &&&
    Nat.ofDigits 256 (List.replicate l.length 85)) = _
  rw [hm]
  have he := ofDigits_map_sub 256 id (fun a => (a / 2) &&& 85) l
    (fun a _ => Nat.and_le_left.trans (Nat.div_le_self _ _))
  unfold byteOne
  simpa only [List.map_id, id_eq] using he

theorem swar_second (l : List ℕ) (hlen : l.length = 288) (hl : ∀ a ∈ l, a < 256) :
    (Nat.ofDigits 256 (l.map byteOne) &&& MK2) +
        ((Nat.ofDigits 256 (l.map byteOne) >>> 2) &&& MK2) =
      Nat.ofDigits 256 (l.map byteTwo) := by
  have h1 : ∀ a ∈ l.map byteOne, a < 256 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact (byteOne_le v).trans_lt (hl v hv)
  have hm : MK2 = Nat.ofDigits 256 (List.replicate (l.map byteOne).length 51) := by
    rw [List.length_map, hlen, MK2_bytes]
  have hz := ofDigits_shift_and_replicate (w := 8) (s := 0) (m := 51)
    (by decide) (by decide) (l.map byteOne) h1
  have hs := ofDigits_shift_and_replicate (w := 8) (s := 2) (m := 51)
    (by decide) (by decide) (l.map byteOne) h1
  norm_num only at hz hs
  simp only [Nat.div_one] at hz
  rw [hm, hz, Nat.shiftRight_eq_div_pow]
  change _ + (Nat.ofDigits 256 (l.map byteOne) / 4 &&&
    Nat.ofDigits 256 (List.replicate (l.map byteOne).length 51)) = _
  rw [hs, ofDigits_map_add]
  unfold byteTwo
  simp only [List.map_map, Function.comp_def]

theorem swarByteStage_eq_counts (l : List ℕ) (hlen : l.length = 288)
    (hl : ∀ a ∈ l, a < 256) :
    swarByteStage (Nat.ofDigits 256 l) = Nat.ofDigits 256 (l.map byteCount) := by
  simp only [swarByteStage, swar_first l hlen hl, swar_second l hlen hl]
  rw [MK4_bytes, ← hlen,
    ← List.length_map (f := byteTwo), Nat.shiftRight_eq_div_pow]
  have hb : ∀ a ∈ l.map byteTwo, a % 16 ≤ 4 ∧ a / 16 ≤ 4 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact ⟨(byteTwo_sound ⟨v, hl v hv⟩).1, (byteTwo_sound ⟨v, hl v hv⟩).2.1⟩
  have he := sum_two_halves (w := 4) (r := 4) (by decide) _ hb
  norm_num only at he
  change (Nat.ofDigits 256 (l.map byteTwo) + Nat.ofDigits 256 (l.map byteTwo) / 16) &&&
    Nat.ofDigits 256 (List.replicate (l.map byteTwo).length 15) = _
  rw [he]
  apply congrArg (Nat.ofDigits 256)
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  exact (byteTwo_sound ⟨a, hl a ha⟩).2.2

end Sarkozy.F3Kernel
