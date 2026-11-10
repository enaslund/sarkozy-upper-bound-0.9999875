module

public import Sarkozy.F3Kernel.SwarBytes
public import Sarkozy.F3Kernel.DigitPairs

/-!
# All SWAR stages aggregate byte counts into 64-bit lanes

After the byte stage, three carry-free pairings sum the eight byte populations in each
lane. This proves the actual six-stage implementation, including its repeated masks.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def mergeStep (w mask x : ℕ) : ℕ := (x + (x >>> w)) &&& mask

theorem swar_eq_merge (x : ℕ) : swar x =
    mergeStep 32 MK32 (mergeStep 16 MK16 (mergeStep 8 MK8 (swarByteStage x))) := rfl

theorem MK8_blocks : MK8 = Nat.ofDigits (2 ^ 16) (List.replicate 144 255) := by
  decide +kernel

theorem MK16_blocks : MK16 = Nat.ofDigits (2 ^ 32) (List.replicate 72 65535) := by
  decide +kernel

theorem MK32_blocks : MK32 = Nat.ofDigits (2 ^ 64) (List.replicate 36 4294967295) := by
  decide +kernel

theorem pairSums_le {r : ℕ} (l : List ℕ) (hl : ∀ a ∈ l, a ≤ r) :
    ∀ a ∈ pairBlocks (· + ·) l, a ≤ 2 * r := by
  refine pairBlocks_forall (· + ·) (P := fun a => a ≤ r) (Q := fun a => a ≤ 2 * r)
    (Nat.zero_le _) ?_ l hl
  intro a b ha hb
  omega

theorem mergeStep_digits {w r mask : ℕ} (hr : 2 * r < 2 ^ w) (l : List ℕ)
    (hl : ∀ a ∈ l, a ≤ r)
    (hm : mask = Nat.ofDigits (2 ^ (w + w))
      (List.replicate ((l.length + 1) / 2) (2 ^ w - 1))) :
    mergeStep w mask (Nat.ofDigits (2 ^ w) l) =
      Nat.ofDigits (2 ^ (w + w)) (pairBlocks (· + ·) l) := by
  unfold mergeStep
  rw [Nat.shiftRight_eq_div_pow, hm]
  exact sum_two_digit_blocks hr l hl

def aggregateBytes (l : List ℕ) : List ℕ :=
  pairBlocks (· + ·) (pairBlocks (· + ·) (pairBlocks (· + ·) (l.map byteCount)))

theorem aggregateBytes_length (l : List ℕ) (hl : l.length = 288) :
    (aggregateBytes l).length = 36 := by
  simp only [aggregateBytes, pairBlocks_length, List.length_map, hl]

theorem aggregateBytes_le (l : List ℕ) (hl : ∀ a ∈ l, a < 256) :
    ∀ a ∈ aggregateBytes l, a ≤ 64 := by
  have hb : ∀ a ∈ l.map byteCount, a ≤ 8 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact byteCount_le ⟨v, hl v hv⟩
  exact pairSums_le _ (pairSums_le _ (pairSums_le _ hb))

theorem swar_eq_aggregateBytes (l : List ℕ) (hlen : l.length = 288)
    (hl : ∀ a ∈ l, a < 256) :
    swar (Nat.ofDigits 256 l) = encodeLanes (aggregateBytes l) := by
  have hb : ∀ a ∈ l.map byteCount, a ≤ 8 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact byteCount_le ⟨v, hl v hv⟩
  have hm8 : MK8 = Nat.ofDigits (2 ^ (8 + 8))
      (List.replicate (((l.map byteCount).length + 1) / 2) (2 ^ 8 - 1)) := by
    simp only [List.length_map, hlen]
    convert MK8_blocks using 1
  have hm16 : MK16 = Nat.ofDigits (2 ^ (16 + 16))
      (List.replicate (((pairBlocks (· + ·) (l.map byteCount)).length + 1) / 2)
        (2 ^ 16 - 1)) := by
    simp only [pairBlocks_length, List.length_map, hlen]
    convert MK16_blocks using 1
  have hm32 : MK32 = Nat.ofDigits (2 ^ (32 + 32))
      (List.replicate (((pairBlocks (· + ·) (pairBlocks (· + ·)
        (l.map byteCount))).length + 1) / 2) (2 ^ 32 - 1)) := by
    simp only [pairBlocks_length, List.length_map, hlen]
    convert MK32_blocks using 1
  have h8 := mergeStep_digits (w := 8) (r := 8) (by decide) _ hb hm8
  have h16 := mergeStep_digits (w := 16) (r := 16) (by decide) _ (pairSums_le _ hb) hm16
  have h32 := mergeStep_digits (w := 32) (r := 32) (by decide) _
    (pairSums_le _ (pairSums_le _ hb)) hm32
  norm_num only at h8 h16 h32
  rw [swar_eq_merge, swarByteStage_eq_counts l hlen hl, h8, h16, h32]
  rfl

end Sarkozy.F3Kernel
