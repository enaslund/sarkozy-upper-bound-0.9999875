module

public import Sarkozy.F3Kernel.SwarPopcount
public import Sarkozy.F3Kernel.FreeDegrees

/-!
# Recovering graph degrees from the SWAR lanes

A well-formed matrix word has bits only at the 36-by-36 positions used by the checker.
Its lane populations are therefore exactly the row degrees of `decM`, or the column
degrees of `decT`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.ExtractionK

def MatrixWord (m : ℕ) : Prop :=
  ∀ p, m.testBit p = true → p % 64 < 36 ∧ p / 64 < 36

theorem MatrixWord.lt {m : ℕ} (h : MatrixWord m) : m < 2 ^ 2304 := by
  by_contra hn
  obtain ⟨p, hp, hb⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (Nat.le_of_not_gt hn)
  have := h p hb
  omega

theorem swar_packCounts (f : Fin 36 → ℕ) (hf : ∀ v, f v < 2 ^ 64) :
    swar (packCounts f) = packCounts (fun v => byteCount (f v)) := by
  rw [← encodeLanes_ofFn, swar_encodeLanes _ List.length_ofFn]
  · rw [List.map_ofFn, encodeLanes_ofFn]
    rfl
  · simpa only [List.forall_mem_ofFn_iff] using hf

theorem lane64_lt (x i : ℕ) : lane64 x i < 2 ^ 64 := Nat.mod_lt _ (by decide)

set_option exponentiation.threshold 4096 in
theorem packCounts_lane64 {x : ℕ} (hx : x < 2 ^ 2304) :
    packCounts (fun i : Fin 36 => lane64 x i) = x := by
  let l := Nat.digitsAppend (2 ^ 64) 36 x
  have hx' : x < (2 ^ 64) ^ 36 := by rwa [← pow_mul]
  have hlen : l.length = 36 := Nat.length_digitsAppend (by decide) _ hx'
  have hl : ∀ a ∈ l, a < 2 ^ 64 := fun a ha => Nat.lt_of_mem_digitsAppend (by decide) _ a ha
  have he : encodeLanes l = x := (Nat.setInvOn_digitsAppend_ofDigits
    (by decide : 1 < 2 ^ 64) 36).2 hx'
  have hd : List.ofFn (fun i : Fin 36 => lane64 x i) = l := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi hj
      rw [List.getElem_ofFn, ← he, lane64_encode l hl]
      simp [List.getD_eq_getElem?_getD, hj]
  rw [← encodeLanes_ofFn, hd, he]

theorem bit_lane64 (x u i : ℕ) :
    bit (lane64 x u) i = (decide (i < 64) && bit x (64 * u + i)) := by
  simp only [bit_eq_testBit, lane64, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rw [Nat.add_comm i (64 * u)]

theorem MatrixWord.lane_bits {m : ℕ} (hm : MatrixWord m) (u : Fin 36) :
    bits (lane64 m u) = (univ.filter (fun v : Fin 36 => (u, v) ∈ decM m)).image Fin.val := by
  ext i
  rw [mem_bits, bit_lane64, Bool.and_eq_true, decide_eq_true_eq, mem_image]
  constructor
  · rintro ⟨hi, hb⟩
    have ht := hm (64 * u.val + i) (by rwa [← bit_eq_testBit])
    have hi36 : i < 36 := by omega
    refine ⟨⟨i, hi36⟩, ?_, rfl⟩
    simpa only [mem_filter, mem_univ, true_and, mem_decM] using hb
  · rintro ⟨v, hv, rfl⟩
    refine ⟨by have := v.isLt; omega, ?_⟩
    simpa only [mem_filter, mem_univ, true_and, mem_decM] using hv

theorem MatrixWord.lane_count {m : ℕ} (hm : MatrixWord m) (u : Fin 36) :
    byteCount (lane64 m u) = cmpHx (decM m) u := by
  rw [byteCount, hm.lane_bits, card_image_of_injective _ Fin.val_injective]
  rfl

theorem MatrixWord.swar_rows {m : ℕ} (hm : MatrixWord m) :
    swar m = packCounts (cmpHx (decM m)) := by
  have he := swar_packCounts (fun i : Fin 36 => lane64 m i) (fun i => lane64_lt m i)
  rw [packCounts_lane64 hm.lt] at he
  rw [he]
  exact congrArg packCounts (funext hm.lane_count)

theorem MatrixWord.swar_cols {m : ℕ} (hm : MatrixWord m) :
    swar m = packCounts (cmpHz (decT m)) := by
  rw [hm.swar_rows]
  apply congrArg packCounts
  funext u
  unfold cmpHx cmpHz
  apply congrArg Finset.card
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_decM, mem_decT]

end Sarkozy.F3Kernel
