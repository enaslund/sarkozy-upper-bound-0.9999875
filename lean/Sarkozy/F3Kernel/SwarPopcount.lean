module

public import Sarkozy.F3Kernel.SwarLanes
public import Sarkozy.F3Kernel.MaskLayouts

/-!
# The SWAR result is the population count of each original lane

Recombining byte digits preserves the original integer and adds their disjoint bit
populations. Uniqueness of bounded digits then identifies the output for arbitrary
36-lane inputs with the encoded list of mathematical bit cardinalities.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

@[simp] theorem byteCount_zero : byteCount 0 = 0 := by decide +kernel

theorem byteCount_low_high {w a : ℕ} (ha : a < 2 ^ w) (b : ℕ) :
    byteCount (a + 2 ^ w * b) = byteCount a + byteCount b := by
  have hb : bits (2 ^ w * b) = (bits b).image (· + w) := by
    have he := bits_shiftLeft b w
    change bits (b <<< w) = _ at he
    rw [Nat.shiftLeft_eq, Nat.mul_comm] at he
    exact he
  have hd : Disjoint ((bits b).image (· + w)) (bits a) := by
    rw [disjoint_left]
    intro i hi hai
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    have := bit_lt_of_mem ha hai
    omega
  unfold byteCount
  rw [Nat.add_comm, Nat.two_pow_add_eq_or_of_lt ha]
  change (bits (Nat.lor (2 ^ w * b) a)).card = _
  rw [bits_lor, hb, card_union_of_disjoint hd,
    card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]
  exact Nat.add_comm _ _

theorem pairBlocks_popcount {w : ℕ} (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) :
    (pairBlocks (fun a b => a + 2 ^ w * b) l).map byteCount =
      pairBlocks (· + ·) (l.map byteCount) := by
  induction l using pairBlocks.induct with
  | case1 => rfl
  | case2 a => simp [pairBlocks]
  | case3 a b l ih =>
      simp only [pairBlocks, List.map_cons, byteCount_low_high (hl a List.mem_cons_self)]
      rw [ih (fun u hu => hl u (by simp [hu]))]

def groupBytes (l : List ℕ) : List ℕ :=
  pairBlocks (fun a b => a + 2 ^ 32 * b)
    (pairBlocks (fun a b => a + 2 ^ 16 * b) (pairBlocks (fun a b => a + 256 * b) l))

theorem groupBytes_length (l : List ℕ) (hl : l.length = 288) :
    (groupBytes l).length = 36 := by
  simp only [groupBytes, pairBlocks_length, hl]

theorem groupBytes_bounds (l : List ℕ) (hl : ∀ a ∈ l, a < 256) :
    ∀ a ∈ groupBytes l, a < 2 ^ 64 := by
  have h1 := pairDigits_lt (by decide : 0 < 256) l hl
  have h2 := pairDigits_lt (by decide : 0 < 2 ^ 16) _ h1
  have h3 := pairDigits_lt (by decide : 0 < 2 ^ 32) _ h2
  exact h3

theorem groupBytes_encode (l : List ℕ) : encodeLanes (groupBytes l) = Nat.ofDigits 256 l := by
  unfold encodeLanes groupBytes
  have h1 := ofDigits_pairBlocks 256 l
  have h2 := ofDigits_pairBlocks (2 ^ 16) (pairBlocks (fun a b => a + 256 * b) l)
  have h3 := ofDigits_pairBlocks (2 ^ 32)
    (pairBlocks (fun a b => a + 2 ^ 16 * b) (pairBlocks (fun a b => a + 256 * b) l))
  exact h3.symm.trans (h2.symm.trans h1.symm)

theorem aggregateBytes_eq_popcounts (l : List ℕ) (hl : ∀ a ∈ l, a < 256) :
    aggregateBytes l = (groupBytes l).map byteCount := by
  have h1 := pairDigits_lt (by decide : 0 < 256) l hl
  have h2 := pairDigits_lt (by decide : 0 < 2 ^ 16) _ h1
  unfold aggregateBytes groupBytes
  rw [pairBlocks_popcount _ h2, pairBlocks_popcount _ h1]
  have he := pairBlocks_popcount (w := 8) l hl
  change (pairBlocks (fun a b => a + 256 * b) l).map byteCount = _ at he
  rw [he]

set_option exponentiation.threshold 4096 in
theorem swar_encodeLanes (l : List ℕ) (hlen : l.length = 36)
    (hl : ∀ a ∈ l, a < 2 ^ 64) :
    swar (encodeLanes l) = encodeLanes (l.map byteCount) := by
  let bs := Nat.digitsAppend 256 288 (encodeLanes l)
  have hx : encodeLanes l < 256 ^ 288 := by
    have he : (2 ^ 64 : ℕ) ^ 36 = 256 ^ 288 := by
      change (2 ^ 64 : ℕ) ^ 36 = (2 ^ 8) ^ 288
      rw [← pow_mul, ← pow_mul]
    rw [← he, ← hlen]
    exact Nat.ofDigits_lt_base_pow_length (by decide) hl
  have hbslen : bs.length = 288 := Nat.length_digitsAppend (by decide) _ hx
  have hbs : ∀ a ∈ bs, a < 256 := fun a ha => Nat.lt_of_mem_digitsAppend (by decide) _ a ha
  have hencode : Nat.ofDigits 256 bs = encodeLanes l := by
    exact (Nat.setInvOn_digitsAppend_ofDigits (by decide : 1 < 256) 288).2 hx
  have hgroup : groupBytes bs = l := by
    apply Nat.ofDigits_inj_of_len_eq (by decide : 1 < 2 ^ 64)
    · rw [groupBytes_length bs hbslen, hlen]
    · exact groupBytes_bounds bs hbs
    · exact hl
    · exact (groupBytes_encode bs).trans hencode
  rw [← hencode, swar_eq_aggregateBytes bs hbslen hbs,
    aggregateBytes_eq_popcounts bs hbs, hgroup]

end Sarkozy.F3Kernel
