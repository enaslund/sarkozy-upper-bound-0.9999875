module

public import Sarkozy.F3Kernel.OrderBlocks
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Arithmetic of the checker's count lanes

Counts are encoded as base-`2^64` digits. Bounded digits are recovered exactly by lane
extraction, and the checker's seven-bit signature extraction recovers counts below 128.
The packed witness sums are literal sums of these extracted counts.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem ofDigits_digit {b : ℕ} (hb : 0 < b) (l : List ℕ)
    (hl : ∀ x ∈ l, x < b) (i : ℕ) : Nat.ofDigits b l / b ^ i % b = l.getD i 0 := by
  induction i generalizing l with
  | zero =>
    rw [Nat.pow_zero, Nat.div_one, Nat.ofDigits_mod_eq_head!]
    cases l with
    | nil => simp
    | cons x xs =>
      simp only [List.head!_cons, List.getD_cons_zero]
      exact Nat.mod_eq_of_lt (hl x List.mem_cons_self)
  | succ i ih =>
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.ofDigits_div_eq_ofDigits_tail hb l hl]
    cases l with
    | nil => simp
    | cons x xs =>
      simp only [List.tail_cons, List.getD_cons_succ]
      exact ih xs (fun v hv => hl v (List.mem_cons_of_mem _ hv))

def encodeLanes (l : List ℕ) : ℕ := Nat.ofDigits (2 ^ 64) l

def lane64 (x i : ℕ) : ℕ := x / 2 ^ (64 * i) % 2 ^ 64

theorem lane64_encode (l : List ℕ) (hl : ∀ x ∈ l, x < 2 ^ 64) (i : ℕ) :
    lane64 (encodeLanes l) i = l.getD i 0 := by
  change Nat.ofDigits (2 ^ 64) l / 2 ^ (64 * i) % 2 ^ 64 = _
  rw [pow_mul]
  exact ofDigits_digit (by decide) l hl i

theorem signature_eq_lane_mod (T u : ℕ) : signature T u = lane64 T u % 128 := by
  unfold signature lane64
  change (T >>> (u <<< 6)) &&& (2 ^ 7 - 1) = (T / 2 ^ (64 * u) % 2 ^ 64) % 128
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show 2 ^ 6 = 64 from rfl, Nat.mul_comm u 64,
    Nat.mod_mod_of_dvd _ (by decide : 128 ∣ 2 ^ 64)]

theorem list_getD_lt {b : ℕ} (hb : 0 < b) {l : List ℕ} (hl : ∀ x ∈ l, x < b) (i : ℕ) :
    l.getD i 0 < b := by
  induction l generalizing i with
  | nil => simpa using hb
  | cons x xs ih =>
    cases i with
    | zero => exact hl x List.mem_cons_self
    | succ i => exact ih (fun v hv => hl v (List.mem_cons_of_mem _ hv)) i

theorem signature_encode (l : List ℕ) (hl : ∀ x ∈ l, x < 128) (u : ℕ) :
    signature (encodeLanes l) u = l.getD u 0 := by
  rw [signature_eq_lane_mod, lane64_encode l (fun x hx => by have := hl x hx; omega)]
  exact Nat.mod_eq_of_lt (list_getD_lt (by decide) hl u)

theorem encodeLanes_add {l r : List ℕ} (hlen : l.length = r.length) :
    encodeLanes l + encodeLanes r = encodeLanes (l.zipWith (· + ·) r) :=
  Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq hlen

theorem hSum_eq_list_sum (H n r : ℕ) :
    hSum H n r = ((packedList n r).map (signature H)).sum := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    change signature H (firstVertex r) + hSum H n (Nat.shiftRight r 6) =
      signature H (firstVertex r) + ((packedList n (Nat.shiftRight r 6)).map (signature H)).sum
    rw [ih]

theorem adjSum_eq_list_sum (G : Consts) (n r : ℕ) :
    adjSum G n r = ((packedList n r).map (adj64 G)).sum := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    change adj64 G (firstVertex r) + adjSum G n (Nat.shiftRight r 6) =
      adj64 G (firstVertex r) + ((packedList n (Nat.shiftRight r 6)).map (adj64 G)).sum
    rw [ih]

theorem hSum_encode (l : List ℕ) (hl : ∀ x ∈ l, x < 128) (n r : ℕ) :
    hSum (encodeLanes l) n r = ((packedList n r).map (fun u => l.getD u 0)).sum := by
  rw [hSum_eq_list_sum]
  congr 1
  apply List.map_congr_left
  intro u _
  exact signature_encode l hl u

end Sarkozy.F3Kernel
