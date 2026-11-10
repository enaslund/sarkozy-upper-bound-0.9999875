module

public import Sarkozy.F3Kernel.LaneArithmetic

/-!
# Bitwise operations on bounded base-power digits

These elementary block identities support the proof of the parallel population counter.
They separate bitwise operations from the arithmetic between disjoint digit positions.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem and_low_high {w a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (x y : ℕ) :
    (a + 2 ^ w * x) &&& (b + 2 ^ w * y) = (a &&& b) + 2 ^ w * (x &&& y) := by
  have hap : a / 2 ^ w = 0 := Nat.div_eq_of_lt ha
  have hbp : b / 2 ^ w = 0 := Nat.div_eq_of_lt hb
  have hm := Nat.mod_add_div ((a + 2 ^ w * x) &&& (b + 2 ^ w * y)) (2 ^ w)
  rw [Nat.and_mod_two_pow, Nat.and_div_two_pow] at hm
  simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), hap, hbp, Nat.zero_add] using hm.symm

theorem ofDigits_and {w : ℕ} {l r : List ℕ} (hlen : l.length = r.length)
    (hl : ∀ a ∈ l, a < 2 ^ w) (hr : ∀ b ∈ r, b < 2 ^ w) :
    Nat.ofDigits (2 ^ w) l &&& Nat.ofDigits (2 ^ w) r =
      Nat.ofDigits (2 ^ w) (l.zipWith (· &&& ·) r) := by
  induction l generalizing r with
  | nil => cases r <;> simp_all
  | cons a l ih =>
      cases r with
      | nil => simp at hlen
      | cons b r =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          rw [Nat.ofDigits_cons, Nat.ofDigits_cons,
            and_low_high (hl a List.mem_cons_self) (hr b List.mem_cons_self),
            ih hlen (fun x hx => hl x (List.mem_cons_of_mem _ hx))
              (fun x hx => hr x (List.mem_cons_of_mem _ hx))]
          rfl

theorem ofDigits_le_of_forall2 {b : ℕ} {l r : List ℕ} (h : List.Forall₂ (· ≤ ·) l r) :
    Nat.ofDigits b l ≤ Nat.ofDigits b r := by
  induction h with
  | nil => rfl
  | cons hab _ ih => exact Nat.add_le_add hab (Nat.mul_le_mul_left _ ih)

theorem ofDigits_sub {b : ℕ} {l r : List ℕ} (hlen : l.length = r.length)
    (hle : List.Forall₂ (· ≤ ·) r l) :
    Nat.ofDigits b l - Nat.ofDigits b r = Nat.ofDigits b (l.zipWith (· - ·) r) := by
  induction hle with
  | nil => rfl
  | @cons x y r l hxy htail ih =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      change y + b * Nat.ofDigits b l - (x + b * Nat.ofDigits b r) =
        (y - x) + b * Nat.ofDigits b (l.zipWith (· - ·) r)
      rw [← ih hlen, Nat.mul_sub_left_distrib]
      have he := Nat.mul_le_mul_left b (ofDigits_le_of_forall2 (b := b) htail)
      omega

theorem shift_low_high {w s a : ℕ} (hs : s ≤ w) (x : ℕ) :
    (a + 2 ^ w * x) / 2 ^ s =
      (a / 2 ^ s + 2 ^ (w - s) * (x % 2 ^ s)) + 2 ^ w * (x / 2 ^ s) := by
  have hp : 2 ^ w = 2 ^ s * 2 ^ (w - s) := by rw [← pow_add, Nat.add_sub_cancel' hs]
  calc (a + 2 ^ w * x) / 2 ^ s = a / 2 ^ s + 2 ^ (w - s) * x := by
        rw [hp, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
    _ = _ := by
        conv_lhs => arg 2; arg 2; rw [← Nat.mod_add_div x (2 ^ s)]
        rw [hp]
        ring

theorem shift_low_lt {w s a : ℕ} (hs : s ≤ w) (ha : a < 2 ^ w) (x : ℕ) :
    a / 2 ^ s + 2 ^ (w - s) * (x % 2 ^ s) < 2 ^ w := by
  have hp : 2 ^ w = 2 ^ (w - s) * 2 ^ s := by rw [← pow_add, Nat.sub_add_cancel hs]
  have ha' : a / 2 ^ s < 2 ^ (w - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← hp]
    exact ha
  have hx := Nat.mod_lt x (Nat.two_pow_pos s)
  rw [hp]
  calc a / 2 ^ s + 2 ^ (w - s) * (x % 2 ^ s) <
        2 ^ (w - s) + 2 ^ (w - s) * (x % 2 ^ s) := Nat.add_lt_add_right ha' _
    _ = 2 ^ (w - s) * (x % 2 ^ s + 1) := by ring
    _ ≤ 2 ^ (w - s) * 2 ^ s := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hx)

theorem shifted_low_and {w s a m : ℕ} (hs : s ≤ w) (ha : a < 2 ^ w)
    (hm : m < 2 ^ (w - s)) (x : ℕ) :
    (a / 2 ^ s + 2 ^ (w - s) * x) &&& m = (a / 2 ^ s) &&& m := by
  have ha' : a / 2 ^ s < 2 ^ (w - s) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel hs]
    exact ha
  have he := and_low_high ha' hm x 0
  simpa using he

theorem ofDigits_shift_and_replicate {w s m : ℕ} (hs : s ≤ w)
    (hm : m < 2 ^ (w - s)) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ w) :
    (Nat.ofDigits (2 ^ w) l / 2 ^ s) &&&
        Nat.ofDigits (2 ^ w) (List.replicate l.length m) =
      Nat.ofDigits (2 ^ w) (l.map (fun a => (a / 2 ^ s) &&& m)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hl a List.mem_cons_self
      have htail := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      have hm' : m < 2 ^ w := hm.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
      simp only [List.length_cons, List.replicate_succ, List.map_cons, Nat.ofDigits_cons]
      rw [shift_low_high hs, and_low_high (shift_low_lt hs ha _) hm',
        shifted_low_and hs ha hm, ih htail]

end Sarkozy.F3Kernel
