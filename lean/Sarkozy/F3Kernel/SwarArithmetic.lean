module

public import Sarkozy.F3Kernel.DigitBlocks

/-!
# Carry-free addition in the parallel population counter

Adding a word to its half-block shift and retaining the lower half of each block adds
the two local counts. Bounds on both half-blocks exclude carries from adjacent blocks.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem ofDigits_map_add (b : ℕ) (f g : ℕ → ℕ) (l : List ℕ) :
    Nat.ofDigits b (l.map f) + Nat.ofDigits b (l.map g) =
      Nat.ofDigits b (l.map (fun a => f a + g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, Nat.ofDigits_cons]
      rw [← ih]
      ring

theorem ofDigits_map_sub (b : ℕ) (f g : ℕ → ℕ) (l : List ℕ)
    (hle : ∀ a ∈ l, g a ≤ f a) :
    Nat.ofDigits b (l.map f) - Nat.ofDigits b (l.map g) =
      Nat.ofDigits b (l.map (fun a => f a - g a)) := by
  have he : Nat.ofDigits b (l.map (fun a => f a - g a)) + Nat.ofDigits b (l.map g) =
      Nat.ofDigits b (l.map f) := by
    rw [ofDigits_map_add]
    apply congrArg (Nat.ofDigits b)
    apply List.map_congr_left
    exact fun a ha => Nat.sub_add_cancel (hle a ha)
  omega

theorem ofDigits_half_mod_le {w r : ℕ} (l : List ℕ)
    (hl : ∀ a ∈ l, a % 2 ^ w ≤ r) : Nat.ofDigits (2 ^ (w + w)) l % 2 ^ w ≤ r := by
  cases l with
  | nil => simp
  | cons a l =>
      rw [Nat.ofDigits_cons, pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left]
      exact hl a List.mem_cons_self

theorem sum_two_halves {w r : ℕ} (hr : 2 * r < 2 ^ w) (l : List ℕ)
    (hl : ∀ a ∈ l, a % 2 ^ w ≤ r ∧ a / 2 ^ w ≤ r) :
    (Nat.ofDigits (2 ^ (w + w)) l + Nat.ofDigits (2 ^ (w + w)) l / 2 ^ w) &&&
        Nat.ofDigits (2 ^ (w + w)) (List.replicate l.length (2 ^ w - 1)) =
      Nat.ofDigits (2 ^ (w + w)) (l.map (fun a => a % 2 ^ w + a / 2 ^ w)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := hl a List.mem_cons_self
      have htail := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      let x := Nat.ofDigits (2 ^ (w + w)) l
      have hx : x % 2 ^ w ≤ r := ofDigits_half_mod_le l (fun u hu => (htail u hu).1)
      have hlow : a % 2 ^ w + a / 2 ^ w < 2 ^ w := by omega
      have hhigh : a / 2 ^ w + x % 2 ^ w < 2 ^ w := by omega
      have hrepr : a + a / 2 ^ w + 2 ^ w * (x % 2 ^ w) =
          (a % 2 ^ w + a / 2 ^ w) + 2 ^ w * (a / 2 ^ w + x % 2 ^ w) := by
        have he := Nat.mod_add_div a (2 ^ w)
        nlinarith
      have hbound : a + a / 2 ^ w + 2 ^ w * (x % 2 ^ w) < 2 ^ (w + w) := by
        rw [hrepr, pow_add]
        calc (a % 2 ^ w + a / 2 ^ w) + 2 ^ w * (a / 2 ^ w + x % 2 ^ w) <
              2 ^ w + 2 ^ w * (a / 2 ^ w + x % 2 ^ w) := Nat.add_lt_add_right hlow _
          _ = 2 ^ w * (a / 2 ^ w + x % 2 ^ w + 1) := by ring
          _ ≤ 2 ^ w * 2 ^ w := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hhigh)
      have hmask : 2 ^ w - 1 < 2 ^ (w + w) :=
        (Nat.sub_lt (Nat.two_pow_pos w) (by decide)).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
      have hsplit : (a + 2 ^ (w + w) * x) + (a + 2 ^ (w + w) * x) / 2 ^ w =
          (a + a / 2 ^ w + 2 ^ w * (x % 2 ^ w)) +
            2 ^ (w + w) * (x + x / 2 ^ w) := by
        rw [shift_low_high (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        ring
      simp only [List.length_cons, List.replicate_succ, List.map_cons, Nat.ofDigits_cons]
      change ((a + 2 ^ (w + w) * x) + (a + 2 ^ (w + w) * x) / 2 ^ w) &&&
          ((2 ^ w - 1) + 2 ^ (w + w) * Nat.ofDigits (2 ^ (w + w))
            (List.replicate l.length (2 ^ w - 1))) = _
      rw [hsplit, and_low_high hbound hmask, Nat.and_two_pow_sub_one_eq_mod,
        hrepr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
      exact congrArg (fun z => a % 2 ^ w + a / 2 ^ w + 2 ^ (w + w) * z) (ih htail)

end Sarkozy.F3Kernel
