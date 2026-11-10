module

public import Sarkozy.F3Kernel.SwarArithmetic

/-!
# Pairing digits without changing their encoded value

The SWAR aggregation stages group consecutive digits into twice-wide blocks, then sum
their two halves. A final unmatched digit is padded by zero.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def pairBlocks (f : ℕ → ℕ → ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [f a 0]
  | a :: b :: l => f a b :: pairBlocks f l

theorem pairBlocks_length (f : ℕ → ℕ → ℕ) (l : List ℕ) :
    (pairBlocks f l).length = (l.length + 1) / 2 := by
  induction l using pairBlocks.induct with
  | case1 => rfl
  | case2 a => simp [pairBlocks]
  | case3 a b l ih => simp only [pairBlocks, List.length_cons, ih]; omega

theorem pairBlocks_forall (f : ℕ → ℕ → ℕ) {P Q : ℕ → Prop}
    (hzero : P 0) (hf : ∀ a b, P a → P b → Q (f a b))
    (l : List ℕ) (hl : ∀ a ∈ l, P a) : ∀ a ∈ pairBlocks f l, Q a := by
  induction l using pairBlocks.induct with
  | case1 => simp [pairBlocks]
  | case2 a =>
      simpa only [pairBlocks, List.mem_singleton, forall_eq] using
        hf a 0 (hl a List.mem_cons_self) hzero
  | case3 a b l ih =>
      simp only [pairBlocks, List.mem_cons, forall_eq_or_imp]
      exact ⟨hf a b (hl a List.mem_cons_self) (hl b (by simp)),
        ih (fun u hu => hl u (by simp [hu]))⟩

theorem pairBlocks_map (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (l : List ℕ) :
    (pairBlocks f l).map g = pairBlocks (fun a b => g (f a b)) l := by
  induction l using pairBlocks.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b l ih => simp only [pairBlocks, List.map_cons, ih]

theorem ofDigits_pairBlocks (b : ℕ) (l : List ℕ) :
    Nat.ofDigits b l = Nat.ofDigits (b * b) (pairBlocks (fun a c => a + b * c) l) := by
  induction l using pairBlocks.induct with
  | case1 => rfl
  | case2 a => simp [pairBlocks]
  | case3 a c l ih =>
      simp only [pairBlocks, Nat.ofDigits_cons, ← ih]
      ring

theorem pairDigits_halves {b r : ℕ} (hb : r < b) (l : List ℕ)
    (hl : ∀ a ∈ l, a ≤ r) :
    ∀ a ∈ pairBlocks (fun x y => x + b * y) l, a % b ≤ r ∧ a / b ≤ r := by
  refine pairBlocks_forall (fun x y => x + b * y) (P := fun a => a ≤ r)
    (Q := fun a => a % b ≤ r ∧ a / b ≤ r) (Nat.zero_le r) ?_ l hl
  intro a c ha hc
  have hab : a < b := ha.trans_lt hb
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hab,
    Nat.add_mul_div_left _ _ (lt_of_le_of_lt (Nat.zero_le r) hb),
    Nat.div_eq_of_lt hab, Nat.zero_add]
  exact ⟨ha, hc⟩

theorem pairDigits_sums {b : ℕ} (hb : 0 < b) (l : List ℕ) (hl : ∀ a ∈ l, a < b) :
    (pairBlocks (fun x y => x + b * y) l).map (fun a => a % b + a / b) =
      pairBlocks (· + ·) l := by
  induction l using pairBlocks.induct with
  | case1 => rfl
  | case2 a =>
      simp [pairBlocks, Nat.mod_eq_of_lt (hl a List.mem_cons_self),
        Nat.div_eq_of_lt (hl a List.mem_cons_self)]
  | case3 a c l ih =>
      have ha := hl a List.mem_cons_self
      simp only [pairBlocks, List.map_cons, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt ha, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, Nat.zero_add]
      rw [ih (fun u hu => hl u (by simp [hu]))]

theorem sum_two_digit_blocks {w r : ℕ} (hr : 2 * r < 2 ^ w) (l : List ℕ)
    (hl : ∀ a ∈ l, a ≤ r) :
    (Nat.ofDigits (2 ^ w) l + Nat.ofDigits (2 ^ w) l / 2 ^ w) &&&
        Nat.ofDigits (2 ^ (w + w)) (List.replicate ((l.length + 1) / 2) (2 ^ w - 1)) =
      Nat.ofDigits (2 ^ (w + w)) (pairBlocks (· + ·) l) := by
  have hb : r < 2 ^ w := by omega
  have hd := pairDigits_halves hb l hl
  have he := sum_two_halves hr _ hd
  rw [pairBlocks_length, pairDigits_sums (Nat.two_pow_pos _) l
    (fun a ha => (hl a ha).trans_lt hb)] at he
  rw [show 2 ^ (w + w) = 2 ^ w * 2 ^ w from pow_add _ _ _,
    ← ofDigits_pairBlocks] at he
  simpa only [pow_add] using he

theorem pairDigits_lt {b : ℕ} (hb : 0 < b) (l : List ℕ) (hl : ∀ a ∈ l, a < b) :
    ∀ a ∈ pairBlocks (fun x y => x + b * y) l, a < b * b := by
  refine pairBlocks_forall (fun x y => x + b * y) (P := fun a => a < b)
    (Q := fun a => a < b * b) hb ?_ l hl
  intro a c ha hc
  calc a + b * c < b + b * c := Nat.add_lt_add_right ha _
    _ = b * (c + 1) := by ring
    _ ≤ b * b := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hc)

end Sarkozy.F3Kernel
