module

public import Sarkozy.F3Kernel.Checker
public import Sarkozy.F3Kernel.Sanity
public import Sarkozy.F3Kernel.LL22Consts
public import Sarkozy.Extraction.CompressedPartition
public import Mathlib.Data.Fintype.Prod

@[expose] public section




namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

/-- The pairs of a `T`-layout mask: `(x, y)` with bit `64 y + x` set. -/
def decT (n : Nat) : Finset (Fin 36 × Fin 36) :=
  univ.filter fun e => n.testBit (64 * (e.2 : Nat) + e.1) = true

/-- The pair at `T`-position `p` (`p % 64 < 36`, `p / 64 < 36`). -/
def pairOf (p : Nat) (hx : p % 64 < 36) (hy : p / 64 < 36) : Fin 36 × Fin 36 :=
  (⟨p % 64, hx⟩, ⟨p / 64, hy⟩)

/-- The edge mask of `G` has its bits at positions `64 y + x` with `x, y < 36` only. -/
def Consts.WellFormedT (G : Consts) : Prop :=
  ∀ p, G.ET.testBit p = true → p % 64 < 36 ∧ p / 64 < 36

/-- The checker's bit test is `Nat.testBit`. -/
theorem bit_eq_testBit (x i : Nat) : bit x i = x.testBit i := by
  unfold bit
  rw [Nat.testBit_eq_decide_div_mod_eq, show Nat.land (Nat.shiftRight x i) 1 = x >>> i &&& 1 from rfl,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> rw [h] <;> rfl

/-- Setting bit `p`. -/
theorem testBit_lor_bit (a p j : Nat) :
    (Nat.lor a (Nat.shiftLeft 1 p)).testBit j = (a.testBit j || decide (p = j)) := by
  rw [show Nat.lor a (Nat.shiftLeft 1 p) = a ||| 2 ^ p by
    rw [show Nat.lor a (Nat.shiftLeft 1 p) = a ||| (1 <<< p) from rfl, Nat.shiftLeft_eq,
      one_mul]]
  rw [Nat.testBit_or, Nat.testBit_two_pow]

/-- The position of a pair determines it. -/
theorem pos_eq_iff (p : Nat) (hx : p % 64 < 36) (hy : p / 64 < 36) (e : Fin 36 × Fin 36) :
    p = 64 * (e.2 : Nat) + e.1 ↔ e = pairOf p hx hy := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := e
  simp only [pairOf, Prod.mk.injEq, Fin.mk.injEq]
  omega

/-- Setting bit `p` adds the pair at `p`. -/
theorem decT_lor_bit (a p : Nat) (hx : p % 64 < 36) (hy : p / 64 < 36) :
    decT (Nat.lor a (Nat.shiftLeft 1 p)) = insert (pairOf p hx hy) (decT a) := by
  ext e
  simp only [decT, mem_filter, mem_univ, true_and, mem_insert, testBit_lor_bit,
    Bool.or_eq_true, decide_eq_true_eq, pos_eq_iff p hx hy e]
  tauto

/-- The pair at `p` lies in `decT n` exactly when bit `p` of `n` is set. -/
theorem pairOf_mem_decT (n p : Nat) (hx : p % 64 < 36) (hy : p / 64 < 36) :
    pairOf p hx hy ∈ decT n ↔ n.testBit p = true := by
  simp only [decT, mem_filter, mem_univ, true_and, pairOf]
  rw [show 64 * (p / 64) + p % 64 = p by omega]

/-- The token of a split on the `T`-position `pay` decodes to tag `1` and payload `pay`. -/
theorem split_token (pay : Nat) :
    Nat.land (4 * pay + 1) 3 = 1 ∧ Nat.shiftRight (4 * pay + 1) 2 = pay := by
  constructor
  · rw [show Nat.land (4 * pay + 1) 3 = (4 * pay + 1) &&& (2 ^ 2 - 1) from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rw [show Nat.shiftRight (4 * pay + 1) 2 = (4 * pay + 1) >>> 2 from rfl,
      Nat.shiftRight_eq_div_pow]
    omega

/-- **A split token accepted by `step`.** If the current cylinder is `c`, the token `4 pay + 1`
is accepted only if `pay` is the position of a pair `g` of the edge set that is free in `c`
(`T` layout), and the new current cylinder and the pushed cylinder are `c` with `g` present,
resp. absent. -/
theorem step_split {G : Consts} (hG : G.WellFormedT) {st st' : St} {c : Cyl} {pay : Nat}
    (hc : st.cur = some c) (h : step G st (4 * pay + 1) = some st') :
    ∃ (hx : pay % 64 < 36) (hy : pay / 64 < 36),
      pairOf pay hx hy ∈ decT G.ET \ (decT c.pt ∪ decT c.qt) ∧
      (∃ pm, st'.cur = some ⟨pm, c.am, Nat.lor c.pt (Nat.shiftLeft 1 pay), c.qt⟩) ∧
      (∃ am, ∃ rest, st'.stack = ⟨c.pm, am, c.pt, Nat.lor c.qt (Nat.shiftLeft 1 pay)⟩ :: rest) := by
  obtain ⟨htag, hpay⟩ := split_token pay
  unfold step at h
  simp only [htag, hpay, hc] at h
  simp only [Nat.beq_refl, Bool.cond_true] at h
  -- the guard
  have hguard : (Nat.blt pay 2304 && isEdge G pay && !bit (Nat.lor c.pt c.qt) pay) = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rw [hne, Bool.cond_false] at h
    cases h
  rw [hguard, Bool.cond_true, Option.some.injEq] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hguard
  obtain ⟨⟨-, hedge⟩, hfree⟩ := hguard
  rw [isEdge, bit_eq_testBit] at hedge
  rw [bit_eq_testBit, show Nat.lor c.pt c.qt = c.pt ||| c.qt from rfl, Nat.testBit_or,
    Bool.or_eq_false_iff] at hfree
  obtain ⟨hx, hy⟩ := hG pay hedge
  refine ⟨hx, hy, ?_, ⟨_, by rw [← h]⟩, ⟨_, _, by rw [← h]⟩⟩
  rw [mem_sdiff, mem_union, pairOf_mem_decT, pairOf_mem_decT, pairOf_mem_decT, hfree.1,
    hfree.2]
  exact ⟨hedge, by simp⟩

/-- **The split as a refinement step** (`lem:advance:compressed-partition`(c)): in any family
`𝓟` of class data containing the decoded current cylinder `(P, A)`, replacing it by the decoded
new current and pushed cylinders is a `RefineStep` of the edge set `decT G.ET`. With
`IsExactPartition.refine`, a sequence of accepted splits keeps an exact partition. -/
theorem step_split_refineStep {G : Consts} (hG : G.WellFormedT) {st st' : St} {c : Cyl}
    {pay : Nat} (hc : st.cur = some c) (h : step G st (4 * pay + 1) = some st')
    (𝓟 : Finset (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)))
    (h𝓟 : (decT c.pt, decT c.qt) ∈ 𝓟) :
    ∃ c₁ c₂ : Cyl, st'.cur = some c₁ ∧ st'.stack.head? = some c₂ ∧
      RefineStep (decT G.ET) 𝓟
        (insert (decT c₁.pt, decT c₁.qt) (insert (decT c₂.pt, decT c₂.qt)
          (𝓟.erase (decT c.pt, decT c.qt)))) := by
  obtain ⟨hx, hy, hg, ⟨pm, hcur⟩, ⟨am, rest, hstack⟩⟩ := step_split hG hc h
  refine ⟨_, _, hcur, by rw [hstack]; rfl, ⟨(decT c.pt, decT c.qt), h𝓟, pairOf pay hx hy, hg, ?_⟩⟩
  simp only [decT_lor_bit _ _ hx hy]

/-- The `T`-layout well-formedness of generated constants is a bounded check: it holds if
`G.ET < 2^N` and every set bit below `N` is at a position `64 y + x` with `x, y < 36` (for the
generated constants, `N = 2304` and the bounded check is a finite `decide`). -/
theorem wellFormedT_of_bounded {G : Consts} {N : Nat} (hlt : G.ET < 2 ^ N)
    (hbits : ∀ p < N, G.ET.testBit p = true → p % 64 < 36 ∧ p / 64 < 36) :
    G.WellFormedT := by
  intro p hp
  by_cases h : p < N
  · exact hbits p h hp
  · have hle : 2 ^ N ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt h)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt hle)] at hp
    exact absurd hp (by decide)

/-- Non-vacuity of `Consts.WellFormedT`: the generated LL20 constants satisfy it. -/
theorem LL20_wellFormedT : LL20.WellFormedT :=
  wellFormedT_of_bounded (N := 2304) (by decide +kernel) (by decide +kernel)

/-- Non-vacuity of `Consts.WellFormedT`: the generated LL22 constants satisfy it. -/
theorem LL22_wellFormedT : LL22.WellFormedT :=
  wellFormedT_of_bounded (N := 2304) (by decide +kernel) (by decide +kernel)

/-- Non-vacuity of `step_split`: in the class `Sanity.good` (tokens: class, split, leaf, …) the
split token is accepted after the class token. -/
theorem good_split_accepted :
    ((step LL20 ⟨none, [], 0, 0, 0, 0, 0, 0, 0⟩ (Sanity.good.getD 0 0)).bind
      (fun st => step LL20 st (Sanity.good.getD 1 0))).isSome = true := by
  decide +kernel

/-- The second token of `Sanity.good` is a split token `4 pay + 1`. -/
theorem good_token_one : Nat.land (Sanity.good.getD 1 0) 3 = 1 := by
  decide +kernel

end Sarkozy.F3Kernel
