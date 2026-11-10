module

public import Sarkozy.PartV.IndexIncrement
public import Sarkozy.TheoremC.Defs

@[expose] public section

/-!
# The increments of the coupled index are nonvanishing square classes

`paper/sections/18_design.tex`, `def:construction`(a), and `def:nonvanishing-square-class`.

The increment at a prime power `p^h` of `M₀` is `x²` for `x` of `p`-adic valuation `j < 64`
(V1's `PartV.squareIncrementLaw p h 64`). With `h ≥ 128`, and `h ≥ 129` at `p = 2`, the residue
`x² = p^{2j} w` has even valuation `2j < h` and a unit part `w ≡ u²` (`x = p^j u`) that is a
nonzero square modulo `p`, and `≡ 1 (mod 8)` with `2j + 3 ≤ h` at `p = 2`. So every increment is
a nonvanishing square coordinate (`TheoremC.IsNonvanishingSquareCoord`):
`squareIncrementLaw_nonvanishing`. V1 lists this as not proved in `IndexIncrement.lean`.
-/

namespace Sarkozy.PaperData

open Finset

/-- Odd squares are `1` modulo `8`. -/
theorem odd_mul_self_mod_eight {u : ℕ} (hu : u % 2 = 1) : u * u % 8 = 1 := by
  have h8 : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
  rw [Nat.mul_mod]
  rcases h8 with h | h | h | h <;> rw [h]

/-- **The arithmetic of `x²` modulo `p^h`** for `x` of valuation `j < 64`: with `u = n / p^j`,
`n² mod p^h = p^{2j} · (u² mod p^{h-2j})`, and `p ∤ u² mod p^{h-2j}`. -/
theorem sq_mod_prime_pow {p h n : ℕ} (hp : p.Prime) (hn : ¬ p ^ 64 ∣ n) (hh : 128 ≤ h) :
    ∃ j u : ℕ, j < 64 ∧ ¬ p ∣ u ∧
      n * n % p ^ h = p ^ (2 * j) * (u * u % p ^ (h - 2 * j)) ∧
      ¬ p ∣ u * u % p ^ (h - 2 * j) := by
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero _)
  have : Fact p.Prime := ⟨hp⟩
  set j := padicValNat p n with hj
  have hdvd : p ^ j ∣ n := pow_padicValNat_dvd
  have hj64 : j < 64 := by
    by_contra hge
    exact hn ((pow_dvd_pow p (not_lt.mp hge)).trans hdvd)
  obtain ⟨u, hu⟩ := hdvd
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hn0 (by rw [hu, mul_zero])
  have hpu : ¬ p ∣ u := by
    intro hpu
    obtain ⟨c, hc⟩ := hpu
    have h1 : p ^ (j + 1) ∣ n := ⟨c, by rw [hu, hc, pow_succ]; ring⟩
    have h2 := (padicValNat_dvd_iff_le hn0).mp h1
    omega
  have hsplit : p ^ h = p ^ (2 * j) * p ^ (h - 2 * j) := by
    rw [← pow_add]
    congr 1
    omega
  have hnn : n * n = p ^ (2 * j) * (u * u) := by
    rw [hu, pow_mul]
    ring
  have hk : 1 ≤ h - 2 * j := by omega
  refine ⟨j, u, hj64, hpu, ?_, ?_⟩
  · rw [hnn, hsplit, Nat.mul_mod_mul_left]
  · intro hw
    have hmod : u * u % p ^ (h - 2 * j) % p = u * u % p :=
      Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega))
    have h0 : u * u % p = 0 := by
      rw [← hmod]
      exact Nat.mod_eq_zero_of_dvd hw
    rcases (Nat.Prime.dvd_mul hp).mp (Nat.dvd_of_mod_eq_zero h0) with h | h <;> exact hpu h
/-- **The square of a residue of valuation `< 64` is a nonvanishing square coordinate** of
`ℤ/p^hℤ`, for `h ≥ 128` and `h ≥ 129` at `p = 2`. -/
theorem sq_nonvanishing {p h : ℕ} [NeZero (p ^ h)] (hp : p.Prime) (hh : 128 ≤ h)
    (h2 : p = 2 → 129 ≤ h) {x : ZMod (p ^ h)} (hx : ¬ p ^ 64 ∣ x.val) :
    TheoremC.IsNonvanishingSquareCoord p h (x ^ 2) := by
  obtain ⟨j, u, hj, hpu, heq, hw⟩ := sq_mod_prime_pow hp hx hh
  have : Fact p.Prime := ⟨hp⟩
  have hk0 : h - 2 * j ≠ 0 := by omega
  have hval : (x ^ 2).val = p ^ (2 * j) * (u * u % p ^ (h - 2 * j)) := by
    rw [sq, ZMod.val_mul, heq]
  have hw0 : u * u % p ^ (h - 2 * j) ≠ 0 := fun h0 => hw (h0 ▸ dvd_zero p)
  have hv : padicValNat p (x ^ 2).val = 2 * j := by
    rw [hval, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hw0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hw, add_zero]
  have hdiv : (x ^ 2).val / p ^ padicValNat p (x ^ 2).val = u * u % p ^ (h - 2 * j) := by
    rw [hv, hval, Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  unfold TheoremC.IsNonvanishingSquareCoord
  refine ⟨by rw [hval]; exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) hw0,
    by rw [hv]; exact even_two_mul j, ?_⟩
  split_ifs with hp2
  · subst hp2
    have h129 := h2 rfl
    refine ⟨by rw [hv]; omega, ?_⟩
    rw [hdiv]
    have h3 : 3 ≤ h - 2 * j := by omega
    have h8 : 8 ∣ 2 ^ (h - 2 * j) := by
      have := Nat.pow_dvd_pow 2 h3
      simpa using this
    rw [Nat.mod_mod_of_dvd _ h8]
    exact odd_mul_self_mod_eight (Nat.two_dvd_ne_zero.mp hpu)
  · rw [hdiv]
    have hcast : (((u * u % p ^ (h - 2 * j) : ℕ)) : ZMod p) = (u : ZMod p) * (u : ZMod p) := by
      rw [(ZMod.natCast_eq_natCast_iff' _ (u * u) p).mpr
        (Nat.mod_mod_of_dvd _ (dvd_pow_self p hk0)), Nat.cast_mul]
    refine ⟨⟨(u : ZMod p), hcast⟩, ?_⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hw

/-- **Every increment of `squareIncrementLaw p h 64` is a nonvanishing square coordinate**
(`def:construction`(a) with `def:nonvanishing-square-class`). -/
theorem squareIncrementLaw_nonvanishing {p h : ℕ} [NeZero (p ^ h)] (hp : p.Prime)
    (hh : 128 ≤ h) (h2 : p = 2 → 129 ≤ h) (hne : (PartV.lowValuation p h 64).Nonempty)
    {r : ZMod (p ^ h)} (hr : (PartV.squareIncrementLaw p h 64 hne).weight r ≠ 0) :
    TheoremC.IsNonvanishingSquareCoord p h r := by
  obtain ⟨x, hx, rfl⟩ := PartV.squareIncrementLaw_support hne hr
  have hx' : ¬ p ^ 64 ∣ x.val := by
    unfold PartV.lowValuation at hx
    exact (mem_filter.mp hx).2
  exact sq_nonvanishing hp hh h2 hx'

end Sarkozy.PaperData
