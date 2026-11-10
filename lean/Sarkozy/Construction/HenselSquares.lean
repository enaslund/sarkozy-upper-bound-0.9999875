module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Squares lift modulo odd prime powers (Hensel)

Used by the square-clique law (`lem:frontier:iidlocal`(iii), `paper/sections/19_prefix.tex`) and
by the remark after `def:strict-square-class`: for an odd prime `p` and an integer `u` prime to
`p`, if `u` is a square modulo `p` then it is a square modulo every power `p^k`.

* `hensel_square_step`: from `p^k ∣ x² - u` with `p ∤ x` to `p^{k+1} ∣ x'² - u` with
  `x' ≡ x (mod p)`.
* `exists_sq_mod_pow`: lifting to every `k ≥ 1`.
* `isSquare_zmod_pow`: the statement in `ZMod (p^k)`.
-/

@[expose] public section

namespace Sarkozy.Hensel

variable {p : ℕ} [hp : Fact p.Prime]

/-- **One Hensel step for `X² - u`** at an odd prime. -/
theorem hensel_square_step (hp2 : p ≠ 2) {k : ℕ} (hk1 : 1 ≤ k) {x u : ℤ} (hx : ¬ (p : ℤ) ∣ x)
    (hk : (p : ℤ) ^ k ∣ x ^ 2 - u) :
    ∃ x' : ℤ, (p : ℤ) ^ (k + 1) ∣ x' ^ 2 - u ∧ (p : ℤ) ∣ x' - x := by
  obtain ⟨m, hm⟩ := hk
  -- solve `2 x t + m ≡ 0 (mod p)` for `t`
  have h2x : ((2 * x : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h with h' | h'
    · have : (p : ℤ) ∣ 2 := h'
      have : p ∣ 2 := by exact_mod_cast this
      rcases (Nat.le_of_dvd (by norm_num) this).lt_or_eq with hlt | heq
      · interval_cases p
        · exact absurd hp.out Nat.not_prime_zero
        · exact absurd hp.out Nat.not_prime_one
      · exact hp2 heq
    · exact hx h'
  set t : ℤ := ((((-(m : ZMod p)) * ((2 * x : ℤ) : ZMod p)⁻¹ : ZMod p)).val : ℤ)
  have htcast : ((t : ℤ) : ZMod p) = (-(m : ZMod p)) * ((2 * x : ℤ) : ZMod p)⁻¹ := by
    simp only [t, Int.cast_natCast, ZMod.natCast_zmod_val]
  have ht : ((2 * x * t + m : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [htcast]
    have : ((2 : ZMod p) * x) * ((2 * x : ℤ) : ZMod p)⁻¹ = 1 := by
      have := mul_inv_cancel₀ h2x
      push_cast at this ⊢
      exact this
    linear_combination (-(m : ZMod p)) * this
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ht
  obtain ⟨r, hr⟩ := ht
  have hpow : (p : ℤ) ^ k = p * p ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hpow2 : (p : ℤ) ^ (2 * k) = p ^ (k + 1) * p ^ (k - 1) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨x + t * p ^ k, ⟨r + t ^ 2 * p ^ (k - 1), ?_⟩, ⟨t * p ^ (k - 1), ?_⟩⟩
  · -- (x + t p^k)² - u = p^k (2xt + m) + t² p^{2k} = p^{k+1} r + t² p^{2k}
    have : (x + t * p ^ k) ^ 2 - u = p ^ k * (2 * x * t + m) + t ^ 2 * p ^ (2 * k) := by
      rw [show (x + t * (p : ℤ) ^ k) ^ 2 - u = (x ^ 2 - u) + 2 * x * t * p ^ k +
        t ^ 2 * (p ^ k) ^ 2 by ring, hm, ← pow_mul, mul_comm k 2]
      ring
    rw [this, hr, hpow2, pow_succ]
    ring
  · rw [hpow]; ring

/-- **Squares lift to every power of an odd prime.** -/
theorem exists_sq_mod_pow (hp2 : p ≠ 2) {u x₀ : ℤ} (hx₀ : ¬ (p : ℤ) ∣ x₀)
    (h₀ : (p : ℤ) ∣ x₀ ^ 2 - u) :
    ∀ k : ℕ, 1 ≤ k → ∃ x : ℤ, (p : ℤ) ^ k ∣ x ^ 2 - u ∧ ¬ (p : ℤ) ∣ x := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨x₀, by simpa using h₀, hx₀⟩
  | succ k _ ih =>
    obtain ⟨x, hxk, hxp⟩ := ih
    obtain ⟨x', hx', hcong⟩ := hensel_square_step hp2 (by assumption) hxp hxk
    refine ⟨x', hx', fun h => hxp ?_⟩
    have := dvd_sub h hcong
    simpa using this

/-- **`IsSquare` lifts from `ZMod p` to `ZMod (p^k)`** for integers prime to an odd `p`. -/
theorem isSquare_zmod_pow (hp2 : p ≠ 2) {u : ℤ} (hu : ¬ (p : ℤ) ∣ u)
    (hsq : IsSquare (u : ZMod p)) (k : ℕ) : IsSquare (u : ZMod (p ^ k)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]; exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨r, hr⟩ := hsq
  set x₀ : ℤ := (r.val : ℤ)
  have hx0c : ((x₀ : ℤ) : ZMod p) = r := by
    simp only [x₀, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hr' : ((x₀ ^ 2 - u : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hx0c, hr]; ring
  have h₀ : (p : ℤ) ∣ x₀ ^ 2 - u := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hr'
  have hx₀ : ¬ (p : ℤ) ∣ x₀ := by
    intro h
    have : (p : ℤ) ∣ x₀ ^ 2 := dvd_pow h two_ne_zero
    have : (p : ℤ) ∣ u := by
      have := dvd_sub this h₀
      simpa using this
    exact hu this
  obtain ⟨x, hx, _⟩ := exists_sq_mod_pow hp2 hx₀ h₀ k hk
  refine ⟨(x : ZMod (p ^ k)), ?_⟩
  have h0 : (((x ^ 2 - u : ℤ)) : ZMod (p ^ k)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hx
  push_cast at h0
  linear_combination -h0

end Sarkozy.Hensel
