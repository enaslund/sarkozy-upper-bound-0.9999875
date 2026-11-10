module

public import Sarkozy.Functional.Lift

@[expose] public section

/-!
# Characters as elements of `ℚ/ℤ` (`def:record:functional`(b))

`def:record:functional`(b) identifies the character with label `(a_p)_p` with
`ξ = ∑_p a_p/p^{e_p} ∈ ℚ/ℤ`, defines its conductor as the reduced denominator of
`ξ`, and uses `e(nξ)` for integers `n`. This module proves that the
representation of `Lift.lean` agrees with this reading:

* `conductor_eq_den`: for pairwise coprime moduli, the conductor
  `∏_j addOrderOf (a j)` is the reduced denominator of `∑_j a_j/m_j`
  (with `a_j` represented in `[0, m_j)`);
* `prodChar_integerResidue_eq_expPhase`: `e(n·ξ)` for an integer `n` is the
  character value at the residue of `n`.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

/-- The reduced denominator of a sum of two rationals with coprime denominators is
the product of the denominators. -/
theorem rat_den_add_of_coprime (x y : ℚ) (h : x.den.Coprime y.den) :
    (x + y).den = x.den * y.den := by
  apply Nat.dvd_antisymm (Rat.add_den_dvd x y)
  have hx : x.den ∣ (x + y).den := by
    have h1 := Rat.add_den_dvd (x + y) (-y)
    have e : x + y + -y = x := by ring
    rw [e, Rat.neg_den] at h1
    exact h.dvd_of_dvd_mul_right h1
  have hy : y.den ∣ (x + y).den := by
    have h1 := Rat.add_den_dvd (x + y) (-x)
    have e : x + y + -x = y := by ring
    rw [e, Rat.neg_den] at h1
    exact h.symm.dvd_of_dvd_mul_right h1
  exact h.mul_dvd_of_dvd_of_dvd hx hy

/-- The reduced denominator of `v/n` is `n / gcd(n, v)`. -/
theorem rat_den_natCast_div (v n : ℕ) (hn : n ≠ 0) : ((v : ℚ) / n).den = n / n.gcd v := by
  obtain ⟨g, hg⟩ : ∃ g, g = n.gcd v := ⟨_, rfl⟩
  rw [← hg]
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  obtain ⟨n', hn'⟩ : g ∣ n := hg ▸ Nat.gcd_dvd_left n v
  obtain ⟨v', hv'⟩ : g ∣ v := hg ▸ Nat.gcd_dvd_right n v
  have hcop : Nat.Coprime n' v' := by
    have h := Nat.coprime_div_gcd_div_gcd (m := n) (n := v) (hg ▸ hg0)
    rw [← hg] at h
    rwa [hn', hv', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at h
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h, mul_zero] at hn'; exact absurd hn' hn
    · exact h
  have hq : ((v : ℚ) / n) = ((v' : ℤ) : ℚ) / ((n' : ℤ) : ℚ) := by
    rw [hn', hv']
    push_cast
    have : (g : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
    field_simp
  have hden := Rat.den_div_eq_of_coprime (a := (v' : ℤ)) (b := (n' : ℤ))
    (by exact_mod_cast hn'pos) (by simpa using hcop.symm)
  rw [hq, hn', Nat.mul_div_cancel_left _ hg0]
  exact_mod_cast hden

/-- The reduced denominator of `x/n` for `x ∈ [0, n)` is the additive order of
`x` in `ℤ/nℤ`. -/
theorem rat_den_val_div {n : ℕ} [NeZero n] (x : ZMod n) :
    (((x.val : ℚ) / n).den) = addOrderOf x := by
  have hn : n ≠ 0 := NeZero.ne n
  rw [rat_den_natCast_div _ _ hn]
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  exact (ZMod.addOrderOf_coe _ hn).symm

variable {J : Type*} [Fintype J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The rational representative `ξ = ∑_j a_j/m_j`, `a_j ∈ [0, m_j)`, of the
character with label `a` (`def:record:functional`(b)). -/
noncomputable def frequency (a : ResidueSpace m) : ℚ := ∑ j, ((a j).val : ℚ) / m j

/-- `def:record:functional`(b): for pairwise coprime moduli the conductor is the
reduced denominator of `ξ = ∑_j a_j/m_j`. -/
theorem conductor_eq_den (hcop : Pairwise fun i j => (m i).Coprime (m j))
    (a : ResidueSpace m) : conductor m a = (frequency m a).den := by
  classical
  unfold conductor frequency
  have key : ∀ s : Finset J,
      (∑ j ∈ s, ((a j).val : ℚ) / m j).den = ∏ j ∈ s, addOrderOf (a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [sum_insert hi, prod_insert hi, rat_den_add_of_coprime, ih, rat_den_val_div]
      rw [rat_den_val_div, ih]
      apply Nat.Coprime.prod_right
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      exact Nat.Coprime.of_dvd (addOrderOf_dvd_modulus m i (a i))
        (addOrderOf_dvd_modulus m j (a j)) (hcop hij)
  exact (key univ).symm

/-- For an integer `n`, `e(nξ)` with `ξ = ∑_j a_j/m_j` is the value of the
character at the residue of `n`: the paper's `e(nξ)` is well defined and equals
`prodChar m a (integerResidue m n)`. -/
theorem prodChar_integerResidue_eq_expPhase (a : ResidueSpace m) (n : ℤ) :
    prodChar m a (integerResidue m n) = expPhase (n * frequencyAngle m a) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · have := prodChar_nat_diagonal m a k
    simpa [integerResidue] using this
  · rw [prodChar_integerResidue_neg]
    have := prodChar_nat_diagonal m a k
    have h1 : prodChar m a (integerResidue m (k : ℤ)) = expPhase (k * frequencyAngle m a) := by
      simpa [integerResidue] using this
    rw [h1]
    push_cast
    rw [neg_mul, expPhase_neg]

end Sarkozy.Functional
