module

public import Sarkozy.PartV.Parameters
public import Sarkozy.ProbabilityConstructions

@[expose] public section

/-!
# The increments of the coupled index (`def:construction`(a))

`paper/sections/18_design.tex`, `def:construction`(a): the index of a query is
`ω_e = (b_e, s_e) ∈ ℤ/Kℤ × ℤ/M₀ℤ`, coupled to `(b_e + 1, s_e + r_e)`, where each prime-power
component of `r_e` is the square of a uniform residue conditioned to have `p`-adic valuation
less than `m_ext = 64`. Here, at one prime power `p^h` of `M₀` (`h = 2m_ext + 1 = 129` at
`p = 2`, `h = 2m_ext = 128` at the odd primes of the small modulus):
* `lowValuation p h v`: the residues `x` of `ℤ/p^hℤ` with `p^v ∤ x` (valuation `< v`), nonempty
  for `v ≥ 1` (`one_mem_lowValuation`);
* `squareIncrementLaw p h v`: the law of `x²` for `x` uniform on `lowValuation p h v`;
* `smallModulusExponent p`: `h_2 = 129`, `h_p = 128` otherwise.

Not proved here: that these increments are nonvanishing square classes
(`TheoremC.IsNonvanishingSquareCoord`), and the depth tails `δ_{p,j}` of
`lem:imp:padic-envelope`.
-/

namespace Sarkozy.PartV

open Finset

/-- The exponent of the prime `p` in `M₀`: `2m_ext + 1 = 129` at `p = 2`, `2m_ext = 128` at the
odd primes of the small modulus. -/
def smallModulusExponent (p : ℕ) : ℕ := if p = 2 then 2 * mExt + 1 else 2 * mExt

/-- The residues of `ℤ/p^hℤ` of `p`-adic valuation less than `v`: `p^v ∤ x`. -/
def lowValuation (p h v : ℕ) [NeZero (p ^ h)] : Finset (ZMod (p ^ h)) :=
  univ.filter fun x => ¬ p ^ v ∣ x.val

/-- The residue `1` has valuation `0 < v` (for `p ≥ 2`, `v ≥ 1`, `h ≥ 1`). -/
theorem one_mem_lowValuation {p h v : ℕ} [NeZero (p ^ h)] (hp : 2 ≤ p) (hh : 1 ≤ h)
    (hv : 1 ≤ v) : (1 : ZMod (p ^ h)) ∈ lowValuation p h v := by
  unfold lowValuation
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  have hph : 1 < p ^ h := Nat.one_lt_pow (by omega) (by omega)
  have : (1 : ZMod (p ^ h)).val = 1 := by
    have : Fact (1 < p ^ h) := ⟨hph⟩
    exact ZMod.val_one (p ^ h)
  rw [this]
  intro hd
  have h1 : p ^ v ≤ 1 := Nat.le_of_dvd one_pos hd
  have h2 : 1 < p ^ v := Nat.one_lt_pow (by omega) (by omega)
  omega

/-- The uniform law on a nonempty finite set. -/
noncomputable def uniformOnSet {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X)
    (hA : A.Nonempty) : FiniteLaw X where
  weight x := if x ∈ A then (A.card : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  total := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    have : (A.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hA).ne'
    field_simp

/-- **The increment law at a prime power of `M₀`** (`def:construction`(a)): the law of `x²` for
`x` uniform on the residues of valuation less than `v`. -/
noncomputable def squareIncrementLaw (p h v : ℕ) [NeZero (p ^ h)]
    (hne : (lowValuation p h v).Nonempty) : FiniteLaw (ZMod (p ^ h)) :=
  (uniformOnSet (lowValuation p h v) hne).map fun x => x ^ 2

/-- The construction's increment law at a prime `p ≥ 2` of the small modulus, `v = m_ext = 64`. -/
noncomputable def indexIncrement (p : ℕ) (hp : 2 ≤ p) [NeZero (p ^ smallModulusExponent p)] :
    FiniteLaw (ZMod (p ^ smallModulusExponent p)) :=
  squareIncrementLaw p (smallModulusExponent p) mExt
    ⟨1, one_mem_lowValuation hp (by unfold smallModulusExponent mExt; split_ifs <;> norm_num)
      (by unfold mExt; norm_num)⟩

/-- Every increment is the square of a residue of valuation `< v` (its support). -/
theorem squareIncrementLaw_support {p h v : ℕ} [NeZero (p ^ h)]
    (hne : (lowValuation p h v).Nonempty) {r : ZMod (p ^ h)}
    (hr : (squareIncrementLaw p h v hne).weight r ≠ 0) :
    ∃ x ∈ lowValuation p h v, x ^ 2 = r := by
  unfold squareIncrementLaw FiniteLaw.map at hr
  obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  split_ifs at hx with hxr
  · refine ⟨x, ?_, hxr⟩
    by_contra hn
    apply hx
    change (if x ∈ lowValuation p h v then _ else 0) = 0
    simp only [hn, ↓reduceIte]
  · exact absurd rfl hx

end Sarkozy.PartV
