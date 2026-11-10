module

public import Sarkozy.JointRows.Eig

/-!
# Non-vacuity of `Eig.PaleyLike`: the normalized Paley operator at `p = 3`

At `p = 3 ≡ 3 (mod 4)` the Paley operator is `C f(t) = ∑_s χ(s - t) f(s)/3`. Its normalization
`Φ̂ = C/r`, `r = 3^{-1/2}`, is `Φ̂ f(t) = (f(t + 1) - f(t + 2))/√3`, since `χ(1) = 1`, `χ(2) = -1`.
`paley3_paleyLike` shows that this operator satisfies `PaleyLike` for the uniform law on `ℤ/3ℤ`:
`Φ̂* = -Φ̂` and `Φ̂² = -(I - J)`. These are the facts of `lem:spec:gauss` that `heig_holds` uses.
The instance is not degenerate, because `L²_0(ℤ/3ℤ)` is the plane and `Φ̂` rotates it by a
right angle.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.EigSanity

open Sarkozy.JointRows.Eig

/-- The normalized Paley operator at `p = 3`. -/
noncomputable def paley3 (f : ZMod 3 → ℝ) (t : ZMod 3) : ℝ := (f (t + 1) - f (t + 2)) / √3

theorem sum_zmod3 (g : ZMod 3 → ℝ) : ∑ t, g t = g 0 + g 1 + g 2 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **`Φ̂` at `p = 3` has the properties of `lem:spec:gauss`.** -/
theorem paley3_paleyLike : PaleyLike (FiniteLaw.uniform (ZMod 3)) paley3 := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hs : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : √3 ≠ 0 := by positivity
  have hcard : (Fintype.card (ZMod 3) : ℝ) = 3 := by simp
  have e1 : (0 : ZMod 3) + 1 = 1 := by decide
  have e2 : (0 : ZMod 3) + 2 = 2 := by decide
  have e3 : (1 : ZMod 3) + 1 = 2 := by decide
  have e4 : (1 : ZMod 3) + 2 = 0 := by decide
  have e5 : (2 : ZMod 3) + 1 = 0 := by decide
  have e6 : (2 : ZMod 3) + 2 = 1 := by decide
  constructor
  · intro f g
    simp only [FiniteLaw.expect, FiniteLaw.uniform, hcard, paley3]
    rw [sum_zmod3, sum_zmod3]
    simp only [e1, e2, e3, e4, e5, e6]
    field_simp
    ring
  · intro f t
    simp only [FiniteLaw.expect, FiniteLaw.uniform, hcard, paley3]
    rw [sum_zmod3]
    have ht : t = 0 ∨ t = 1 ∨ t = 2 := by revert t; decide
    rcases ht with rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5, e6] <;>
      rw [← sub_div, div_div, hs] <;> ring

end Sarkozy.JointRows.EigSanity
