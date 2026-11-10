module

public import Sarkozy.Functional.FibreScale

@[expose] public section

/-!
# Averaging a lift over coordinates (`lem:record:fibre-scale`(c), Fourier step)

In the proof of `lem:record:fibre-scale`(c) the paper uses: "averaging `u_j`
over the coordinates of `E'` deletes exactly the characters that are
nonconstant on an atom of `E'` and leaves the others; the remaining characters
are those of `h_j`, with the same coefficients. Hence `E_{E'} u_j = h_j`."

`expect_liftOn_freeze` is this Fourier identity for an arbitrary lift and an
arbitrary set `W` of coordinates: the average over the `W`-coordinates of the
lift with label set `T` is the lift with label set `{a ∈ T : a = 0 on W}`. With
`T` the retained set `{q(a) ≤ Q'}`, the result is the lift on the remaining
coordinates (`expect_lift_freeze`); this is `E_{E'} u_j = h_j` once the
characters of `G_n` of conductor `≤ n^β` vanishing on `E'` are identified with
the retained characters of `X_{𝒮'}`. The remaining inequality of (c),
`Z_{𝒮'}(E_{E'} u_j) ≤ Z_{𝒜_n}(u_j)` (averaging over atoms does not increase `Z`,
`lem:record:holder`(d)), is not formalized here.
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- Averaging a character over the coordinates of `W` keeps it exactly when it
vanishes on `W`. -/
theorem expect_prodChar_freeze (W : Finset J) (a y : ResidueSpace m) :
    (𝔼 t, prodChar m a (coordinateFreeze m W t y)) =
      if restrictIn m W a = 0 then prodChar m a y else 0 := by
  simp_rw [prodChar_coordinateFreeze]
  rw [← expect_mul, prodChar_expect]
  by_cases h : restrictIn m W a = 0
  · rw [ite_eq_left h, ite_eq_left h, one_mul]
    congr 1
    funext j
    have hj := congrFun h j
    simp only [restrictOut, restrictIn, Pi.zero_apply] at hj ⊢
    split_ifs with hjW
    · rw [ite_eq_left hjW] at hj; exact hj.symm
    · rfl
  · rw [ite_eq_right h, ite_eq_right h, zero_mul]

/-- `E_W 𝓛_T f = 𝓛_{T ∩ {a = 0 on W}} f`: averaging a lift over the coordinates
of `W` deletes exactly the characters that are nonconstant on `W`. -/
theorem expect_liftOn_freeze (T : Finset (ResidueSpace m)) (I : Finset ℤ) (f : ℤ → ℂ)
    (W : Finset J) (y : ResidueSpace m) :
    (𝔼 t, liftOn m T I f (coordinateFreeze m W t y)) =
      liftOn m (T.filter fun a => ∀ j ∈ W, a j = 0) I f y := by
  unfold liftOn
  rw [expect_sum_comm, sum_filter]
  apply sum_congr rfl
  intro a _
  rw [← mul_expect, expect_prodChar_freeze]
  have hiff : restrictIn m W a = 0 ↔ ∀ j ∈ W, a j = 0 := by
    constructor
    · intro h j hj
      have := congrFun h j
      simpa only [restrictIn, ite_eq_left hj, Pi.zero_apply] using this
    · intro h
      funext j
      simp only [restrictIn, Pi.zero_apply]
      split_ifs with hj
      · exact h j hj
      · rfl
  by_cases h : ∀ j ∈ W, a j = 0
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, mul_zero]

/-- With the retained set: averaging `𝓛_{I,N} f` over the coordinates of `W`
gives the lift with the retained characters that vanish on `W`, i.e. the lift on
the remaining coordinates with the same cutoff (`retainedOff`). -/
theorem expect_lift_freeze (Q : ℝ) (I : Finset ℤ) (f : ℤ → ℂ) (W : Finset J)
    (y : ResidueSpace m) :
    (𝔼 t, lift m Q I f (coordinateFreeze m W t y)) =
      liftOn m (retainedOff m W Q) I f y := by
  unfold lift
  rw [expect_liftOn_freeze]
  congr 1
  ext a
  simp [retained, retainedOff, and_comm]

omit [Fintype J] [DecidableEq J] [∀ j, NeZero (m j)] in
/-- The children `A'_j ⊆ [n]` of the square step are admissible at the scale `n`
(`lem:record:fibre-scale`(b),(c): they are the sets to which the induction
hypothesis `Y(ℓ, A'_j) ≤ …`, `n = Kℓ`, is applied). -/
theorem stepChild_admissible {A : Finset ℤ} (hA : IsSquareDifferenceFree A) (I : Finset ℤ)
    {R r : ℕ} (hR : R = r ^ 2) (hr : 1 ≤ r) (n : ℕ) (c j : ℤ) :
    Admissible n (stepChild A I R n c j) :=
  ⟨filter_subset _ _, stepChild_free hA I hR hr n c j⟩

end Sarkozy.Functional
