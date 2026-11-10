module

public import Sarkozy.PaperFrame.TwoScale

@[expose] public section

/-!
# Restoration at the paper's scales (`lem:record:fibre-scale`(c))

`lem:record:fibre-scale`(c) states `Z_𝒮(h_j) ≤ Y(ℓ, A'_j)`. This module proves the
averaging step for a law on any alphabet `X` identified with the group `G_N` by an additive
equivalence (`referenceEnergy_stepLift_le_equiv`), so that it applies directly to the
comparison worker's reference law on `X₀ × X_tail`.
-/

open Finset Function
open scoped BigOperators ComplexConjugate

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional

/-- `lem:record:fibre-scale`(c), averaging step, for a law on an alphabet `X ≃+ G_N`:
`Z_μ(h_j ∘ e) ≤ Z_μ(u_j ∘ e)`, with `h_j` the square-step piece (labels vanishing on `E`)
and `u_j` the lift with the same cutoff on all coordinates. The law must be reflection
positive at the sorting cuts and invariant under the simultaneous translations by the
elements of `X` whose image vanishes off `E` ((R2), and (R3) with `r_p = 1`). -/
theorem referenceEnergy_stepLift_le_equiv {Jc : Type} [Fintype Jc] [DecidableEq Jc]
    (m : Jc → ℕ) [∀ j, NeZero (m j)] {X : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
    (e : X ≃+ ResidueSpace m) (μ : FiniteLaw (Slot → X))
    (hp : SlotReflectionPositive (signedIntegral μ.weight)) (E : Finset Jc)
    (hinv : ∀ s : X, (∀ k ∉ E, e s k = 0) →
      ∀ F : (Slot → X) → ℝ, μ.expect (fun z => F (fun v => z v + s)) = μ.expect F)
    (Q' : ℝ) (B : Finset ℤ) (n : ℕ) :
    referenceEnergy μ (fun x => (stepLift m E Q' B n (e x)).re) ≤
      referenceEnergy μ (fun x => (Functional.lift m Q' (Icc 1 (n : ℤ)) (indicator B) (e x)).re) := by
  set u : ResidueSpace m → ℂ := fun y => Functional.lift m Q' (Icc 1 (n : ℤ)) (indicator B) y
  have hstep : ∀ x, (stepLift m E Q' B n (e x)).re =
      ∑ t : ResidueSpace m, (Fintype.card (ResidueSpace m) : ℝ)⁻¹ *
        (u (e (x + e.symm (restrictIn m E t)))).re := by
    intro x
    have h1 := expect_lift_freeze m Q' (Icc 1 (n : ℤ)) (indicator B) E (e x)
    rw [expect_freeze_eq_translates m E
      (fun y => Functional.lift m Q' (Icc 1 (n : ℤ)) (indicator B) y) (e x)] at h1
    unfold stepLift
    rw [← h1, expect_eq_sum_div_card, card_univ]
    have he : ∀ t : ResidueSpace m, e (x + e.symm (restrictIn m E t)) = e x + restrictIn m E t := by
      intro t
      rw [map_add, AddEquiv.apply_symm_apply]
    simp_rw [he]
    rw [show ((∑ t : ResidueSpace m, u (e x + restrictIn m E t)) /
        (Fintype.card (ResidueSpace m) : ℂ)) =
        (((Fintype.card (ResidueSpace m) : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ t : ResidueSpace m, u (e x + restrictIn m E t) by
      push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
  have hfun : (fun x => (stepLift m E Q' B n (e x)).re) = fun x =>
      ∑ t : ResidueSpace m, (Fintype.card (ResidueSpace m) : ℝ)⁻¹ *
        (u (e (x + e.symm (restrictIn m E t)))).re :=
    funext hstep
  rw [hfun]
  apply referenceEnergy_average_le μ hp (fun _ => (Fintype.card (ResidueSpace m) : ℝ)⁻¹)
    (fun _ => by positivity)
  · rw [sum_const, card_univ, nsmul_eq_mul]
    have : (Fintype.card (ResidueSpace m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · intro t
    have hs : ∀ k ∉ E, e (e.symm (restrictIn m E t)) k = 0 := by
      intro k hk
      rw [AddEquiv.apply_symm_apply]
      exact restrictIn_supported m E t k hk
    exact referenceEnergy_translate μ (e.symm (restrictIn m E t)) (hinv _ hs)
      (fun x => (u (e x)).re)

end Sarkozy.PaperFrame
