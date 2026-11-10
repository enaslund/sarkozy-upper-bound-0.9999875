module

public import Sarkozy.L20Cap.BalancedRowBounds

/-!
# The balanced L20 collision bound

`prop:l20-collisions`(a): the actual collision kernel has row means and form norm
at most `D_bal`. The only external analytic input is the named Weil bound.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Extraction Sarkozy.Labellings Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The balanced bound for every admissible row of the actual six-label kernel. -/
theorem balanced_collision_row (hW : WeilBound F) (hm1 : quadraticChar F (-1) = -1)
    (h64 : 64 ≤ Fintype.card F) (hne : (injLabellings F G6).Nonempty)
    (x : Fin 6 → F) (hx : x ∈ injLabellings F G6) :
    (graphLaw G6 hne).expect (collisionKernelColl D20Z x) ≤
      Dbal (Real.sqrt (Fintype.card F))⁻¹ (Fintype.card F : ℝ)⁻¹ := by
  have hQ : (64 : ℝ) ≤ Fintype.card F := by exact_mod_cast h64
  have hn : Fintype.card (Fin 6) ≤ 6 := by simp
  have hS1 := SanityX1.coarseError_G6_lt hQ
  have h1 := collision_rowSum_signed_incident_le hW G6 D20Z balanced_signs hm1 hne
    hn hS1 balancedOrd balancedOrd_spec x hx
  have h2 := collision_rowSum2_signed_incident_le hW G6 D20Z balanced_signs hm1 hne
    hn hS1 piVal pi_val_spec x hx
  have ha : Avoid (toHalf x hx) := (labels_mem _).mp (by rwa [labels_toHalf])
  have hD := balanced_incident_le hm1 hQ (toHalf x hx) ha piVal
  rw [labels_toHalf] at hD
  have he : collisionKernelColl D20Z x =
      fun y => collisionKernel1 D20Z x y + collisionKernel2 D20Z x y := by
    funext y
    exact collisionKernelColl_eq D20Z x y
  rw [he, FiniteLaw.expect_add]
  exact (add_le_add h1 h2).trans hD

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

/-- **`prop:l20-collisions`(a)**, in the half-law form used by the L20 caps. -/
theorem hD_balanced (hW : WeilBound F) (hm1 : quadraticChar F (-1) = -1)
    (h64 : 64 ≤ Fintype.card F) (f : CoreT F × PairT F → ℝ) :
    |kernelForm (halfLaw (by omega : 6 ≤ Fintype.card F))
        (halfLaw (by omega : 6 ≤ Fintype.card F)) collK f f| ≤
      Dbal (Real.sqrt (Fintype.card F))⁻¹ (Fintype.card F : ℝ)⁻¹ *
        nrm (halfLaw (by omega : 6 ≤ Fintype.card F)) f ^ 2 := by
  have h6 : 6 ≤ Fintype.card F := by omega
  have hne := injLabellings_G6_nonempty (F := F) h6
  refine schur_test (halfLaw h6) collK (collK_nonneg hm1) collK_symm (fun x hx => ?_) f
  have hAx : Avoid x := by
    by_contra h
    rw [halfLaw_weight_off h6 h] at hx
    exact lt_irrefl _ hx
  have hmem := (labels_mem x).mpr hAx
  have h := balanced_collision_row hW hm1 h64 hne (labels x) hmem
  rw [graphLaw_eq_halfLaw h6 hne] at h
  refine le_trans (le_of_eq ?_) h
  apply (halfLaw h6).expect_congr
  intro y
  rw [collisionKernelColl_eq, collK_eq hm1]

end Sarkozy.L20Cap
