module

public import Sarkozy.Structured.MainTerm

/-!
# Step 1 of `lem:record:density-dc`: telescoping

`lem:record:density-dc` (`paper/sections/08_scale_comparison.tex`), Step 1. For fixed
`(ω, z)` and inputs `a_v = g_v(z_v, ·)`, `b_v = g̃_v(z_v, ·)` that agree outside the set `C`
of changed slots, `Λ((a_v)_v) - Λ((b_v)_v) = ∑_{v ∈ C} Λ(Y^{(v)})`. Each `Y^{(v)}`
carries:
* `a_v - b_v` at `v`;
* `b_w` at the slots of a set `T_v ∌ v`, the slots already changed;
* `a_w` at the other slots.

The paper orders the changed slots as `v_1, …, v_k`, with `T_{v_i} = {v_j : j < i}`.
Here the sets `T_v` come from an induction on `C`. They depend only on `C`, not on the
inputs.

* `hybrid a b v T`: the inputs of `Y^{(v)}`.
* `multilinear_sub_single`: the case of one slot (multilinearity).
* `multilinear_sub_eq_sum_hybrid`: the telescoping identity.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.DensityDC

variable {X : Type*}

/-- The inputs of the telescoping term at `v`: `a_v - b_v` at `v`, `b` on `T`, `a`
elsewhere. -/
def hybrid (a b : Slot → X → ℝ) (v : Slot) (T : Finset Slot) : Slot → X → ℝ :=
  fun w => if w = v then a v - b v else if w ∈ T then b w else a w

theorem hybrid_self (a b : Slot → X → ℝ) (v : Slot) (T : Finset Slot) :
    hybrid a b v T v = a v - b v := by
  unfold hybrid
  rw [ite_eq_left rfl]

theorem hybrid_ne (a b : Slot → X → ℝ) {v w : Slot} (T : Finset Slot) (hw : w ≠ v) :
    hybrid a b v T w = if w ∈ T then b w else a w := by
  unfold hybrid
  rw [ite_eq_right hw]

/-- Two inputs that differ only at `u`: `Λ(a) - Λ(c) = Λ(a with a_u - c_u at u)`. -/
theorem multilinear_sub_single (L : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) (a c : Slot → X → ℝ) (u : Slot)
    (hac : ∀ w, w ≠ u → a w = c w) :
    multilinearIntegral L a - multilinearIntegral L c =
      multilinearIntegral L (hybrid a c u ∅) := by
  unfold multilinearIntegral
  rw [← map_sub]
  congr 1
  funext z
  change (∏ v, a v (z v)) - ∏ v, c v (z v) = ∏ v, hybrid a c u ∅ v (z v)
  rw [← mul_prod_erase univ (fun v => a v (z v)) (mem_univ u),
    ← mul_prod_erase univ (fun v => c v (z v)) (mem_univ u),
    ← mul_prod_erase univ (fun v => hybrid a c u ∅ v (z v)) (mem_univ u)]
  have h1 : ∏ w ∈ univ.erase u, c w (z w) = ∏ w ∈ univ.erase u, a w (z w) :=
    prod_congr rfl fun w hw => by rw [hac w (ne_of_mem_erase hw)]
  have h2 : ∏ w ∈ univ.erase u, hybrid a c u ∅ w (z w) = ∏ w ∈ univ.erase u, a w (z w) :=
    prod_congr rfl fun w hw => by
      rw [hybrid_ne a c ∅ (ne_of_mem_erase hw), ite_eq_right (notMem_empty w)]
  rw [h1, h2, hybrid_self]
  change _ = (a u (z u) - c u (z u)) * _
  ring

/-- **Telescoping** (`lem:record:density-dc`, Step 1): for every set `C` of slots there are
sets `T_v ∌ v` such that `Λ(a) - Λ(b) = ∑_{v ∈ C} Λ(hybrid a b v T_v)` for all inputs
`a, b` that agree outside `C`. -/
theorem multilinear_sub_eq_sum_hybrid (L : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) (C : Finset Slot) :
    ∃ T : Slot → Finset Slot, (∀ v, v ∉ T v) ∧ ∀ a b : Slot → X → ℝ,
      (∀ w, w ∉ C → a w = b w) →
      multilinearIntegral L a - multilinearIntegral L b =
        ∑ v ∈ C, multilinearIntegral L (hybrid a b v (T v)) := by
  induction C using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => ∅, fun v => notMem_empty v, ?_⟩
    intro a b hab
    have : a = b := funext fun w => hab w (notMem_empty w)
    subst this
    simp
  | insert u C hu ih =>
    obtain ⟨T, hT, hsum⟩ := ih
    refine ⟨fun v => if v = u then ∅ else insert u (T v), ?_, ?_⟩
    · intro v
      dsimp only
      by_cases hv : v = u
      · rw [ite_eq_left hv]
        exact notMem_empty v
      · rw [ite_eq_right hv, mem_insert, not_or]
        exact ⟨hv, hT v⟩
    · intro a b hab
      set c : Slot → X → ℝ := fun w => if w = u then b u else a w with hcdef
      have hac : ∀ w, w ≠ u → a w = c w := by
        intro w hw
        rw [hcdef]
        dsimp only
        rw [ite_eq_right hw]
      have hcb : ∀ w, w ∉ C → c w = b w := by
        intro w hw
        by_cases hwu : w = u
        · rw [hwu, hcdef]
          dsimp only
          rw [ite_eq_left rfl]
        · rw [hcdef]
          dsimp only
          rw [ite_eq_right hwu]
          exact hab w (by rw [mem_insert, not_or]; exact ⟨hwu, hw⟩)
      have hsplit : multilinearIntegral L a - multilinearIntegral L b =
          (multilinearIntegral L a - multilinearIntegral L c) +
            (multilinearIntegral L c - multilinearIntegral L b) := by ring
      rw [hsplit, multilinear_sub_single L a c u hac, hsum c b hcb, sum_insert hu]
      congr 1
      · dsimp only
        rw [ite_eq_left rfl]
        congr 1
        funext w
        by_cases hwu : w = u
        · rw [hwu, hybrid_self, hybrid_self]
          have : c u = b u := by
            rw [hcdef]
            dsimp only
            rw [ite_eq_left rfl]
          rw [this]
        · rw [hybrid_ne _ _ _ hwu, hybrid_ne _ _ _ hwu, ite_eq_right (notMem_empty w),
            ite_eq_right (notMem_empty w)]
      · apply sum_congr rfl
        intro v hv
        have hvu : v ≠ u := fun h => hu (h ▸ hv)
        dsimp only
        rw [ite_eq_right hvu]
        congr 1
        funext w
        by_cases hwv : w = v
        · rw [hwv, hybrid_self, hybrid_self, ← hac v hvu]
        · rw [hybrid_ne _ _ _ hwv, hybrid_ne _ _ _ hwv]
          by_cases hwu : w = u
          · rw [hwu, ite_eq_left (mem_insert_self u (T v))]
            by_cases huT : u ∈ T v
            · rw [ite_eq_left huT]
            · rw [ite_eq_right huT, hcdef]
              dsimp only
              rw [ite_eq_left rfl]
          · by_cases hwT : w ∈ T v
            · rw [ite_eq_left hwT, ite_eq_left (mem_insert_of_mem hwT)]
            · rw [ite_eq_right hwT, ite_eq_right (by
                rw [mem_insert, not_or]; exact ⟨hwu, hwT⟩), ← hac w hwu]

end Sarkozy.DensityDC
