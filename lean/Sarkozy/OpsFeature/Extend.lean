module

public import Sarkozy.OpsFeature.UnitTable

@[expose] public section

/-!
# Lifts over a sub-alphabet of labels (`lem:oct24:mask-schur`(a), (c))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(c): a diagonal witness gives weights to
the tensor features that are centres or arms (W2's `Feat n k`: the fold labels `0..3`, the matching
labels `0, 1`) and is "extended by any nonnegative weights to the features that are neither
centres nor arms" (the fold label `4`, the matching label `2`).

**`liftMap_extend`**: the lift, by tables `C'` on the full alphabet, of the extension by zero
`extendD ι D` of a matrix `D` on a sub-alphabet `ι : L → L'` is the lift of `D` by the restricted
tables `restrictT ι C'`. So the operator `liftMap CU D` of `hdom_of_table_paley(_blocks)` (with
`CU = restrictT castSucc C'`) is the lift `Lift(D)` of the diagonal witness extended by zero, with
the unit tables `C'` on all five (three) labels (OPS-S's `foldUnit`, `matchUnit`). No injectivity
of `ι` is needed for the identity.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

section Extend

variable {X : Type*} [Fintype X] [DecidableEq X] {L L' O : X → Type*} [∀ b, Fintype (L b)]
  [∀ b, Fintype (L' b)] [∀ b, DecidableEq (L' b)]

/-- The extension of a matrix on the words of a sub-alphabet `ι b : L b → L' b`. -/
def extendD (ι : ∀ b, L b → L' b) (D : Matrix (∀ b, L b) (∀ b, L b) ℝ) :
    Matrix (∀ b, L' b) (∀ b, L' b) ℝ := fun v' w' =>
  ∑ v, ∑ w, (if (fun b => ι b (v b)) = v' then 1 else 0) *
    (if (fun b => ι b (w b)) = w' then 1 else 0) * D v w

/-- The tables restricted to the sub-alphabet. -/
def restrictT (ι : ∀ b, L b → L' b) (C' : ∀ b, Matrix (L' b × O b) (L' b × O b) ℝ) (b : X) :
    Matrix (L b × O b) (L b × O b) ℝ := fun P Q => C' b (ι b P.1, P.2) (ι b Q.1, Q.2)

/-- **The lift of the extension by zero is the lift by the restricted tables.** -/
theorem liftMap_extend (ι : ∀ b, L b → L' b) (C' : ∀ b, Matrix (L' b × O b) (L' b × O b) ℝ)
    (D : Matrix (∀ b, L b) (∀ b, L b) ℝ) :
    liftMap C' (extendD ι D) = liftMap (restrictT ι C') D := by
  ext x y
  simp only [liftMap, extendD, restrictT, sum_mul]
  set F : (∀ b, L' b) → (∀ b, L' b) → (∀ b, L b) → (∀ b, L b) → ℝ := fun v' w' v w =>
    (if (fun b => ι b (v b)) = v' then 1 else 0) * (if (fun b => ι b (w b)) = w' then 1 else 0) *
      D v w * ∏ b, C' b (v' b, x b) (w' b, y b) with hF
  calc ∑ v', ∑ w', ∑ v, ∑ w, F v' w' v w = ∑ v', ∑ v, ∑ w', ∑ w, F v' w' v w :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ v, ∑ v', ∑ w', ∑ w, F v' w' v w := sum_comm
    _ = ∑ v, ∑ v', ∑ w, ∑ w', F v' w' v w :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ v, ∑ w, ∑ v', ∑ w', F v' w' v w := sum_congr rfl fun _ _ => sum_comm
    _ = _ := by
        refine sum_congr rfl fun v _ => sum_congr rfl fun w _ => ?_
        have e : ∀ v' w', F v' w' v w = if (fun b => ι b (w b)) = w' then
            (if (fun b => ι b (v b)) = v' then
              D v w * ∏ b, C' b (v' b, x b) (w' b, y b) else 0) else 0 := by
          intro v' w'
          simp only [hF]
          split_ifs <;> ring
        simp only [e, Finset.sum_ite_eq, mem_univ, ↓reduceIte]

omit [∀ b, Fintype (L' b)] in
/-- With injective `ι`, the extension of a diagonal matrix is diagonal, with the same weights on
the image words. -/
theorem extendD_diagonal [∀ b, DecidableEq (L b)] (ι : ∀ b, L b → L' b)
    (hι : ∀ b, Function.Injective (ι b)) (d : (∀ b, L b) → ℝ)
    (v w : ∀ b, L b) :
    extendD ι (diagonal d) (fun b => ι b (v b)) (fun b => ι b (w b)) =
      if v = w then d v else 0 := by
  have hinj : ∀ u u' : ∀ b, L b, ((fun b => ι b (u b)) = fun b => ι b (u' b)) ↔ u = u' :=
    fun u u' => ⟨fun h => funext fun b => hι b (congrFun h b), fun h => h ▸ rfl⟩
  simp only [extendD, hinj, diagonal_apply, mul_ite, mul_zero, ite_mul, one_mul, zero_mul]
  rw [sum_eq_single v (fun u _ hu => sum_eq_zero fun u' _ => by
    split_ifs with h1 h2 <;> simp_all) (by simp)]
  rw [sum_eq_single w (fun u' _ hu' => by simp [hu']) (by simp)]
  by_cases h : v = w
  · subst h; simp
  · simp [h]

end Extend

end Sarkozy.OpsFeature
