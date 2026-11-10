module

public import Sarkozy.PositiveRoots.FiniteMatrixBound

/-! A finite matrix lower bound restricts to any principal submatrix. -/

@[expose] public section

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {U K : Type*} [Fintype U] [Fintype K]

theorem sum_extend_zero {A R : Type*} [Zero A] [AddCommMonoid R] (e : K ↪ U) (x : K → A)
    (f : U → A → R) (hf : ∀ i, f i 0 = 0) :
    (∑ i, f i (Function.extend e x (fun _ => 0) i)) = ∑ a, f (e a) (x a) := by
  classical
  calc
    _ = ∑ i ∈ univ.map e, f i (Function.extend e x (fun _ => 0) i) := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      have hnot : ¬ ∃ a, e a = i := by simpa only [mem_map, mem_univ, true_and] using hi
      rw [Function.extend_apply' _ _ _ hnot, hf]
    _ = _ := by simp only [sum_map, e.injective.extend_apply]

theorem energy_extend_zero (e : K ↪ U) (x : K → ℂ) :
    (∑ i, ‖Function.extend e x (fun _ => 0) i‖ ^ 2) = ∑ a, ‖x a‖ ^ 2 :=
  sum_extend_zero e x (fun _ z => ‖z‖ ^ 2) (by intro i; simp)

theorem qform_extend_zero (A : U → U → ℂ) (e : K ↪ U) (x : K → ℂ) :
    qform A (Function.extend e x (fun _ => 0)) =
      qform (fun a b => A (e a) (e b)) x := by
  unfold qform
  rw [sum_extend_zero e x
    (fun i z => ∑ j, conj z * A i j * Function.extend e x (fun _ => 0) j)
    (by intro i; simp)]
  apply sum_congr rfl
  intro a _
  exact sum_extend_zero e x (fun j z => conj (x a) * A (e a) j * z)
    (by intro j; simp)

theorem lower_bound_submatrix (A : U → U → ℂ) (e : K ↪ U) {g : ℝ}
    (hA : ∀ x, -g * ∑ i, ‖x i‖ ^ 2 ≤ (qform A x).re) (x : K → ℂ) :
    -g * ∑ a, ‖x a‖ ^ 2 ≤ (qform (fun a b => A (e a) (e b)) x).re := by
  have h := hA (Function.extend e x (fun _ => 0))
  rwa [energy_extend_zero, qform_extend_zero] at h

end Sarkozy.PositiveRoots
