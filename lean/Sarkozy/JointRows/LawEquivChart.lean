module

public import Sarkozy.JointRows.LawEquiv
public import Sarkozy.JointRows.RowsA

/-! Normalized kernels and their form bounds commute with a change of coordinates. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem lawEquiv_kone (μ : FiniteLaw X) (e : X ≃ Y) (K : Y → Y → ℝ) (x : X) :
    kone (lawEquiv μ e) K (e x) = kone μ (fun a b => K (e a) (e b)) x := by
  unfold kone
  rw [← e.sum_comp]
  simp only [lawEquiv, Equiv.symm_apply_apply]

theorem lawEquiv_kone' (μ : FiniteLaw X) (e : X ≃ Y) (K : Y → Y → ℝ) (y : X) :
    kone' (lawEquiv μ e) K (e y) = kone' μ (fun a b => K (e a) (e b)) y := by
  unfold kone'
  rw [← e.sum_comp]
  simp only [lawEquiv, Equiv.symm_apply_apply]

theorem lawEquiv_mass (μ : FiniteLaw X) (e : X ≃ Y) (K : Y → Y → ℝ) :
    RowsA.mass (lawEquiv μ e) K = RowsA.mass μ (fun a b => K (e a) (e b)) :=
  lawEquiv_kf μ e K (fun _ => 1) (fun _ => 1)

theorem lawEquiv_chart (μ : FiniteLaw X) (e : X ≃ Y) (K : Y → Y → ℝ) (x y : X) :
    RowsA.chartKernel (lawEquiv μ e) K (e x) (e y) =
      RowsA.chartKernel μ (fun a b => K (e a) (e b)) x y := by
  simp only [RowsA.chartKernel, RowsA.dens1, RowsA.dens2, lawEquiv_mass,
    lawEquiv_kone, lawEquiv_kone']

theorem formBound_of_lawEquiv (μ : FiniteLaw X) (e : X ≃ Y) (K : Y → Y → ℝ) {s : ℝ}
    (h : FormBound (lawEquiv μ e) K s) :
    FormBound μ (fun x y => K (e x) (e y)) s := by
  intro f g
  have hh := h (fun y => f (e.symm y)) (fun y => g (e.symm y))
  simpa only [lawEquiv_kf, lawEquiv_nrm, Equiv.symm_apply_apply] using hh

end Sarkozy.JointRows
