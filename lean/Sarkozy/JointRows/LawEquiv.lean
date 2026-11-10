module

public import Sarkozy.JointRows.CollBridge

/-! Exact change of coordinates for finite laws and kernel forms. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def lawEquiv (μ : FiniteLaw X) (e : X ≃ Y) : FiniteLaw Y where
  weight y := μ.weight (e.symm y)
  nonneg y := μ.nonneg _
  total := by rw [e.symm.sum_comp μ.weight]; exact μ.total

theorem lawEquiv_expect (μ : FiniteLaw X) (e : X ≃ Y) (f : Y → ℝ) :
    (lawEquiv μ e).expect f = μ.expect (fun x => f (e x)) := by
  unfold FiniteLaw.expect
  change (∑ y, μ.weight (e.symm y) * f y) = _
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem lawEquiv_nrm (μ : FiniteLaw X) (e : X ≃ Y) (f : Y → ℝ) :
    nrm (lawEquiv μ e) f = nrm μ (fun x => f (e x)) := by
  unfold nrm ip
  rw [lawEquiv_expect]

theorem lawEquiv_kf (μ : FiniteLaw X) (e : X ≃ Y)
    (K : Y → Y → ℝ) (f g : Y → ℝ) :
    kf (lawEquiv μ e) K f g = kf μ (fun x y => K (e x) (e y))
      (fun x => f (e x)) (fun x => g (e x)) := by
  unfold kf
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [← e.sum_comp]
  simp only [lawEquiv, Equiv.symm_apply_apply]

theorem formBound_lawEquiv (μ : FiniteLaw X) (e : X ≃ Y) (K : Y → Y → ℝ) {s : ℝ}
    (h : FormBound μ (fun x y => K (e x) (e y)) s) :
    FormBound (lawEquiv μ e) K s := by
  intro f g
  rw [lawEquiv_kf, lawEquiv_nrm, lawEquiv_nrm]
  exact h _ _

theorem perpBound_lawEquiv (μ : FiniteLaw X) (e : X ≃ Y) (K : Y → Y → ℝ) {s : ℝ}
    (h : PerpBound μ (fun x y => K (e x) (e y)) s) :
    PerpBound (lawEquiv μ e) K s := by
  intro f g hf hg
  rw [lawEquiv_kf, lawEquiv_nrm, lawEquiv_nrm]
  exact h _ _ (by rwa [lawEquiv_expect] at hf) (by rwa [lawEquiv_expect] at hg)

end Sarkozy.JointRows
