module

public import Sarkozy.JointRows.ChartVariance

/-! Correlation depends only on the normalized joint law, including after reindexing. -/

@[expose] public section

namespace Sarkozy.JointRows

open Sarkozy.FiveType

variable {X Y : Type*} [Fintype X] [Fintype Y]

def KernelCorr (μ : FiniteLaw X) (K : X → X → ℝ) (ρ : ℝ) : Prop :=
  ∀ f g, |kf μ (covKernel μ K) f g| ≤
    ρ * Real.sqrt (wvar μ (margL μ K) f) * Real.sqrt (wvar μ (margR μ K) g)

theorem covariance_moments (μ : FiniteLaw X) (K : X → X → ℝ) (f g : X → ℝ) :
    kf μ (covKernel μ K) f g = kf μ K f g / RowsA.mass μ K -
      (kf μ K f (fun _ => 1) / RowsA.mass μ K) *
        (kf μ K (fun _ => 1) g / RowsA.mass μ K) := by
  rw [show covKernel μ K = RowsA.chartKernel μ K from rfl, chart_form,
    dens1_moment, dens2_moment]

theorem variance_left_moments (μ : FiniteLaw X) (K : X → X → ℝ) (f : X → ℝ) :
    wvar μ (margL μ K) f = kf μ K (fun x => f x ^ 2) (fun _ => 1) / RowsA.mass μ K -
      (kf μ K f (fun _ => 1) / RowsA.mass μ K) ^ 2 := by
  change wvar μ (RowsA.dens1 μ K) f = _
  rw [wvar, dens1_moment, dens1_moment]

theorem variance_right_moments (μ : FiniteLaw X) (K : X → X → ℝ) (g : X → ℝ) :
    wvar μ (margR μ K) g = kf μ K (fun _ => 1) (fun y => g y ^ 2) / RowsA.mass μ K -
      (kf μ K (fun _ => 1) g / RowsA.mass μ K) ^ 2 := by
  change wvar μ (RowsA.dens2 μ K) g = _
  rw [wvar, dens2_moment, dens2_moment]

theorem KernelCorr.transport {μ : FiniteLaw X} {ν : FiniteLaw Y}
    {K : X → X → ℝ} {T : Y → Y → ℝ} {ρ : ℝ} (h : KernelCorr μ K ρ) (φ : X → Y)
    (hm : ∀ f g, kf ν T f g / RowsA.mass ν T =
      kf μ K (fun x => f (φ x)) (fun x => g (φ x)) / RowsA.mass μ K) :
    KernelCorr ν T ρ := by
  intro f g
  have hh := h (fun x => f (φ x)) (fun x => g (φ x))
  simp only [covariance_moments, variance_left_moments, variance_right_moments] at hh ⊢
  simpa only [hm] using hh

theorem KernelCorr.mono {μ : FiniteLaw X} {K : X → X → ℝ} {ρ ρ' : ℝ}
    (h : KernelCorr μ K ρ) (hρ : ρ ≤ ρ') : KernelCorr μ K ρ' := by
  intro f g
  exact (h f g).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hρ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

theorem exact_moment_left (μ : FiniteLaw X) (K : X → X → ℝ)
    (hK : ExactMarginals μ K) (f : X → ℝ) : kf μ K f (fun _ => 1) = μ.expect f := by
  rw [kf_one_right]
  apply expect_congr_supp
  intro x hx
  simp only [hK.1 x hx, mul_one]

theorem exact_moment_right (μ : FiniteLaw X) (K : X → X → ℝ)
    (hK : ExactMarginals μ K) (g : X → ℝ) : kf μ K (fun _ => 1) g = μ.expect g := by
  rw [kf_one_left]
  apply expect_congr_supp
  intro y hy
  simp only [hK.2 y hy, one_mul]

theorem KernelCorr.normBound {μ : FiniteLaw X} {K : X → X → ℝ} {ρ : ℝ}
    (h : KernelCorr μ K ρ) (hρ : 0 ≤ ρ) (hK : ExactMarginals μ K) : NormBound μ K ρ := by
  have hmass : RowsA.mass μ K = 1 := by
    rw [RowsA.mass, exact_moment_left μ K hK, FiniteLaw.expect_const]
  intro f g
  have hh := h f g
  simp only [covariance_moments, variance_left_moments, variance_right_moments,
    hmass, div_one, exact_moment_left μ K hK, exact_moment_right μ K hK] at hh
  apply hh.trans
  have hn (u : X → ℝ) :
      Real.sqrt (μ.expect (fun x => u x ^ 2) - μ.expect u ^ 2) ≤ nrm μ u := by
    unfold nrm ip
    simp only [← sq]
    exact Real.sqrt_le_sqrt (sub_le_self _ (sq_nonneg _))
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hn f) hρ) (hn g)
    (Real.sqrt_nonneg _) (mul_nonneg hρ (FiveType.nrm_nonneg _ _))

end Sarkozy.JointRows
