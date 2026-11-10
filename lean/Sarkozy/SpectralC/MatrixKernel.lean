module

public import Sarkozy.SpectralC.MatrixNormAverage
public import Sarkozy.JointRows.StarPure
public import Sarkozy.Cuts.Actual

/-! Matrix-valued feature kernels and their finite-law operator bounds. -/

@[expose] public section

namespace Sarkozy.SpectralC

open Finset Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.JointRows.StarOps (expect_swap expect_finset_sum)
open scoped BigOperators

variable {I X Z : Type*} [Fintype I] [Fintype X] [Fintype Z]

noncomputable def matrixFeatureKernel (ν : FiniteLaw Z) (C : I → I → ℝ)
    (W : I → Z → X → ℝ) (x y : X) : ℝ :=
  ν.expect (fun z => ∑ a, ∑ b, W a z x * C a b * W b z y)

noncomputable def matrixFeatureAdj (μ : FiniteLaw X) (W : I → Z → X → ℝ)
    (f : X → ℝ) (a : I) (z : Z) : ℝ := μ.expect (fun x => W a z x * f x)

theorem matrixFeature_factor (μ : FiniteLaw X) (ν : FiniteLaw Z)
    (C : I → I → ℝ) (W : I → Z → X → ℝ) (f g : X → ℝ) :
    kernelForm μ μ (matrixFeatureKernel ν C W) f g =
      ν.expect (fun z => ∑ a, ∑ b,
        matrixFeatureAdj μ W f a z * C a b * matrixFeatureAdj μ W g b z) := by
  have inner (x : X) :
      μ.expect (fun y => matrixFeatureKernel ν C W x y * g y) =
        ν.expect (fun z => ∑ a, ∑ b, W a z x * C a b * matrixFeatureAdj μ W g b z) := by
    unfold matrixFeatureKernel
    simp_rw [← FiniteLaw.expect_mul_const]
    rw [expect_swap]
    apply ν.expect_congr
    intro z
    simp_rw [sum_mul, expect_finset_sum, mul_assoc, FiniteLaw.expect_const_mul]
    rfl
  rw [kernelForm_apply]
  simp_rw [inner, ← FiniteLaw.expect_const_mul]
  rw [expect_swap]
  apply ν.expect_congr
  intro z
  simp_rw [mul_sum, expect_finset_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  calc
    _ = μ.expect (fun x => (W a z x * f x) *
        (C a b * matrixFeatureAdj μ W g b z)) := μ.expect_congr fun x => by ring
    _ = _ := by rw [FiniteLaw.expect_mul_const]; exact (mul_assoc _ _ _).symm

theorem matrixFeature_norm (μ : FiniteLaw X) (ν : FiniteLaw Z)
    (C : I → I → ℝ) (W : I → Z → X → ℝ) {lam κ : ℝ}
    (hlam : 0 ≤ lam) (hκ : 0 ≤ κ)
    (hM : NormLe (fun a b => (C a b : ℂ)) lam)
    (hF : ∀ f, (∑ a, ν.expect (fun z => matrixFeatureAdj μ W f a z ^ 2)) ≤
      κ * μ.expect (fun x => f x ^ 2)) (f g : X → ℝ) :
    |kernelForm μ μ (matrixFeatureKernel ν C W) f g| ≤
      lam * κ * nrm μ f * nrm μ g := by
  rw [matrixFeature_factor]
  have h := normLe_average hlam hM ν (matrixFeatureAdj μ W f) (matrixFeatureAdj μ W g)
  have hf := Real.sqrt_le_sqrt (hF f)
  have hg := Real.sqrt_le_sqrt (hF g)
  calc
    _ ≤ lam * Real.sqrt (∑ a, ν.expect (fun z => matrixFeatureAdj μ W f a z ^ 2)) *
        Real.sqrt (∑ b, ν.expect (fun z => matrixFeatureAdj μ W g b z ^ 2)) := h
    _ ≤ lam * Real.sqrt (κ * μ.expect (fun x => f x ^ 2)) *
        Real.sqrt (κ * μ.expect (fun x => g x ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hf hlam) hg (Real.sqrt_nonneg _)
        (mul_nonneg hlam (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.sqrt_mul hκ, Real.sqrt_mul hκ]
      unfold nrm Recentering.ip
      simp only [← pow_two]
      calc
        _ = lam * (Real.sqrt κ ^ 2) * Real.sqrt (μ.expect (fun x => f x ^ 2)) *
            Real.sqrt (μ.expect (fun x => g x ^ 2)) := by ring
        _ = _ := by rw [Real.sq_sqrt hκ]

end Sarkozy.SpectralC
