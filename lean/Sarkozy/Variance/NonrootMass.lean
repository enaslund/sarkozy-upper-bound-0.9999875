module

public import Sarkozy.PartV.MiddleReference

/-!
# The nonroot mass of a middle block (`eq:record:nonroot-mass`)

`paper/sections/22_variance.tex`, step (C) of the proof of `lem:record:restoration` and
`eq:record:nonroot-mass`: the reference of a middle block is the root plus a nonnegative measure
`𝓜_𝔅` of mass `h_𝔅`,
`μ̃_𝔅 = Π_{L,𝔅} + 𝓜_𝔅`, `h_𝔅 = μ̃_𝔅(1) - 1
  = (3w_D + 2w_S + v_L) r + (6w_R + 3v_D + 2v_S) r² + (2w_C + 6v_R) r³ + 2v_C r⁴`.

This is stated for V1's middle reference `PartV.middleTilde` (any field laws, any weights with
`w_L = 1`, any `r ≥ 0`):
* `middleTilde_split`: `μ̃_𝔅 = Π_{L,𝔅} + 𝓜_𝔅`, the root being the two-layer component of type `L`
  (coefficient `w_L r⁰ = 1`), and `𝓜_𝔅` (`middleNonroot`) the sum of the other weighted
  components;
* `middleNonroot_nonneg`, `middleNonroot_mass`: `𝓜_𝔅 ≥ 0` and `𝓜_𝔅(1) = P(r) - 1`;
* `nonroot_mass_eq`: **`eq:record:nonroot-mass`**, `P(r) - 1` in the paper's form;
* `middleReference_split`: `μ_𝔅 = (1 + h_𝔅)⁻¹ (Π_{L,𝔅} + 𝓜_𝔅)`, the hypothesis `hmix` of
  `Variance.restoration` for a single block.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.PartV

namespace Sarkozy.Variance

/-- The index of the root component: two-layer, type `L`, its only pattern. -/
def rootIdx : MidIdx := (true, ⟨PType.L, ()⟩)

theorem midCoeff_root (W : MiddleWeights) (r : ℝ) : midCoeff W r rootIdx = 1 := by
  simp [rootIdx, midCoeff, W.w_L, PType.deg]

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The nonroot part `𝓜_𝔅` of `μ̃_𝔅`: the sum of the weighted components other than the root. -/
noncomputable def middleNonroot (F : MiddleFieldLaws X) (W : MiddleWeights) (r : ℝ) :
    ((Slot → X) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i ∈ univ.erase rootIdx, midCoeff W r i • signedIntegral (midComponent F i).weight

/-- **Step (C) of `lem:record:restoration`**: `μ̃_𝔅 = Π_{L,𝔅} + 𝓜_𝔅`. -/
theorem middleTilde_split (F : MiddleFieldLaws X) (W : MiddleWeights) (r : ℝ) :
    middleTilde F W r = signedIntegral (midComponent F rootIdx).weight + middleNonroot F W r := by
  unfold middleTilde tildeMeasure middleNonroot
  rw [← add_sum_erase _ _ (mem_univ rootIdx), midCoeff_root, one_smul]

/-- `𝓜_𝔅` is a nonnegative measure. -/
theorem middleNonroot_nonneg (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r)
    (f : (Slot → X) → ℝ) (hf : ∀ z, 0 ≤ f z) : 0 ≤ middleNonroot F W r f := by
  unfold middleNonroot
  rw [LinearMap.sum_apply]
  refine sum_nonneg fun i _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul, ← FiniteLaw.expect_eq_signedIntegral]
  exact mul_nonneg (midCoeff_nonneg W hr i) ((midComponent F i).expect_nonneg hf)

/-- The mass of `𝓜_𝔅` is `P(r) - 1`. -/
theorem middleNonroot_mass (F : MiddleFieldLaws X) (W : MiddleWeights) (r : ℝ) :
    middleNonroot F W r (fun _ => 1) = midPoly W r - 1 := by
  have h := middleTilde_split F W r
  have hm : middleTilde F W r (fun _ => 1) = midPoly W r := by
    rw [middleTilde, tildeMeasure_mass, sum_midCoeff]
  have hroot : signedIntegral (midComponent F rootIdx).weight (fun _ => 1) = 1 := by
    rw [← FiniteLaw.expect_eq_signedIntegral, FiniteLaw.expect_const]
  rw [h, LinearMap.add_apply, hroot] at hm
  linarith

/-- **`eq:record:nonroot-mass`**: `h_𝔅 = P(r) - 1 = (3w_D + 2w_S + v_L) r +
(6w_R + 3v_D + 2v_S) r² + (2w_C + 6v_R) r³ + 2v_C r⁴`. -/
theorem nonroot_mass_eq (W : MiddleWeights) (r : ℝ) :
    midPoly W r - 1 = (3 * W.w .D + 2 * W.w .S + W.v .L) * r +
      (6 * W.w .R + 3 * W.v .D + 2 * W.v .S) * r ^ 2 + (2 * W.w .C + 6 * W.v .R) * r ^ 3 +
      2 * W.v .C * r ^ 4 := by
  rw [midPoly_eq]
  ring

/-- The normalized middle reference is `μ_𝔅 = (1 + h_𝔅)⁻¹ (Π_{L,𝔅} + 𝓜_𝔅)` with
`h_𝔅 = P(r) - 1 ≥ 0`: the hypothesis `hmix` of `restoration` for a single block. -/
theorem middleReference_split (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ}
    (hr : 0 ≤ r) :
    signedIntegral (middleReference F W hr).weight =
        (1 + (midPoly W r - 1))⁻¹ •
          (signedIntegral (midComponent F rootIdx).weight + middleNonroot F W r) ∧
      0 ≤ midPoly W r - 1 := by
  refine ⟨?_, by linarith [one_le_midPoly W hr]⟩
  rw [middleReference_eq, middleTilde_split]
  congr 1
  ring

end Sarkozy.Variance
