module

public import Sarkozy.PositiveRoots.CoherentCubeFrame
public import Sarkozy.PositiveRoots.Chamber

/-! The physical chamber score as a bounded feature kernel on the uniform cube. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open Sarkozy.JointRows.StarOps (expect_finset_sum)
open scoped BigOperators

theorem chamberCoeff_eval_real (F : Feature → Feature → ℝ) :
    (∑ a, ∑ b, (chamberCoeff a b : ℝ) * F a b) =
      (dictionary39.map fun sc => (sc.2 : ℝ) *
        F (chamberFeature true sc.1) (chamberFeature false sc.1)).sum := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ratCast]
  have hc (l : List ℝ) : (l.sum : ℂ) = (l.map fun (r : ℝ) => (r : ℂ)).sum := by
    induction l with
    | nil => simp
    | cons r l ih => simp only [List.sum_cons, List.map_cons, Complex.ofReal_add, ih]
  rw [hc]
  simpa only [List.map_map, Function.comp_def, Complex.ofReal_mul,
    Complex.ofReal_ratCast] using chamberCoeff_eval (fun a b => (F a b : ℂ))

variable {p : ℕ} [Fact p.Prime]

theorem cubeFeature_chamber (sc : Support × ℚ) (hsc : sc ∈ dictionary39)
    (side : Bool) (z : ZMod p) (x : Fin 6 → ZMod p) :
    cubeFeature (chamberFeature side sc.1) z x =
      StarMatrix.psi (chamberSupport side sc.1) z x := by
  have hs : 2 ≤ (chamberSupport side sc.1).card := by
    have h := chamber_support_sizes sc hsc
    cases side <;> omega
  rw [chamberFeature, supportFeature_star _ hs]
  rfl

theorem cube_score_kernel (x y : Fin 6 → ZMod p) :
    coherentScore p dictionary39 (chamberConfiguration x y) =
      (rp p)⁻¹ * matrixFeatureKernel (FiniteLaw.uniform (ZMod p))
        (fun a b => (chamberCoeff a b : ℝ)) cubeFeature x y := by
  have hsum (z : ZMod p) :
      (∑ a, ∑ b, cubeFeature a z x * (chamberCoeff a b : ℝ) * cubeFeature b z y) =
        (dictionary39.map fun sc => (sc.2 : ℝ) *
          (StarMatrix.psi (chamberSupport true sc.1) z x *
            StarMatrix.psi (chamberSupport false sc.1) z y)).sum := by
    calc
      _ = ∑ a, ∑ b, (chamberCoeff a b : ℝ) * (cubeFeature a z x * cubeFeature b z y) :=
        sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
      _ = _ := by
        rw [chamberCoeff_eval_real]
        apply congrArg List.sum
        apply List.map_congr_left
        intro sc hsc
        rw [cubeFeature_chamber sc hsc, cubeFeature_chamber sc hsc]
  have swap (l : List (Support × ℚ)) :
      (FiniteLaw.uniform (ZMod p)).expect (fun z =>
        (l.map fun sc => (sc.2 : ℝ) *
          (StarMatrix.psi (chamberSupport true sc.1) z x *
            StarMatrix.psi (chamberSupport false sc.1) z y)).sum) =
        (l.map fun sc => (sc.2 : ℝ) *
          StarMatrix.tracePair (chamberSupport true sc.1) (chamberSupport false sc.1) x y).sum := by
    induction l with
    | nil => simp
    | cons sc l ih =>
      simp only [List.map_cons, List.sum_cons, FiniteLaw.expect_add, ih,
        FiniteLaw.expect_const_mul]
      congr 2
      rw [FiniteLaw.expect_uniform, ZMod.card]
      unfold StarMatrix.tracePair
      ring
  rw [score_chamber, matrixFeatureKernel]
  simp_rw [hsum]
  rw [swap, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc _
  ring

theorem cube_score_norm (hp3 : p % 4 = 3) (f g : (Fin 6 → ZMod p) → ℝ) :
    |kernelForm (cubeLaw p) (cubeLaw p)
      (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) f g| ≤
        (rp p / 3) * nrm (cubeLaw p) f * nrm (cubeLaw p) g := by
  have hM : NormLe (fun a b => (((chamberCoeff a b : ℝ)) : ℂ)) (1 / 3) := by
    simpa only [Complex.ofReal_ratCast] using chamberCoeff_norm
  have h := matrixFeature_norm (cubeLaw p) (FiniteLaw.uniform (ZMod p))
    (fun a b => (chamberCoeff a b : ℝ)) cubeFeature
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by positivity : 0 ≤ (p : ℝ)⁻¹)
    hM (cubeFeature_analysis hp3) f g
  have hr : rp p ≠ 0 := by exact_mod_cast (rp_ne_zero (p := p))
  have he : (rp p)⁻¹ * ((1 / 3 : ℝ) * (p : ℝ)⁻¹) = rp p / 3 := by
    rw [← rp_sq]
    field_simp
  have hk : (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) =
      fun x y => (rp p)⁻¹ * matrixFeatureKernel (FiniteLaw.uniform (ZMod p))
        (fun a b => (chamberCoeff a b : ℝ)) cubeFeature x y :=
    funext fun x => funext fun y => cube_score_kernel x y
  rw [hk, kernelForm_smul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (rp_nonneg (p := p)))]
  calc
    _ ≤ (rp p)⁻¹ * ((1 / 3 : ℝ) * (p : ℝ)⁻¹ * nrm (cubeLaw p) f * nrm (cubeLaw p) g) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (rp_nonneg (p := p)))
    _ = _ := by rw [← mul_assoc, ← mul_assoc, he]

end Sarkozy.PositiveRoots.CoherentFrame
