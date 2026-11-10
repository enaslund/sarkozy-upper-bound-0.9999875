module

public import Sarkozy.PartV.CoherentRawKernel
public import Sarkozy.PartV.CoherentCancellationBound
public import Sarkozy.PartV.CoherentUnrestricted

/-!
# The coherent collision price, including intersections

The ordinary score price holds off the complete-cancellation event. On that
event the unrestricted score bound and the proved matching mass apply.
-/

@[expose] public section

namespace Sarkozy.PartV.CubePins

open Finset

theorem mass_mul_split {X : Type*} [Fintype X]
    (w f : X → ℝ) (hw : ∀ x, 0 ≤ w x) (E F : X → Prop)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg : ∀ x, E x → ¬F x → f x ≤ A) (hb : ∀ x, f x ≤ B) :
    mass (fun x => w x * f x) E ≤ A * mass w E + B * mass w F := by
  classical
  unfold mass
  simp only [sum_filter, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases he : E x
  · by_cases hf : F x
    · simp only [he, hf, ite_true]
      have h := mul_le_mul_of_nonneg_left (hb x) (hw x)
      nlinarith [mul_nonneg hA (hw x)]
    · simp only [he, hf, ite_true, ite_false, mul_zero, add_zero]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hg x he hf) (hw x)
  · by_cases hf : F x
    · simp only [he, hf, ite_true, ite_false, mul_zero, zero_add]
      exact mul_nonneg hB (hw x)
    · simp only [he, hf, ite_false, mul_zero, add_zero, le_refl]

end Sarkozy.PartV.CubePins

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime]

def Collision (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p) : Prop :=
  Function.Injective b ∧ ¬Function.Injective (joinHalves isLayer a b)

theorem score_off_exceptional (hW : WeilBound (ZMod p)) (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p)
    (hb : Function.Injective b) (he : ¬Exceptional isLayer a b) :
    |coherentScore p dictionary39 (joinHalves isLayer a b)| ≤ 14 + 1 / Real.sqrt p := by
  apply dictionary39_partial_cancellation_bound hW
  intro sc hsc hc
  exact he ⟨hb, sc, hsc, hc⟩

theorem coherentWeight_bound_of_score (u η : ℚ) (x : Vertex → ZMod p) (B : ℝ)
    (hB : |coherentScore p dictionary39 x| ≤ B) :
    coherentWeight p dictionary39 u η x ≤ (η : ℝ) + (1 + |(u : ℝ)| * B) ^ 2 := by
  have ha : |1 + (u : ℝ) * coherentScore p dictionary39 x| ≤ 1 + |(u : ℝ)| * B := by
    refine (abs_add_le _ _).trans ?_
    simpa only [abs_one, abs_mul] using
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hB (abs_nonneg (u : ℝ)))
  unfold coherentWeight
  apply add_le_add le_rfl
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ha 2

theorem collision_weight_mass (hW : WeilBound (ZMod p)) (isLayer : Bool)
    (a : Half isLayer true → ZMod p)
    (w : (Half isLayer false → ZMod p) → ℝ) (hw : ∀ b, 0 ≤ w b)
    (u η : ℚ) (hη : 0 ≤ η) (D P : ℝ)
    (hD : CubePins.mass w (Collision isLayer a) ≤ D)
    (hP : CubePins.mass w (Exceptional isLayer a) ≤ P) :
    CubePins.mass (fun b => w b * coherentWeight p dictionary39 u η (joinHalves isLayer a b))
      (Collision isLayer a) ≤
        ((η : ℝ) + (1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p)) ^ 2) * D +
        ((η : ℝ) + (1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p)) ^ 2) * P := by
  have hηR : (0 : ℝ) ≤ η := by exact_mod_cast hη
  have hgood : 0 ≤ (η : ℝ) + (1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p)) ^ 2 := by positivity
  have hbad : 0 ≤ (η : ℝ) + (1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p)) ^ 2 := by positivity
  refine (CubePins.mass_mul_split w _ hw (Collision isLayer a) (Exceptional isLayer a)
    _ _ hgood hbad (fun b hb he => coherentWeight_bound_of_score u η _ _
      (score_off_exceptional hW isLayer a b hb.1 he))
    (fun b => (dictionary39_unrestricted_weight u η _).2)).trans ?_
  exact add_le_add (mul_le_mul_of_nonneg_left hD hgood) (mul_le_mul_of_nonneg_left hP hbad)

theorem raw_collision_weight_mass (hW : WeilBound (ZMod p)) (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (ha : Function.Injective a)
    (ν : FiniteLaw (Half isLayer false → ZMod p))
    (u η : ℚ) (hη : 0 ≤ η) (D Dcube : ℝ) (hDc : 0 ≤ Dcube)
    (hν : ∀ b, ν.weight b ≤ Dcube / (p : ℝ) ^ 6)
    (hD : CubePins.mass (fun b => ν.weight b * rawCrossKernel isLayer (joinHalves isLayer a b))
      (Collision isLayer a) ≤ D) :
    CubePins.mass (fun b => ν.weight b * rawCrossKernel isLayer (joinHalves isLayer a b) *
      coherentWeight p dictionary39 u η (joinHalves isLayer a b)) (Collision isLayer a) ≤
        ((η : ℝ) + (1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p)) ^ 2) * D +
        ((η : ℝ) + (1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p)) ^ 2) *
          (144 * (if isLayer then 4096 else 65536) * Dcube / (p : ℝ) ^ 3) := by
  apply collision_weight_mass hW isLayer a _
    (fun b => mul_nonneg (ν.nonneg b) (rawCrossKernel_nonneg isLayer _)) u η hη _ _ hD
  exact exceptional_kernel_mass isLayer a ha ν _ _ Dcube
    (by cases isLayer <;> norm_num) hDc
    (fun b => rawCrossKernel_nonneg isLayer _) (fun b => rawCrossKernel_le isLayer _) hν

end Sarkozy.PartV.CoherentDictionary
