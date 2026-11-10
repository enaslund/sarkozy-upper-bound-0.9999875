module

public import Sarkozy.PositiveRoots.CoherentTraceRows
public import Sarkozy.JointRows.RawStarFrame
public import Sarkozy.JointRows.PaleyCx
public import Sarkozy.SpectralC.MatrixKernel

/-! The complete raw character frame on the six-coordinate uniform cube. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD
open Sarkozy.JointRows.StarOps Sarkozy.FiveType.Blocks
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def cubeLaw (p : ℕ) [Fact p.Prime] : FiniteLaw (Fin 6 → ZMod p) :=
  blockLaw (fun _ : Fin 6 => FiniteLaw.uniform (ZMod p))

theorem cubeLaw_weight (x : Fin 6 → ZMod p) :
    (cubeLaw p).weight x = (p : ℝ)⁻¹ ^ 6 := by
  simp only [cubeLaw, blockLaw, FiniteLaw.uniform, ZMod.card, prod_const,
    card_univ, Fintype.card_fin]

theorem uniform_phi (hp3 : p % 4 = 3) (z a : ZMod p) :
    phi (FiniteLaw.uniform (ZMod p)) z a = chiRe (z - a) := by
  unfold phi mchi
  rw [FiniteLaw.expect_uniform, JointRows.PaleyGauss.sum_chiR_sub hp3, zero_div, sub_zero]
  rfl

noncomputable def cubeFeature : Feature → ZMod p → (Fin 6 → ZMod p) → ℝ
  | Sum.inl _, _, _ => 0
  | Sum.inr S, z, x => StarMatrix.psi S.val z x

theorem cubeFeature_adj_vertex (f : (Fin 6 → ZMod p) → ℝ) (i : Fin 6) (z : ZMod p) :
    matrixFeatureAdj (cubeLaw p) cubeFeature f (Sum.inl i) z = 0 := by
  simp only [matrixFeatureAdj, cubeFeature, zero_mul, FiniteLaw.expect_const]

theorem cubeFeature_adj_star (hp3 : p % 4 = 3) (f : (Fin 6 → ZMod p) → ℝ)
    (S : StarMatrix.supports (Fin 6)) (z : ZMod p) :
    matrixFeatureAdj (cubeLaw p) cubeFeature f (Sum.inr S) z =
      wStar (fun _ => FiniteLaw.uniform (ZMod p)) S.val f z := by
  unfold matrixFeatureAdj wStar
  apply (cubeLaw p).expect_congr
  intro x
  simp only [cubeFeature, StarMatrix.psi, uniform_phi hp3]
  ring

theorem cubeFeature_analysis (hp3 : p % 4 = 3) (f : (Fin 6 → ZMod p) → ℝ) :
    (∑ a : Feature, (FiniteLaw.uniform (ZMod p)).expect
      (fun z => matrixFeatureAdj (cubeLaw p) cubeFeature f a z ^ 2)) ≤
        (p : ℝ)⁻¹ * (cubeLaw p).expect (fun x => f x ^ 2) := by
  have hp2 : p ≠ 2 := by omega
  have hdens (i : Fin 6) (a : ZMod p) :
      (FiniteLaw.uniform (ZMod p)).weight a ≤ (1 : ℝ) / p := by
    simp only [FiniteLaw.uniform, ZMod.card, one_div, le_refl]
  have hS (S : Finset (Fin 6)) (hS : S ∈ StarMatrix.supports (Fin 6)) : S.Nonempty :=
    support_nonempty ⟨S, hS⟩
  have h := rawStar_analysis hp2 (fun _ : Fin 6 => FiniteLaw.uniform (ZMod p))
    (by norm_num : (0 : ℝ) ≤ 1) hdens (StarMatrix.supports (Fin 6)) hS f
  rw [Fintype.sum_sum_type]
  simp only [cubeFeature_adj_vertex, zero_pow (by decide : 2 ≠ 0),
    FiniteLaw.expect_const, sum_const_zero, zero_add, cubeFeature_adj_star hp3]
  rw [← sum_coe_sort (StarMatrix.supports (Fin 6)) (fun S =>
    FiveType.ip (FiniteLaw.uniform (ZMod p))
      (wStar (fun _ => FiniteLaw.uniform (ZMod p)) S f)
      (wStar (fun _ => FiniteLaw.uniform (ZMod p)) S f))] at h
  simpa only [one_mul, FiveType.ip, ← pow_two, cubeLaw] using h

end Sarkozy.PositiveRoots.CoherentFrame
