module

public import Sarkozy.PositiveRoots.CoherentMeanGeometry
public import Sarkozy.PositiveRoots.CoherentScoreNorm

/-! Cube orthogonality bounds all invariant means, and hence the core mean block. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.Labellings
open Sarkozy.JointRows.StarOps Sarkozy.FiveType.Blocks
open scoped BigOperators

def meanEmbedding (k : CoherentMean.Kind) : Fin (CoherentMean.size k) ↪ nonemptySets (Fin 6) :=
  ⟨fun i => ⟨meanSupport k i, mem_filter.mpr ⟨mem_univ _, meanSupport_nonempty k i⟩⟩,
    fun _ _ h => meanSupport_injective k (congrArg Subtype.val h)⟩

variable {p : ℕ} [Fact p.Prime]

theorem uniform_wOp_const {U : Type*} [Fintype U] [DecidableEq U]
    (hp3 : p % 4 = 3) (S : Finset U) (a : ℝ) (x : U → ZMod p) :
    wOp (fun _ : U => FiniteLaw.uniform (ZMod p)) S (fun _ => a) x = a * starMean S x := by
  unfold wOp
  simp_rw [uniform_phi hp3]
  rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_uniform, ZMod.card]
  unfold starMean starKer
  rw [← mul_sum]
  ring

theorem cube_means_synthesis (hp3 : p % 4 = 3) (u : nonemptySets (Fin 6) → ℝ) :
    (cubeLaw p).expect (fun x =>
      (∑ S : nonemptySets (Fin 6), u S * starMean S.val x) ^ 2) ≤
        (p : ℝ)⁻¹ * ∑ S, u S ^ 2 := by
  have hdens (i : Fin 6) (a : ZMod p) :
      (FiniteLaw.uniform (ZMod p)).weight a ≤ (1 : ℝ) / p := by
    simp only [FiniteLaw.uniform, ZMod.card, one_div, le_refl]
  have h := rawStar_synthesis_subtype (by omega : p ≠ 2)
    (fun _ : Fin 6 => FiniteLaw.uniform (ZMod p)) hdens (nonemptySets (Fin 6))
    (fun _ hS => (mem_filter.mp hS).2) (fun S _ => u S)
  simpa only [uniform_wOp_const hp3, FiveType.ip, ← pow_two, FiniteLaw.expect_const,
    one_mul, cubeLaw] using h

theorem cube_mean_block_synthesis (hp3 : p % 4 = 3) (k : CoherentMean.Kind)
    (u : Fin (CoherentMean.size k) → ℝ) :
    (cubeLaw p).expect (fun x => (∑ i, u i * starMean (meanSupport k i) x) ^ 2) ≤
      (p : ℝ)⁻¹ * ∑ i, u i ^ 2 := by
  let U := Function.extend (meanEmbedding k) u (fun _ => 0)
  have he (x : Fin 6 → ZMod p) :
      (∑ S : nonemptySets (Fin 6), U S * starMean S.val x) =
        ∑ i, u i * starMean (meanSupport k i) x :=
    sum_extend_zero (meanEmbedding k) u (fun S a => a * starMean S.val x)
      (by intro S; simp)
  have hn : (∑ S : nonemptySets (Fin 6), U S ^ 2) = ∑ i, u i ^ 2 :=
    sum_extend_zero (meanEmbedding k) u (fun _ a => a ^ 2) (by intro S; norm_num)
  have h := cube_means_synthesis hp3 U
  simp_rw [he, hn] at h
  exact h

theorem chamber_expect_nonneg (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hne : (injLabellings (ZMod p) L20Cap.G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (graphLaw L20Cap.G6 hne).expect f ≤ L20Cap.chamberCubeDensity p * (cubeLaw p).expect f := by
  unfold FiniteLaw.expect
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  rw [chamberCubeRatio_density hne x]
  have h := mul_le_mul_of_nonneg_right (chamberCubeRatio_le hp3 hp7 hne x)
    (mul_nonneg ((cubeLaw p).nonneg x) (hf x))
  simpa only [mul_assoc] using h

theorem chamber_mean_block_synthesis (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hne : (injLabellings (ZMod p) L20Cap.G6).Nonempty) (k : CoherentMean.Kind)
    (u : Fin (CoherentMean.size k) → ℝ) :
    (graphLaw L20Cap.G6 hne).expect
      (fun x => (∑ i, u i * starMean (meanSupport k i) x) ^ 2) ≤
        (L20Cap.chamberCubeDensity p * (p : ℝ)⁻¹) * ∑ i, u i ^ 2 := by
  calc
    _ ≤ L20Cap.chamberCubeDensity p * (cubeLaw p).expect
        (fun x => (∑ i, u i * starMean (meanSupport k i) x) ^ 2) :=
      chamber_expect_nonneg hp3 hp7 hne _ (fun _ => sq_nonneg _)
    _ ≤ L20Cap.chamberCubeDensity p * ((p : ℝ)⁻¹ * ∑ i, u i ^ 2) :=
      mul_le_mul_of_nonneg_left (cube_mean_block_synthesis hp3 k u)
        (L20Cap.chamberCubeDensity_pos hp7).le
    _ = _ := (mul_assoc _ _ _).symm

end Sarkozy.PositiveRoots.CoherentFrame
