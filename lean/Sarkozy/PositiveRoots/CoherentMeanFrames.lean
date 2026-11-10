module

public import Sarkozy.PositiveRoots.CoherentCubeMeans
public import Sarkozy.PositiveRoots.CoherentPrivateCompression

/-! Actual core and mixed invariant-mean frames on the chamber graph law. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.Labellings Sarkozy.L20Cap
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem mixed_mean_fixed_selected (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    (c : Fin 4 → ZMod p) (hc : Function.Injective c) (u : Fin 10 → ℝ) :
    (privateCube p).expect (fun b =>
      (∑ i, u i * starMean (meanSupport .mixed i) (emb c (b 0, b 1))) ^ 2) ≤
        ((p : ℝ)⁻¹ * (1 + 42 * rp p + 56 * (p : ℝ)⁻¹)) * ∑ i, u i ^ 2 := by
  let U := Function.extend mixedEmbedding u (fun _ => 0)
  have he (b : Fin 2 → ZMod p) :
      (∑ B : PrivateSupport, ∑ A : CoreSupport, U (A, B) * mixedMean A B c b) =
        ∑ i, u i * starMean (meanSupport .mixed i) (emb c (b 0, b 1)) := by
    calc
      _ = ∑ ab : CoreSupport × PrivateSupport, U ab * mixedMean ab.1 ab.2 c b := by
        rw [Fintype.sum_prod_type, sum_comm]
      _ = ∑ i, u i * mixedMean (mixedIndex i).1 (mixedIndex i).2 c b :=
        sum_extend_zero mixedEmbedding u (fun ab a => a * mixedMean ab.1 ab.2 c b)
          (by intro ab; simp)
      _ = _ := by simp only [mixedMean_physical]
  have hn : (∑ B : PrivateSupport, ∑ A : CoreSupport, U (A, B) ^ 2) = ∑ i, u i ^ 2 := by
    calc
      _ = ∑ ab : CoreSupport × PrivateSupport, U ab ^ 2 := by
        rw [Fintype.sum_prod_type, sum_comm]
      _ = _ := sum_extend_zero mixedEmbedding u (fun _ a => a ^ 2) (by intro ab; norm_num)
  have h := mixedMean_fixed_frame hW hp3 c hc U
  simp_rw [he, hn] at h
  exact h

noncomputable def mixedMeanPrice (p : ℕ) : ℝ :=
  privateCompression p * (1 + 42 * rp p + 56 * (p : ℝ)⁻¹)

omit [Fact p.Prime] in
theorem mixedMeanPrice_nonneg (hp6 : 6 ≤ p) : 0 ≤ mixedMeanPrice p := by
  have hp : (6 : ℝ) ≤ p := by exact_mod_cast hp6
  unfold mixedMeanPrice privateCompression
  exact mul_nonneg (div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith)))
    (by have := rp_nonneg (p := p); positivity)

theorem chamber_mixed_mean_synthesis (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    (hp6 : 6 ≤ p) (hne : (injLabellings (ZMod p) G6).Nonempty) (u : Fin 10 → ℝ) :
    (graphLaw G6 hne).expect (fun x => (∑ i, u i * starMean (meanSupport .mixed i) x) ^ 2) ≤
      (mixedMeanPrice p * (p : ℝ)⁻¹) * ∑ i, u i ^ 2 := by
  have hne' := hne
  obtain ⟨z, hz⟩ := hne'
  let : Nonempty (CoreT (ZMod p)) := ⟨(toHalf z hz).1⟩
  let : Nonempty (PairT (ZMod p)) := ⟨(toHalf z hz).2⟩
  have h6 : 6 ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using hp6
  rw [graphLaw_eq_halfLaw h6 hne]
  have h := halfLaw_private_compression hp6
    (fun c b => (∑ i, u i * starMean (meanSupport .mixed i) (emb c.val (b 0, b 1))) ^ 2)
    (fun _ _ => sq_nonneg _)
    (fun c => mixed_mean_fixed_selected hW hp3 c.val c.property.1 u)
  change (halfLaw h6).expect
      (fun x => (∑ i, u i * starMean (meanSupport .mixed i) (labels x)) ^ 2) ≤ _ at h
  calc
    _ ≤ privateCompression p *
        (((p : ℝ)⁻¹ * (1 + 42 * rp p + 56 * (p : ℝ)⁻¹)) * ∑ i, u i ^ 2) := h
    _ = _ := by unfold mixedMeanPrice; ring

theorem chamber_core_mean_analysis (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hne : (injLabellings (ZMod p) G6).Nonempty) (f : (Fin 6 → ZMod p) → ℝ) :
    (∑ i : Fin 5, ((graphLaw G6 hne).expect (fun x =>
      starMean (meanSupport .core i) x * f x)) ^ 2) ≤
        (chamberCubeDensity p * (p : ℝ)⁻¹) * (graphLaw G6 hne).expect (fun x => f x ^ 2) :=
  finiteFrame_analysis (graphLaw G6 hne) (fun i x => starMean (meanSupport .core i) x)
    (mul_nonneg (chamberCubeDensity_pos hp7).le (by positivity))
    (chamber_mean_block_synthesis hp3 hp7 hne .core) f

theorem chamber_mixed_mean_analysis (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    (hp6 : 6 ≤ p) (hne : (injLabellings (ZMod p) G6).Nonempty)
    (f : (Fin 6 → ZMod p) → ℝ) :
    (∑ i : Fin 10, ((graphLaw G6 hne).expect (fun x =>
      starMean (meanSupport .mixed i) x * f x)) ^ 2) ≤
        (mixedMeanPrice p * (p : ℝ)⁻¹) * (graphLaw G6 hne).expect (fun x => f x ^ 2) :=
  finiteFrame_analysis (graphLaw G6 hne) (fun i x => starMean (meanSupport .mixed i) x)
    (mul_nonneg (mixedMeanPrice_nonneg hp6) (by positivity))
    (chamber_mixed_mean_synthesis hW hp3 hp6 hne) f

end Sarkozy.PositiveRoots.CoherentFrame
