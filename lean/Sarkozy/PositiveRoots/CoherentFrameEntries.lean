module

public import Sarkozy.PositiveRoots.CoherentFrameNumerics
public import Sarkozy.PositiveRoots.CoherentFrameDensity
public import Sarkozy.SpectralD.StarMatrixFeatures
public import Sarkozy.SpectralD.OverlapEntries

/-! Every distinct pair of the sixty-three coherent features has Gram norm at most `7r`. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.Labellings Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators ComplexConjugate symmDiff

local notation "𝒮₆" => StarMatrix.supports (Fin 6)

abbrev Feature := Fin 6 ⊕ 𝒮₆

theorem feature_card : Fintype.card Feature = 63 := by
  decide +kernel

theorem support_card (S : 𝒮₆) : 2 ≤ S.val.card :=
  (mem_filter.mp S.property).2

theorem support_nonempty (S : 𝒮₆) : S.val.Nonempty :=
  card_pos.mp (by have := support_card S; omega)

theorem card_le_six (S : Finset (Fin 6)) : S.card ≤ 6 := by
  simpa only [Fintype.card_fin] using card_le_univ S

theorem price_mono {z : ℂ} {C r a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : ‖z‖ ≤ C * a * b) (hC : C ≤ 7 * r) : ‖z‖ ≤ 7 * r * a * b :=
  hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC ha) hb)

variable {p : ℕ} [Fact p.Prime]

section Law

variable (hp : 4096 ≤ p) (hp3 : p % 4 = 3) (hW : WeilBound (ZMod p))
  (μ : (Fin 6 → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
  (hinv : ∀ s c x, s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
  (hinj : ∀ x k l, μ x ≠ 0 → k ≠ l → x k ≠ x l)

include hp hp3 hW hμ0 hμ1 hinv hinj

theorem vert_star_entry (i : Fin 6) (S : 𝒮₆) (h h' : ZMod p → ℂ)
    (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮₆ (Sum.inl i)) h x) *
      kerMap (featKer 𝒮₆ (Sum.inr S)) h' x)‖ ≤
        7 * rp p * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  have hp2 : p ≠ 2 := by omega
  by_cases hi : i ∈ S.val
  · exact price_mono (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (feat_vert_star_mem_entry hp2 hp3 hW μ hμ0 hμ1 hinv hinj 𝒮₆ i S
        (support_card S) hi h h' hh')
      (vertex_star_mem_price hp (support_card S) (card_le_six S.val))
  · exact price_mono (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (feat_vert_star_out_entry hp2 hp3 hW μ hμ0 hμ1 hinv hinj 𝒮₆ i S
        (support_nonempty S) hi h h' hh')
      (vertex_star_out_price hp (support_nonempty S).card_pos (card_le_six S.val))

variable (hD : ∀ j x t, μ x ≠ 0 → condLaw μ j x t ≤ 8 / (p : ℝ))

include hD

theorem star_star_entry (S T : 𝒮₆) (hST : S.val ≠ T.val)
    (h h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮₆ (Sum.inr S)) h x) *
      kerMap (featKer 𝒮₆ (Sum.inr T)) h' x)‖ ≤
        7 * rp p * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  obtain ⟨j, hj⟩ := symmDiff_nonempty.mpr hST
  exact price_mono (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (feat_star_star_entry (by omega) hp3 hW μ hμ0 hμ1 hinv hinj 𝒮₆ S T
      (support_nonempty S) (support_nonempty T) hST hj (hD j) h h' hh')
    (star_price hp (support_nonempty S).card_pos (card_le_six S.val)
      (support_nonempty T).card_pos (card_le_six T.val)
      (card_le_six _) (card_le_six _))

theorem feature_entry (a b : Feature) (hab : a ≠ b) (h h' : ZMod p → ℂ)
    (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮₆ a) h x) *
      kerMap (featKer 𝒮₆ b) h' x)‖ ≤
        7 * rp p * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  rcases a with i | S <;> rcases b with j | T
  · have hij : i ≠ j := fun e => hab (congrArg Sum.inl e)
    exact price_mono (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (feat_vert_vert_entry (by omega) hp3 μ hμ0 hμ1 hinv hinj 𝒮₆ hij h h' hh')
      (vertex_price hp)
  · exact vert_star_entry hp hp3 hW μ hμ0 hμ1 hinv hinj i T h h' hh'
  · rw [Overlap.norm_sum_conj_swap]
    convert vert_star_entry hp hp3 hW μ hμ0 hμ1 hinv hinj j S h' h hh using 1
    ring
  · exact star_star_entry hp hp3 hW μ hμ0 hμ1 hinv hinj hD S T
      (fun e => hab (congrArg Sum.inr (Subtype.ext e))) h h' hh'

end Law

theorem graph_feature_entry (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (G : OrientedGraph (Fin 6))
    (hne : (injLabellings (ZMod p) G).Nonempty)
    (hdeg : ∀ j, nbrCount G (univ.erase j) j ≤ 2)
    (a b : Feature) (hab : a ≠ b) (h h' : ZMod p → ℂ)
    (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (graphWeight G hne x : ℂ) * (conj (kerMap (featKer 𝒮₆ a) h x) *
      kerMap (featKer 𝒮₆ b) h' x)‖ ≤
        7 * rp p * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  obtain ⟨h0, h1, hi, hj⟩ := graphWeight_hyps G hne
  exact feature_entry hp hp3 hW (graphWeight G hne) h0 h1 hi hj
    (graph_pivot_density hW (by omega) G hne hdeg) a b hab h h' hh hh'

end Sarkozy.PositiveRoots.CoherentFrame
