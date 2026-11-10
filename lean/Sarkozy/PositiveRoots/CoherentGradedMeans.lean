module

public import Sarkozy.PositiveRoots.CoherentProductInputs

/-! The even-degree Weil improvement in the coherent core-star mean prices. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD

variable {p : ℕ} [Fact p.Prime]

noncomputable def gradedStarPrice (p k : ℕ) : ℝ :=
  ((k : ℝ) - 1 - (1 + (-1) ^ k) / 2) * rp p +
    ((1 + (-1) ^ k) / 2) * (p : ℝ)⁻¹

theorem abs_starMean_graded {U : Type*} [DecidableEq U]
    (hW : Labellings.WeilBound (ZMod p)) {S : Finset U} (hS : S.Nonempty)
    (x : U → ZMod p) (hx : Set.InjOn x S) :
    |starMean S x| ≤ gradedStarPrice p S.card := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [starMean_eq_starTrace S x hx, Spectral.starTrace_eq_rootSum, ZMod.card,
    abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have h := Labellings.abs_rootSum_le hW (hS.image x)
  rw [card_image_of_injOn hx, ZMod.card] at h
  have he : gradedStarPrice p S.card * (p : ℝ) =
      Labellings.subsetBound (Real.sqrt p) S.card := by
    unfold gradedStarPrice Labellings.subsetBound rp
    calc
      _ = ((S.card : ℝ) - 1 - (1 + (-1) ^ S.card) / 2) *
          ((p : ℝ) / Real.sqrt p) + (1 + (-1) ^ S.card) / 2 := by field_simp
      _ = _ := by rw [Real.div_sqrt]
  rw [he]
  exact h

theorem gradedStarPrice_one (p : ℕ) : gradedStarPrice p 1 = 0 := by
  norm_num [gradedStarPrice]

theorem gradedStarPrice_two (p : ℕ) : gradedStarPrice p 2 = (p : ℝ)⁻¹ := by
  norm_num [gradedStarPrice]

theorem gradedStarPrice_three (p : ℕ) : gradedStarPrice p 3 = 2 * rp p := by
  norm_num [gradedStarPrice]

theorem gradedStarPrice_four (p : ℕ) : gradedStarPrice p 4 = 2 * rp p + (p : ℝ)⁻¹ := by
  norm_num [gradedStarPrice]

omit [Fact p.Prime] in
theorem gradedStarPrice_core_nonneg {S : Finset (Fin 4)} (hS : S.Nonempty) :
    0 ≤ gradedStarPrice p S.card := by
  have h1 := hS.card_pos
  have h4 : S.card ≤ 4 := card_le_univ S
  have hr := rp_nonneg (p := p)
  interval_cases hc : S.card <;>
    simp only [gradedStarPrice_one, gradedStarPrice_two, gradedStarPrice_three,
      gradedStarPrice_four] <;> positivity

end Sarkozy.PositiveRoots.CoherentFrame
