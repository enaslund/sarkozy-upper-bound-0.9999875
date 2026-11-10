module

public import Sarkozy.Labellings.ClassThree

/-!
# Densities of the class-three conditional laws (`lem:record:class-three`(iii))

`paper/sections/20_middle_reference.tex`.

Under `λ_p(G_{F,2})` an F-configuration is drawn uniformly. Given the middle pair `(u, u')`,
the conditional law of the outer pair `(x₀, x₀')` is therefore proportional to its number of
completions `N(x₀, x₀')`. Relative to the uniform law on the admissible pairs, its density is
`N(x₀, x₀') · #pairs / ∑ N`.

* `density_mem_of_ratio`: positive weights whose pairwise ratios are at most `R` have normalized
  densities in `[R⁻¹, R]`. Pure algebra.
* `class_three_iii_density`: hence the density of the outer pairs lies in
  `[R₂⁻¹, R₂]`, `R₂ = (q − 3)(q − 7)/((q − 11)(q − 15))`, by `class_three_iii_ratio`.
* `one_layer_density`: for one layer, the count of a single source `x₀` is the number of
  out-neighbours of `x₀` other than `u`, which lies in `[(q − 3)/2, (q − 1)/2]`. The densities
  lie in `[R₁⁻¹, R₁]`, `R₁ = (q − 1)/(q − 3)`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.TraceMixing

/-- **Pairwise ratio bounds give density bounds.** For weights `w` on a nonempty finite set `S`
with `w > 0` and `w x ≤ R · w y` for all `x, y ∈ S`, the density `w x · |S| / ∑ w` lies in
`[R⁻¹, R]`. -/
theorem density_mem_of_ratio {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (w : ι → ℝ)
    (hw : ∀ x ∈ S, 0 < w x) {R : ℝ} (hR : ∀ x ∈ S, ∀ y ∈ S, w x ≤ R * w y) (x : ι)
    (hx : x ∈ S) :
    R⁻¹ ≤ w x * S.card / ∑ y ∈ S, w y ∧ w x * S.card / ∑ y ∈ S, w y ≤ R := by
  have hsum : 0 < ∑ y ∈ S, w y := sum_pos hw hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hwx := hw x hx
  have hRpos : 0 < R := by
    have h := hR x hx x hx
    nlinarith
  constructor
  · -- `∑ w ≤ R · |S| · w x`
    have hle : ∑ y ∈ S, w y ≤ ∑ _y ∈ S, R * w x := sum_le_sum fun y hy => hR y hy x hx
    rw [sum_const, nsmul_eq_mul] at hle
    rw [inv_eq_one_div, div_le_div_iff₀ hRpos hsum]
    nlinarith
  · -- `|S| · w x ≤ R · ∑ w`
    have hle : ∑ _y ∈ S, w x ≤ ∑ y ∈ S, R * w y := sum_le_sum fun y hy => hR x hx y hy
    rw [sum_const, nsmul_eq_mul, ← mul_sum] at hle
    rw [div_le_iff₀ hsum]
    nlinarith

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- **`lem:record:class-three`(iii), densities of the two-layer conditional law.** Fix the middle
labels `u, u'` and a nonempty set `S` of admissible outer pairs, each with distinct entries
(in the paper: the ordered distinct pairs avoiding `{u, u'}`). For `q ≡ 3 (mod 4)`, `q ≥ 19`,
the normalized completion counts `N(x) · |S| / ∑_S N` lie in `[R₂⁻¹, R₂]`, where
`R₂ = (q − 3)(q − 7)/((q − 11)(q − 15))`. -/
theorem class_three_iii_density (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h19 : 19 ≤ Fintype.card F) (u u' : F) (S : Finset (F × F)) (hS : S.Nonempty)
    (hSd : ∀ x ∈ S, x.1 ≠ x.2) (x : F × F) (hx : x ∈ S) :
    let R₂ : ℝ := ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 7) /
      (((Fintype.card F : ℝ) - 11) * ((Fintype.card F : ℝ) - 15))
    let N : F × F → ℝ := fun y => ((completions u u' y.1 y.2).card : ℝ)
    R₂⁻¹ ≤ N x * S.card / ∑ y ∈ S, N y ∧ N x * S.card / ∑ y ∈ S, N y ≤ R₂ := by
  intro R₂ N
  have hq : (19 : ℝ) ≤ Fintype.card F := by exact_mod_cast h19
  have hA : 0 < ((Fintype.card F : ℝ) - 11) * ((Fintype.card F : ℝ) - 15) := by nlinarith
  have hpos : ∀ y ∈ S, 0 < N y := by
    intro y hy
    obtain ⟨h1, _⟩ := class_three_iii_bounds hF h3 h19 (hSd y hy) u u'
    have hA' : (0 : ℤ) < ((Fintype.card F : ℤ) - 11) * ((Fintype.card F : ℤ) - 15) := by
      have : (19 : ℤ) ≤ Fintype.card F := by exact_mod_cast h19
      nlinarith
    have : (0 : ℤ) < ((completions u u' y.1 y.2).card : ℤ) := by linarith
    show (0 : ℝ) < ((completions u u' y.1 y.2).card : ℝ)
    exact_mod_cast this
  have hratio : ∀ y ∈ S, ∀ z ∈ S, N y ≤ R₂ * N z := by
    intro y hy z hz
    have h := class_three_iii_ratio hF h3 h19 (hSd y hy) (hSd z hz) u u' u u'
    have hR : ((((Fintype.card F : ℤ) - 11) * ((Fintype.card F : ℤ) - 15) *
        ((completions u u' y.1 y.2).card : ℤ) : ℤ) : ℝ) ≤
        ((((Fintype.card F : ℤ) - 3) * ((Fintype.card F : ℤ) - 7) *
        ((completions u u' z.1 z.2).card : ℤ) : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at hR
    show ((completions u u' y.1 y.2).card : ℝ) ≤
      ((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 7) /
        (((Fintype.card F : ℝ) - 11) * ((Fintype.card F : ℝ) - 15)) *
          ((completions u u' z.1 z.2).card : ℝ)
    rw [div_mul_eq_mul_div, le_div_iff₀ hA]
    linarith
  exact density_mem_of_ratio S hS N hpos hratio x hx

/-- **One layer** (`lem:record:class-three`(iii), last sentence). For `q ≡ 3 (mod 4)`, the number
of out-neighbours of `x₀` other than `u` satisfies `q − 3 ≤ 2 N ≤ q − 1`. Hence the normalized
counts over a nonempty set of sources lie in `[R₁⁻¹, R₁]`, `R₁ = (q − 1)/(q − 3)`, for
`q ≥ 7`. -/
theorem one_layer_density (hF : ringChar F ≠ 2) (h7 : 7 ≤ Fintype.card F) (u : F)
    (S : Finset F) (hS : S.Nonempty) (x : F) (hx : x ∈ S) :
    let N : F → ℝ := fun y => ((univ.filter fun c => χ (c - y) = 1 ∧ c ≠ u).card : ℝ)
    ((Fintype.card F : ℝ) - 1) / ((Fintype.card F : ℝ) - 3) ≥ 0 ∧
    (((Fintype.card F : ℝ) - 1) / ((Fintype.card F : ℝ) - 3))⁻¹ ≤ N x * S.card / ∑ y ∈ S, N y ∧
      N x * S.card / ∑ y ∈ S, N y ≤ ((Fintype.card F : ℝ) - 1) / ((Fintype.card F : ℝ) - 3) := by
  intro N
  have hq : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast h7
  have hbounds : ∀ y : F, ((Fintype.card F : ℝ) - 3) / 2 ≤ N y ∧
      N y ≤ ((Fintype.card F : ℝ) - 1) / 2 := by
    intro y
    have hout := card_out hF y
    have hsplit := card_sdiff_add_card_inter (univ.filter fun c => χ (c - y) = 1)
      ({u} : Finset F)
    have hset : (univ.filter fun c => χ (c - y) = 1 ∧ c ≠ u) =
        (univ.filter fun c => χ (c - y) = 1) \ {u} := by
      ext c
      simp
    have hint : ((univ.filter fun c => χ (c - y) = 1) ∩ {u}).card ≤ 1 :=
      (card_le_card inter_subset_right).trans (card_singleton u).le
    have hNy : N y = (((univ.filter fun c => χ (c - y) = 1) \ {u}).card : ℝ) := by
      show (((univ.filter fun c => χ (c - y) = 1 ∧ c ≠ u)).card : ℝ) = _
      rw [hset]
    have hsplitR : ((((univ.filter fun c => χ (c - y) = 1) \ {u}).card : ℤ)) +
        (((univ.filter fun c => χ (c - y) = 1) ∩ {u}).card : ℤ) =
        ((univ.filter fun c => χ (c - y) = 1).card : ℤ) := by exact_mod_cast hsplit
    have hintZ : (((univ.filter fun c => χ (c - y) = 1) ∩ {u}).card : ℤ) ≤ 1 := by
      exact_mod_cast hint
    have hint0 : (0 : ℤ) ≤ (((univ.filter fun c => χ (c - y) = 1) ∩ {u}).card : ℤ) :=
      Nat.cast_nonneg _
    have hlow : (Fintype.card F : ℤ) - 3 ≤
        2 * ((((univ.filter fun c => χ (c - y) = 1) \ {u}).card : ℤ)) := by linarith
    have hhigh : 2 * ((((univ.filter fun c => χ (c - y) = 1) \ {u}).card : ℤ)) ≤
        (Fintype.card F : ℤ) - 1 := by linarith
    have hlowR : (Fintype.card F : ℝ) - 3 ≤
        2 * ((((univ.filter fun c => χ (c - y) = 1) \ {u}).card : ℝ)) := by exact_mod_cast hlow
    have hhighR : 2 * ((((univ.filter fun c => χ (c - y) = 1) \ {u}).card : ℝ)) ≤
        (Fintype.card F : ℝ) - 1 := by exact_mod_cast hhigh
    rw [hNy]
    constructor <;> linarith
  have h3pos : (0 : ℝ) < (Fintype.card F : ℝ) - 3 := by linarith
  have hpos : ∀ y ∈ S, 0 < N y := by
    intro y _
    have := (hbounds y).1
    have : (0 : ℝ) < ((Fintype.card F : ℝ) - 3) / 2 := by positivity
    linarith
  have hratio : ∀ y ∈ S, ∀ z ∈ S,
      N y ≤ ((Fintype.card F : ℝ) - 1) / ((Fintype.card F : ℝ) - 3) * N z := by
    intro y _ z _
    obtain ⟨_, hy2⟩ := hbounds y
    obtain ⟨hz1, _⟩ := hbounds z
    rw [div_mul_eq_mul_div, le_div_iff₀ h3pos]
    nlinarith
  refine ⟨div_nonneg (by linarith) h3pos.le, density_mem_of_ratio S hS N hpos hratio x hx⟩

end Sarkozy.TraceMixing
