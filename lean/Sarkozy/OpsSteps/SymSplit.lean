module

public import Sarkozy.RecordExpansion.SharpFirst

@[expose] public section

/-!
# One category of the sharp-first expansion, separated (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `lem:orbit-coupon`(i) ("consider the category of the
count vector `e_s`: exactly one record difference, of tag `s` … Its bound in `lem:bracket-energy`
is `(d e^{U₀} + o(1)) C_X Y`, the term of `e_s` in `e^{U₀} 𝔗(d, v)`; the other categories keep their
bounds"); `paper/sections/10_comparison_lemmas.tex`, `lem:sharp-first`.

The summation `abs_sum_le_tagSeries` of `lem:sharp-first` bounds all categories (count vectors `k`)
together by `K e^P 𝔗(d, v)`. The orbit coupon improves one category. Here:

* **`abs_sum_le_tagSeries_split`**: `|∑_{σ≠∅} T_σ| ≤ |∑_{σ ∈ k₀} T_σ| +
  K e^P (𝔗(d, v) − 𝔗_{k₀}(d, v)) + ∑_{σ ∉ k₀} r_σ`, with the per-term bounds only off the category
  `k₀` (`𝔗_{k₀} = tagMin k₀`, the term of `k₀` in the series);
* `tagMin_single`: the term of `e_s` (one difference of tag `s`) is `d_s`;
* **`tagSeries_sub_mono`**: `𝔗(d, v) − 𝔗_{k₀}(d, v)` is nondecreasing in `d`, `v` (the other terms).
-/

open Finset
open scoped BigOperators Nat

namespace Sarkozy.OpsSteps

open Sarkozy.RecordExpansion

section Series

variable {Tag : Type*} [Fintype Tag] [DecidableEq Tag]

/-- **The term of `e_s` in the tag series is `d_s`.** -/
theorem tagMin_single (d v : Tag → ℝ) (s : Tag) : tagMin d v (Pi.single s 1) = d s := by
  have hts : tagsOf (Pi.single s 1 : Tag → ℕ) = {s} := by
    ext j
    by_cases hj : j = s
    · subst hj; simp [tagsOf]
    · simp [tagsOf, hj, Pi.single_apply]
  have hne : (tagsOf (Pi.single s 1 : Tag → ℕ)).Nonempty := by rw [hts]; exact singleton_nonempty s
  unfold tagMin
  rw [dite_eq_left hne]
  simp only [hts, inf'_singleton]
  unfold tagTerm
  have hnum : ∏ j', (if j' = s then d j' else v j') ^ (Pi.single s 1 : Tag → ℕ) j' = d s := by
    rw [prod_eq_single s (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hden : ∏ j', (((Pi.single s 1 : Tag → ℕ) j')! : ℝ) = 1 := by
    refine prod_eq_one fun j _ => ?_
    by_cases hj : j = s
    · subst hj; simp
    · simp [hj]
  rw [hnum, hden, div_one]

/-- **The tag series without one term is nondecreasing** in `d`, `v`. -/
theorem tagSeries_sub_mono {d v d' v' : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (hdd : ∀ j, d j ≤ d' j) (hvv : ∀ j, v j ≤ v' j) (k₀ : Tag → ℕ) :
    tagSeries d v - tagMin d v k₀ ≤ tagSeries d' v' - tagMin d' v' k₀ := by
  have hd' : ∀ j, 0 ≤ d' j := fun j => (hd j).trans (hdd j)
  have hv' : ∀ j, 0 ≤ v' j := fun j => (hv j).trans (hvv j)
  have hs := tagMin_summable hd hv
  have hs' := tagMin_summable hd' hv'
  unfold tagSeries
  rw [hs.tsum_eq_add_tsum_ite k₀, hs'.tsum_eq_add_tsum_ite k₀, add_sub_cancel_left,
    add_sub_cancel_left]
  refine (hs.update k₀ 0).tsum_le_tsum (fun k => ?_) (hs'.update k₀ 0)
    |>.trans_eq' ?_ |>.trans_eq ?_
  · by_cases hk : k = k₀
    · simp [Function.update, hk]
    · simp only [Function.update, hk, ↓reduceDIte]
      exact tagMin_mono hd hv hdd hvv k
  · refine tsum_congr fun k => ?_
    by_cases hk : k = k₀ <;> simp [Function.update, hk]
  · refine tsum_congr fun k => ?_
    by_cases hk : k = k₀ <;> simp [Function.update, hk]

end Series

section Split

variable {J : Type*} [Fintype J] [DecidableEq J] {I : J → Type*} [∀ b, Fintype (I b)]
  [∀ b, DecidableEq (I b)] {Tag : Type*} [Fintype Tag] [DecidableEq Tag]

/-- **The summation of `lem:sharp-first` with one category separated**: if every nonempty choice
outside the category `k₀` satisfies `|T_σ| ≤ K wt_j(σ) + r_σ` for every tag `j` present in it, then
`|∑_{σ≠∅} T_σ| ≤ |∑_{σ ∈ k₀} T_σ| + K e^P (𝔗(d, v) − 𝔗_{k₀}(d, v)) + ∑_{σ ∉ k₀} r_σ`. -/
theorem abs_sum_le_tagSeries_split (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) {K : ℝ}
    (hK : 0 ≤ K) (term r : (∀ b, Option (I b)) → ℝ) (k₀ : Tag → ℕ)
    (hterm : ∀ σ, σ ≠ (fun _ => none) → countVec tag σ ≠ k₀ → ∀ j, 1 ≤ countVec tag σ j →
      |term σ| ≤ K * tagWeight tag d v p j σ + r σ) :
    |∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none), term σ| ≤
      |∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec tag σ = k₀), term σ| +
        K * Real.exp (∑ b, p b) * (tagSeries (tagTotal tag d) (tagTotal tag v) -
          tagMin (tagTotal tag d) (tagTotal tag v) k₀) +
        ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec tag σ ≠ k₀), r σ := by
  set ne := univ.filter (fun σ : (∀ b, Option (I b)) => σ ≠ fun _ => none) with hne
  set rest := ne.filter (fun σ => countVec tag σ ≠ k₀) with hrest
  set Kset := (rest.image (countVec tag)) with hKset
  have hd' : ∀ j, 0 ≤ tagTotal tag d j :=
    fun j => sum_nonneg fun b _ => sum_nonneg fun i _ => by split_ifs <;> simp [hd b i]
  have hv' : ∀ j, 0 ≤ tagTotal tag v j :=
    fun j => sum_nonneg fun b _ => sum_nonneg fun i _ => by split_ifs <;> simp [hv b i]
  have hsplit : ∑ σ ∈ ne, term σ = ∑ σ ∈ ne.filter (fun σ => countVec tag σ = k₀), term σ +
      ∑ σ ∈ rest, term σ := (sum_filter_add_sum_filter_not ne _ term).symm
  have hcat : ∀ k ∈ Kset,
      ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), |term σ| ≤
        K * Real.exp (∑ b, p b) * tagMin (tagTotal tag d) (tagTotal tag v) k +
          ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), r σ := by
    intro k hk
    obtain ⟨σ₀, hσ₀, hσk⟩ := mem_image.mp hk
    have hσ₀ne : σ₀ ∈ ne := (mem_filter.mp hσ₀).1
    have hk0 : k ≠ 0 := by
      rw [← hσk]
      intro h
      exact (mem_filter.mp hσ₀ne).2 ((countVec_eq_zero_iff tag σ₀).mp h)
    have hkk₀ : k ≠ k₀ := by rw [← hσk]; exact (mem_filter.mp hσ₀).2
    have hnemp : (tagsOf k).Nonempty := by
      by_contra hemp
      apply hk0
      funext j
      by_contra hj
      simp only [Pi.zero_apply] at hj
      exact hemp ⟨j, by simp [tagsOf]; omega⟩
    obtain ⟨j, hj, hjmin⟩ :=
      Finset.exists_mem_eq_inf' hnemp (tagTerm (tagTotal tag d) (tagTotal tag v) k)
    have hjk : 1 ≤ k j := by simpa [tagsOf] using hj
    have hmin : tagMin (tagTotal tag d) (tagTotal tag v) k =
        tagTerm (tagTotal tag d) (tagTotal tag v) k j := by
      unfold tagMin
      rw [dite_eq_left hnemp, hjmin]
    rw [hmin]
    have h1 : ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), |term σ| ≤
        ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), (K * tagWeight tag d v p j σ + r σ) := by
      apply sum_le_sum
      intro σ hσ
      rw [mem_filter] at hσ
      have hσr := mem_filter.mp hσ.1
      apply hterm σ (mem_filter.mp hσr.1).2 hσr.2 j
      rw [hσ.2]
      exact hjk
    have h2 : ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), tagWeight tag d v p j σ ≤
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (I b)) => countVec tag σ = k),
          tagWeight tag d v p j σ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro σ hσ
        rw [mem_filter] at hσ ⊢
        exact ⟨mem_univ _, hσ.2⟩
      · intro σ _ _
        apply prod_nonneg
        intro b _
        rcases σ b with _ | i
        · exact add_nonneg zero_le_one (hp b)
        · change 0 ≤ if tag b i = j then d b i else v b i
          split_ifs
          · exact hd b i
          · exact hv b i
    have h3 := sum_category_le tag hd hv hp k j
    rw [sum_add_distrib, ← mul_sum] at h1
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hK
    linarith
  have hfib : ∑ σ ∈ rest, |term σ| =
      ∑ k ∈ Kset, ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), |term σ| :=
    (Finset.sum_fiberwise_of_maps_to (fun σ hσ => mem_image_of_mem _ hσ) _).symm
  have hfibr : ∑ σ ∈ rest, r σ =
      ∑ k ∈ Kset, ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), r σ :=
    (Finset.sum_fiberwise_of_maps_to (fun σ hσ => mem_image_of_mem _ hσ) _).symm
  have hk₀ : k₀ ∉ Kset := by
    intro h
    obtain ⟨σ, hσ, hσk⟩ := mem_image.mp h
    exact (mem_filter.mp hσ).2 hσk
  have hseries : ∑ k ∈ Kset, tagMin (tagTotal tag d) (tagTotal tag v) k ≤
      tagSeries (tagTotal tag d) (tagTotal tag v) -
        tagMin (tagTotal tag d) (tagTotal tag v) k₀ := by
    have := sum_tagMin_le_tagSeries hd' hv' (insert k₀ Kset)
    rw [sum_insert hk₀] at this
    linarith
  have hEP : 0 ≤ K * Real.exp (∑ b, p b) := mul_nonneg hK (Real.exp_pos _).le
  have hrestb : |∑ σ ∈ rest, term σ| ≤ K * Real.exp (∑ b, p b) *
      (tagSeries (tagTotal tag d) (tagTotal tag v) -
        tagMin (tagTotal tag d) (tagTotal tag v) k₀) + ∑ σ ∈ rest, r σ := by
    calc |∑ σ ∈ rest, term σ| ≤ ∑ σ ∈ rest, |term σ| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Kset, ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), |term σ| := hfib
      _ ≤ ∑ k ∈ Kset, (K * Real.exp (∑ b, p b) * tagMin (tagTotal tag d) (tagTotal tag v) k +
            ∑ σ ∈ rest.filter (fun σ => countVec tag σ = k), r σ) := sum_le_sum hcat
      _ = K * Real.exp (∑ b, p b) * ∑ k ∈ Kset, tagMin (tagTotal tag d) (tagTotal tag v) k +
            ∑ σ ∈ rest, r σ := by
          rw [sum_add_distrib, ← mul_sum, hfibr]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hseries hEP
          linarith
  rw [hsplit]
  calc _ ≤ |∑ σ ∈ ne.filter (fun σ => countVec tag σ = k₀), term σ| + |∑ σ ∈ rest, term σ| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

end Split

end Sarkozy.OpsSteps
