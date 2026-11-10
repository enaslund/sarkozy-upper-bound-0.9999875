module

public import Sarkozy.RecordExpansion.Multinomial
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The tag series `𝔗(d, v)`

The series of (CP2) (`def:cp2`, Section 9 of the paper), which gives the cost
`L_0 = e^P 𝔗(d, v)` of the first stage:

  `𝔗(d, v) = ∑_{k ∈ ℕ^𝔗 ∖ {0}} min_{j : k_j ≥ 1} d_j^{k_j} ∏_{j' ≠ j} v_{j'}^{k_{j'}} / ∏_{j'} k_{j'}!`.

`tagTerm d v k j` is the term of the count vector `k` charged sharply at the tag
`j`, `tagMin d v k` its minimum over the tags present (`0` for `k = 0`), and
`tagSeries d v` the sum, a `tsum` over all count vectors `k : 𝔗 → ℕ`.

From `rem:cp:tags`: the terms are nonnegative (`tagMin_nonneg`), the series
converges with `𝔗(d, v) ≤ e^{∑_j m_j} - 1` for `m_j ≥ max(d_j, v_j)`
(`tagMin_summable`, `tagSeries_le_exp`), and it is nondecreasing in every
argument (`tagSeries_mono`), a minimum of nondecreasing functions being
nondecreasing. Every finite partial sum is at most
`𝔗(d, v)` (`sum_tagMin_le_tagSeries`), which is how `lem:sharp-first` uses it.
-/

@[expose] public section

open Finset
open scoped BigOperators Nat

namespace Sarkozy.RecordExpansion

variable {Tag : Type*} [Fintype Tag] [DecidableEq Tag]

/-- The term `d_j^{k_j} ∏_{j' ≠ j} v_{j'}^{k_{j'}} / ∏_{j'} k_{j'}!` of a count vector `k`,
charged sharply at the tag `j`. -/
noncomputable def tagTerm (d v : Tag → ℝ) (k : Tag → ℕ) (j : Tag) : ℝ :=
  (∏ j', (if j' = j then d j' else v j') ^ k j') / ∏ j', ((k j')! : ℝ)

/-- The tags present in a count vector. -/
def tagsOf (k : Tag → ℕ) : Finset Tag := univ.filter fun j => 1 ≤ k j

/-- The minimum over the tags present of `tagTerm`; zero for the zero count vector. -/
noncomputable def tagMin (d v : Tag → ℝ) (k : Tag → ℕ) : ℝ :=
  if h : (tagsOf k).Nonempty then (tagsOf k).inf' h (tagTerm d v k) else 0

/-- The tag series `𝔗(d, v)` of (CP2). -/
noncomputable def tagSeries (d v : Tag → ℝ) : ℝ := ∑' k : Tag → ℕ, tagMin d v k

theorem tagTerm_nonneg {d v : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (k : Tag → ℕ) (j : Tag) : 0 ≤ tagTerm d v k j := by
  unfold tagTerm
  apply div_nonneg _ (prod_nonneg fun j' _ => by positivity)
  apply prod_nonneg
  intro j' _
  split_ifs
  · exact pow_nonneg (hd j') _
  · exact pow_nonneg (hv j') _

theorem tagMin_nonneg {d v : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (k : Tag → ℕ) : 0 ≤ tagMin d v k := by
  unfold tagMin
  split_ifs with h
  · exact Finset.le_inf' h _ fun j _ => tagTerm_nonneg hd hv k j
  · exact le_rfl

theorem tagMin_le_tagTerm (d v : Tag → ℝ) {k : Tag → ℕ} {j : Tag} (hj : 1 ≤ k j) :
    tagMin d v k ≤ tagTerm d v k j := by
  have hmem : j ∈ tagsOf k := by simp [tagsOf, hj]
  unfold tagMin
  rw [dite_eq_left ⟨j, hmem⟩]
  exact Finset.inf'_le _ hmem

/-- A number below every `tagTerm` of the tags present is below `tagMin`. -/
theorem le_tagMin (d v : Tag → ℝ) {k : Tag → ℕ} (hk : k ≠ 0) {a : ℝ}
    (h : ∀ j, 1 ≤ k j → a ≤ tagTerm d v k j) : a ≤ tagMin d v k := by
  have hne : (tagsOf k).Nonempty := by
    by_contra hemp
    apply hk
    funext j
    by_contra hj
    simp only [Pi.zero_apply] at hj
    exact hemp ⟨j, by simp [tagsOf]; omega⟩
  unfold tagMin
  rw [dite_eq_left hne]
  exact Finset.le_inf' hne _ fun j hj => h j (by simpa [tagsOf] using hj)

theorem tagMin_zero (d v : Tag → ℝ) : tagMin d v 0 = 0 := by
  unfold tagMin
  have : ¬(tagsOf (0 : Tag → ℕ)).Nonempty := by
    rintro ⟨j, hj⟩
    simp [tagsOf] at hj
  rw [dite_eq_right this]

/-- Each term is at most `∏_j m_j^{k_j} / k_j!` for `m_j ≥ max(d_j, v_j)`. -/
theorem tagMin_le_prod {d v m : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (hdm : ∀ j, d j ≤ m j) (hvm : ∀ j, v j ≤ m j) {k : Tag → ℕ} (hk : k ≠ 0) :
    tagMin d v k ≤ ∏ j, m j ^ k j / ((k j)! : ℝ) := by
  have hne : ∃ j, 1 ≤ k j := by
    by_contra h
    push Not at h
    apply hk
    funext j
    have := h j
    simp only [Pi.zero_apply]
    omega
  obtain ⟨j, hj⟩ := hne
  refine (tagMin_le_tagTerm d v hj).trans ?_
  unfold tagTerm
  rw [Finset.prod_div_distrib]
  apply div_le_div_of_nonneg_right _ (prod_nonneg fun j' _ => by positivity)
  apply Finset.prod_le_prod₀
  · intro j' _
    split_ifs
    · exact pow_nonneg (hd j') _
    · exact pow_nonneg (hv j') _
  · intro j' _
    split_ifs
    · exact pow_le_pow_left₀ (hd j') (hdm j') _
    · exact pow_le_pow_left₀ (hv j') (hvm j') _

/-- The finite partial sums of `∏_j m_j^{k_j}/k_j!` over a box are at most `e^{∑ m}`. -/
theorem sum_box_prod_le_exp {m : Tag → ℝ} (hm : ∀ j, 0 ≤ m j) (K : ℕ) :
    ∑ k ∈ Fintype.piFinset (fun _ : Tag => range K), ∏ j, m j ^ k j / ((k j)! : ℝ) ≤
      Real.exp (∑ j, m j) := by
  rw [← Finset.prod_univ_sum (fun _ => range K) (fun j n => m j ^ n / (n ! : ℝ)), Real.exp_sum]
  exact Finset.prod_le_prod₀
    (fun j _ => sum_nonneg fun i _ => div_nonneg (pow_nonneg (hm j) _) (by positivity))
    (fun j _ => Real.sum_le_exp_of_nonneg (hm j) K)

/-- **Finite partial sums** (`rem:cp:tags`): for `m_j ≥ max(d_j, v_j)`, every finite sum of
the terms of `𝔗(d, v)` is at most `e^{∑_j m_j} - 1`. -/
theorem sum_tagMin_le {d v m : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (hdm : ∀ j, d j ≤ m j) (hvm : ∀ j, v j ≤ m j) (s : Finset (Tag → ℕ)) :
    ∑ k ∈ s, tagMin d v k ≤ Real.exp (∑ j, m j) - 1 := by
  have hm : ∀ j, 0 ≤ m j := fun j => (hd j).trans (hdm j)
  -- a box containing `s` and `0`
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ∈ s, ∀ j, k j < K := by
    refine ⟨∑ k ∈ s, ∑ j, k j + 1, ?_⟩
    intro k hk j
    have h1 : k j ≤ ∑ j', k j' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)
    have h2 : ∑ j', k j' ≤ ∑ k' ∈ s, ∑ j', k' j' :=
      Finset.single_le_sum (f := fun k' : Tag → ℕ => ∑ j', k' j') (fun _ _ => Nat.zero_le _) hk
    omega
  set box := Fintype.piFinset (fun _ : Tag => range (K + 1)) with hbox
  have hsub : s ⊆ box := by
    intro k hk
    simp only [hbox, Fintype.mem_piFinset, mem_range]
    intro j
    have := hK k hk j
    omega
  have h0 : (0 : Tag → ℕ) ∈ box := by
    simp only [hbox, Fintype.mem_piFinset, mem_range, Pi.zero_apply]
    intro _
    omega
  have hle : ∀ k ∈ box, tagMin d v k ≤
      (∏ j, m j ^ k j / ((k j)! : ℝ)) - if k = 0 then 1 else 0 := by
    intro k _
    by_cases hk : k = 0
    · subst hk
      simp [tagMin_zero]
    · rw [ite_eq_right hk, sub_zero]
      exact tagMin_le_prod hd hv hdm hvm hk
  calc ∑ k ∈ s, tagMin d v k ≤ ∑ k ∈ box, tagMin d v k :=
        sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => tagMin_nonneg hd hv k)
    _ ≤ ∑ k ∈ box, ((∏ j, m j ^ k j / ((k j)! : ℝ)) - if k = 0 then 1 else 0) :=
        sum_le_sum hle
    _ = (∑ k ∈ box, ∏ j, m j ^ k j / ((k j)! : ℝ)) - 1 := by
        rw [sum_sub_distrib, Finset.sum_ite_eq' box 0 (fun _ => (1 : ℝ))]
        simp [h0]
    _ ≤ Real.exp (∑ j, m j) - 1 := by
        linarith [sum_box_prod_le_exp hm (K + 1)]

/-- **Convergence** (`rem:cp:tags`): the series `𝔗(d, v)` converges. -/
theorem tagMin_summable {d v : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j) :
    Summable (tagMin d v) :=
  summable_of_sum_le (fun k => tagMin_nonneg hd hv k)
    (sum_tagMin_le hd hv (m := fun j => max (d j) (v j)) (fun _ => le_max_left _ _)
      (fun _ => le_max_right _ _))

/-- **The bound of `rem:cp:tags`**: `𝔗(d, v) ≤ e^{∑_j m_j} - 1` for `m_j ≥ max(d_j, v_j)`. -/
theorem tagSeries_le_exp {d v m : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (hdm : ∀ j, d j ≤ m j) (hvm : ∀ j, v j ≤ m j) :
    tagSeries d v ≤ Real.exp (∑ j, m j) - 1 :=
  Real.tsum_le_of_sum_le (fun k => tagMin_nonneg hd hv k) (sum_tagMin_le hd hv hdm hvm)

theorem tagSeries_nonneg {d v : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ tagSeries d v :=
  tsum_nonneg fun k => tagMin_nonneg hd hv k

/-- Every finite partial sum of the tag series is at most `𝔗(d, v)`. -/
theorem sum_tagMin_le_tagSeries {d v : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (s : Finset (Tag → ℕ)) : ∑ k ∈ s, tagMin d v k ≤ tagSeries d v :=
  (tagMin_summable hd hv).sum_le_tsum s (fun k _ => tagMin_nonneg hd hv k)

theorem tagTerm_mono {d v d' v' : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (hdd : ∀ j, d j ≤ d' j) (hvv : ∀ j, v j ≤ v' j) (k : Tag → ℕ) (j : Tag) :
    tagTerm d v k j ≤ tagTerm d' v' k j := by
  unfold tagTerm
  apply div_le_div_of_nonneg_right _ (prod_nonneg fun j' _ => by positivity)
  apply Finset.prod_le_prod₀
  · intro j' _
    split_ifs
    · exact pow_nonneg (hd j') _
    · exact pow_nonneg (hv j') _
  · intro j' _
    split_ifs
    · exact pow_le_pow_left₀ (hd j') (hdd j') _
    · exact pow_le_pow_left₀ (hv j') (hvv j') _

theorem tagMin_mono {d v d' v' : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (hdd : ∀ j, d j ≤ d' j) (hvv : ∀ j, v j ≤ v' j) (k : Tag → ℕ) :
    tagMin d v k ≤ tagMin d' v' k := by
  unfold tagMin
  split_ifs with h
  · apply Finset.le_inf' h
    intro j hj
    exact (Finset.inf'_le _ hj).trans (tagTerm_mono hd hv hdd hvv k j)
  · exact le_rfl

/-- **Monotonicity** (`rem:cp:tags`): `𝔗(d, v)` is nondecreasing in every `d_j` and `v_j`
on nonnegative arguments. -/
theorem tagSeries_mono {d v d' v' : Tag → ℝ} (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j)
    (hdd : ∀ j, d j ≤ d' j) (hvv : ∀ j, v j ≤ v' j) :
    tagSeries d v ≤ tagSeries d' v' := by
  have hd' : ∀ j, 0 ≤ d' j := fun j => (hd j).trans (hdd j)
  have hv' : ∀ j, 0 ≤ v' j := fun j => (hv j).trans (hvv j)
  exact (tagMin_summable hd hv).tsum_le_tsum (tagMin_mono hd hv hdd hvv)
    (tagMin_summable hd' hv')

end Sarkozy.RecordExpansion
