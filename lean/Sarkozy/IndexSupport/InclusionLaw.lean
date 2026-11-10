module

public import Sarkozy.IndexSupport.Abstract

/-!
# Inclusion laws and inclusion moments

The remark "The inclusion and depth laws" after `lem:record:common-mean`: the proof of the
Index-support lemma uses only `Pr(S ⊆ 𝒥) ≥ δ_S` (see `common_mean`, whose hypothesis is
`δ_s ≤ Pr(s retained)`), and among such inclusion laws the independent one minimizes every
moment later paid for the inclusions: for `w_j ≥ 1`,
`E ∏_{j ∈ 𝒥} w_j = ∑_S Pr(S ⊆ 𝒥) ∏_{j ∈ S} (w_j - 1) ≥ ∏_j (1 + δ_j (w_j - 1))`
(`expect_prod_eq`, `prod_le_expect_prod`), with equality for independent inclusion with
probabilities `δ_j`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.IndexSupport

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The probability that the random set contains `S`. -/
noncomputable def containProb (law : FiniteLaw (Finset K)) (S : Finset K) : ℝ :=
  law.expect (fun J => if S ⊆ J then 1 else 0)

/-- `E ∏_{j ∈ 𝒥} w_j = ∑_S Pr(S ⊆ 𝒥) ∏_{j ∈ S} (w_j - 1)`. -/
theorem expect_prod_eq (law : FiniteLaw (Finset K)) (w : K → ℝ) :
    law.expect (fun J => ∏ j ∈ J, w j) =
      ∑ S : Finset K, containProb law S * ∏ j ∈ S, (w j - 1) := by
  have h (J : Finset K) : ∏ j ∈ J, w j =
      ∑ S : Finset K, (if S ⊆ J then 1 else 0) * ∏ j ∈ S, (w j - 1) := by
    rw [show ∏ j ∈ J, w j = ∏ j ∈ J, (1 + (w j - 1)) from
      prod_congr rfl (fun j _ => by ring), prod_one_add]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext S
    simp only [mem_powerset, mem_filter, mem_univ, true_and]
  simp only [h, containProb, FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro S _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro J _
  ring

/-- If `Pr(S ⊆ 𝒥) ≥ ∏_{j ∈ S} δ_j` for every `S`, then for `w_j ≥ 1`,
`E ∏_{j ∈ 𝒥} w_j ≥ ∏_j (1 + δ_j (w_j - 1))`. -/
theorem prod_le_expect_prod (law : FiniteLaw (Finset K)) (δ : K → ℝ)
    (hδ : ∀ S : Finset K, ∏ j ∈ S, δ j ≤ containProb law S) (w : K → ℝ)
    (hw : ∀ j, 1 ≤ w j) :
    ∏ j, (1 + δ j * (w j - 1)) ≤ law.expect (fun J => ∏ j ∈ J, w j) := by
  rw [expect_prod_eq, Finset.prod_one_add, Finset.powerset_univ]
  apply Finset.sum_le_sum
  intro S _
  rw [Finset.prod_mul_distrib]
  exact mul_le_mul_of_nonneg_right (hδ S) (Finset.prod_nonneg (fun j _ => by linarith [hw j]))

/-- Independent inclusion with probabilities `δ_j ∈ [0, 1]`. -/
noncomputable def independentInclusion (δ : K → ℝ) (hδ0 : ∀ j, 0 ≤ δ j)
    (hδ1 : ∀ j, δ j ≤ 1) : FiniteLaw (Finset K) where
  weight J := (∏ j ∈ J, δ j) * ∏ j ∈ Jᶜ, (1 - δ j)
  nonneg J := mul_nonneg (prod_nonneg (fun j _ => hδ0 j))
    (prod_nonneg (fun j _ => by linarith [hδ1 j]))
  total := by
    have h := Fintype.prod_add δ (fun j => 1 - δ j)
    simp only [add_sub_cancel, prod_const_one] at h
    exact h.symm

/-- For independent inclusion, `Pr(S ⊆ 𝒥) = ∏_{j ∈ S} δ_j`. -/
theorem containProb_independent (δ : K → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (S : Finset K) : containProb (independentInclusion δ hδ0 hδ1) S = ∏ j ∈ S, δ j := by
  unfold containProb
  simp only [FiniteLaw.expect, independentInclusion, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  -- sum over `J ⊇ S`, written as `J = S ∪ T` with `T ⊆ Sᶜ`
  have hbij : ∑ J ∈ univ.filter (fun J : Finset K => S ⊆ J),
      (∏ j ∈ J, δ j) * ∏ j ∈ Jᶜ, (1 - δ j) =
      ∑ T ∈ Sᶜ.powerset, (∏ j ∈ S ∪ T, δ j) * ∏ j ∈ (S ∪ T)ᶜ, (1 - δ j) := by
    apply Finset.sum_bij' (fun J _ => J \ S) (fun T _ => S ∪ T)
    · intro J hJ
      simp only [mem_powerset]
      intro x hx
      simp only [mem_sdiff] at hx
      simp [hx.2]
    · intro T hT
      simp
    · intro J hJ
      simp only [mem_filter, mem_univ, true_and] at hJ
      simp [Finset.union_sdiff_of_subset hJ]
    · intro T hT
      simp only [mem_powerset] at hT
      rw [Finset.union_sdiff_left]
      exact Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_of_subset_left hT
        disjoint_compl_left) |>.symm ▸ rfl
    · intro J hJ
      simp only [mem_filter, mem_univ, true_and] at hJ
      rw [Finset.union_sdiff_of_subset hJ]
  rw [hbij]
  have hsplit (T : Finset K) (hT : T ⊆ Sᶜ) :
      (∏ j ∈ S ∪ T, δ j) * ∏ j ∈ (S ∪ T)ᶜ, (1 - δ j) =
        (∏ j ∈ S, δ j) * ((∏ j ∈ T, δ j) * ∏ j ∈ Sᶜ \ T, (1 - δ j)) := by
    have hdisj : Disjoint S T := Finset.disjoint_of_subset_right hT disjoint_compl_right
    rw [Finset.prod_union hdisj, Finset.compl_union, ← Finset.sdiff_eq_inter_compl]
    ring
  rw [Finset.sum_congr rfl (fun T hT => hsplit T (mem_powerset.mp hT)), ← Finset.mul_sum]
  have h := Finset.prod_add δ (fun j => 1 - δ j) Sᶜ
  simp only [add_sub_cancel, prod_const_one] at h
  rw [← h, mul_one]

end Sarkozy.IndexSupport
