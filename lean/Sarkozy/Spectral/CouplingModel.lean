module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Star.Real

/-!
# `def:coupling-model`: the star Gram model `𝐇` and its parts

`paper/sections/14_spectral.tex`, `eq:spec:H` and `def:coupling-model`. The cross pattern is
given by the neighbourhoods `N(k) = {j ∈ U⁺ : ς_jk ≠ 0}` and the signs `σ j k = χ(ς_jk) = ±1`
(for `j ∈ N(k)`). For `J ⊆ U⁺`, `(ε_J)_k = ∏_{j∈J} σ j k` if `J ⊆ N(k)` and `0` otherwise.

* `starGram N σ = ∑_{∅ ≠ J} ε_J ε_Jᵀ` (`𝐇`, `eq:spec:H`);
  `starGram_apply`: `𝐇_kl = ∏_{j ∈ N(k) ∩ N(l)} (1 + σ j k σ j l) - 1`;
  `starGram_posSemidef`: `𝐇 ⪰ 0`; `starGram_diag`: `𝐇_kk = 2^{r_k} - 1`;
  `starGram_inconsistent`: `𝐇_kl = -1` for an inconsistent pair.
* `starGramOn N σ P`: the sum over the sets `J` satisfying a predicate `P`; with `P` "`|J| ≥ 2`
  and coverable" this is `𝐇^cov`, with "`|J| ≥ 2` and not coverable" it is `𝐇^nc`.
  `starGramOn_posSemidef`; `starGram_split`: `𝐇 = 𝐇^{(1)} + 𝐇^cov + 𝐇^nc`, the first term
  over the singletons. `𝐇⁺ = 𝐇 + [p ≡ 1 (4)] 𝐇^cov` is then a sum of positive semidefinite
  matrices.
-/

@[expose] public section

open scoped BigOperators Matrix
open Finset

namespace Sarkozy.Spectral

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `(ε_J)_k = ∏_{j∈J} σ j k` if `J ⊆ N(k)`, else `0`. -/
def epsJ (N : U → Finset U) (σ : U → U → ℝ) (J : Finset U) (k : U) : ℝ :=
  if J ⊆ N k then ∏ j ∈ J, σ j k else 0

/-- The star Gram model over the sets `J` with property `P`: `∑_{J, P J} ε_J ε_Jᵀ`. -/
noncomputable def starGramOn (N : U → Finset U) (σ : U → U → ℝ) (P : Finset U → Prop)
    [DecidablePred P] : Matrix U U ℝ :=
  ∑ J ∈ (Finset.univ : Finset U).powerset.filter P,
    Matrix.vecMulVec (epsJ N σ J) (epsJ N σ J)

/-- **The star Gram model** `𝐇 = ∑_{∅ ≠ J ⊆ U⁺} ε_J ε_Jᵀ` (`eq:spec:H`). -/
noncomputable def starGram (N : U → Finset U) (σ : U → U → ℝ) : Matrix U U ℝ :=
  starGramOn N σ (fun J => J.Nonempty)

theorem starGramOn_apply (N : U → Finset U) (σ : U → U → ℝ) (P : Finset U → Prop)
    [DecidablePred P] (k l : U) :
    starGramOn N σ P k l = ∑ J ∈ (Finset.univ : Finset U).powerset.filter P,
      epsJ N σ J k * epsJ N σ J l := by
  rw [starGramOn, Matrix.sum_apply]
  rfl

/-- `𝐇^{(P)} ⪰ 0`: a sum of Gram rank-one terms. -/
theorem starGramOn_posSemidef (N : U → Finset U) (σ : U → U → ℝ) (P : Finset U → Prop)
    [DecidablePred P] : (starGramOn N σ P).PosSemidef := by
  rw [starGramOn]
  refine Matrix.posSemidef_sum _ fun J _ => ?_
  have h := Matrix.posSemidef_vecMulVec_self_star (epsJ N σ J)
  simpa using h

theorem starGram_posSemidef (N : U → Finset U) (σ : U → U → ℝ) :
    (starGram N σ).PosSemidef :=
  starGramOn_posSemidef N σ _

/-- **`eq:spec:H`, the entries**: `𝐇_kl = ∏_{j ∈ N(k) ∩ N(l)} (1 + σ j k σ j l) - 1`. -/
theorem starGram_apply (N : U → Finset U) (σ : U → U → ℝ) (k l : U) :
    starGram N σ k l = ∏ j ∈ N k ∩ N l, (1 + σ j k * σ j l) - 1 := by
  rw [starGram, starGramOn_apply, Finset.prod_one_add]
  -- the summand vanishes unless `J ⊆ N(k) ∩ N(l)`
  have hterm : ∀ J : Finset U, epsJ N σ J k * epsJ N σ J l =
      if J ⊆ N k ∩ N l then ∏ j ∈ J, (σ j k * σ j l) else 0 := by
    intro J
    simp only [epsJ, Finset.subset_inter_iff]
    by_cases hk : J ⊆ N k <;> by_cases hl : J ⊆ N l <;>
      simp [hk, hl, Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- the sets `∅ ≠ J ⊆ N(k) ∩ N(l)`, plus the empty set, are the powerset of `N(k) ∩ N(l)`
  have hset : ((Finset.univ : Finset U).powerset.filter (fun J => J.Nonempty)).filter
      (fun J => J ⊆ N k ∩ N l) = (N k ∩ N l).powerset.filter (fun J => J.Nonempty) := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    tauto
  rw [hset, ← Finset.sum_filter_add_sum_filter_not (N k ∩ N l).powerset (fun J => J.Nonempty)]
  have hempty : (N k ∩ N l).powerset.filter (fun J => ¬ J.Nonempty) = {∅} := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, rfl⟩
      rfl
    · rintro rfl
      exact ⟨Finset.empty_subset _, rfl⟩
  rw [hempty, Finset.sum_singleton, Finset.prod_empty]
  ring

/-- **The diagonal**: `𝐇_kk = 2^{r_k} - 1` when the signs are `±1` on `N(k)`. -/
theorem starGram_diag (N : U → Finset U) (σ : U → U → ℝ)
    (hσ : ∀ k, ∀ j ∈ N k, σ j k = 1 ∨ σ j k = -1) (k : U) :
    starGram N σ k k = 2 ^ (N k).card - 1 := by
  rw [starGram_apply, Finset.inter_self]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => show 1 + σ j k * σ j k = 2 by
    rcases hσ k j hj with h | h <;> rw [h] <;> norm_num), Finset.prod_const]

/-- **Inconsistent pairs**: if `σ j k σ j l = -1` for some `j ∈ N(k) ∩ N(l)`, then
`𝐇_kl = -1`. -/
theorem starGram_inconsistent (N : U → Finset U) (σ : U → U → ℝ) {k l j : U}
    (hj : j ∈ N k ∩ N l) (h : σ j k * σ j l = -1) : starGram N σ k l = -1 := by
  rw [starGram_apply, Finset.prod_eq_zero hj (by rw [h]; ring)]
  ring

/-- **The split** `𝐇 = 𝐇^{(1)} + 𝐇^cov + 𝐇^nc` (`def:coupling-model`), for any coverability
predicate `cov`: singletons, coverable sets with `|J| ≥ 2`, and the others with `|J| ≥ 2`. -/
theorem starGram_split (N : U → Finset U) (σ : U → U → ℝ) (cov : Finset U → Prop)
    [DecidablePred cov] :
    starGram N σ = starGramOn N σ (fun J => J.card = 1) +
      starGramOn N σ (fun J => 2 ≤ J.card ∧ cov J) +
      starGramOn N σ (fun J => 2 ≤ J.card ∧ ¬ cov J) := by
  ext k l
  simp only [Matrix.add_apply, starGramOn_apply, starGram]
  set f := fun J : Finset U => epsJ N σ J k * epsJ N σ J l
  set s := (Finset.univ : Finset U).powerset
  have h1 : ∑ J ∈ s.filter (fun J => J.Nonempty), f J =
      ∑ J ∈ s.filter (fun J => J.card = 1), f J + ∑ J ∈ s.filter (fun J => 2 ≤ J.card), f J := by
    rw [← Finset.sum_union]
    · congr 1
      ext J
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hs, hne⟩
        have := Finset.card_pos.mpr hne
        by_cases h : J.card = 1
        · exact Or.inl ⟨hs, h⟩
        · exact Or.inr ⟨hs, by omega⟩
      · rintro (⟨hs, h⟩ | ⟨hs, h⟩)
        · exact ⟨hs, Finset.card_pos.mp (by omega)⟩
        · exact ⟨hs, Finset.card_pos.mp (by omega)⟩
    · rw [Finset.disjoint_filter]
      intro J _ h1 h2
      omega
  have h2 : ∑ J ∈ s.filter (fun J => 2 ≤ J.card), f J =
      ∑ J ∈ s.filter (fun J => 2 ≤ J.card ∧ cov J), f J +
        ∑ J ∈ s.filter (fun J => 2 ≤ J.card ∧ ¬ cov J), f J := by
    rw [← Finset.sum_filter_add_sum_filter_not (s.filter (fun J => 2 ≤ J.card)) cov,
      Finset.filter_filter, Finset.filter_filter]
  rw [h1, h2, add_assoc]

end Sarkozy.Spectral
