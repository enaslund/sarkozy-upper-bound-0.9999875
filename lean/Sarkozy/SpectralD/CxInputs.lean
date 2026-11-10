module

public import Sarkozy.SpectralD.CxCriterion3

@[expose] public section

/-!
# Small inputs of the spectral criterion for the cut, discharged

Three hypotheses of `spectral_criterion_cut_three` that are not certified numbers proper:
* `lowerProd_pos_cut`: `L_i > 0` (`hLpos`) from `e_t(p, n') < 1` for `t ≤ Δ` and the degree
  bound `Δ` (WP-P's `lowerProd_pos`);
* `rhoRow_le`: `ρ_row ≤ (∑_l (2^{r_l} − 1))²`, so `hρ` holds with `ρ = (∑_l (2^{r_l} − 1))²`
  (the paper uses the sharper `max_k (2^{r_k} − 1) ∑_l (2^{r_l} − 1)`, which `hρ` also accepts);
* `deltaE_normLe`: `‖Δ^E‖ ≤ Λ` for any `Λ ≥ max_k r_k` (Schur test, WP-K's `normLe_schur`), so
  `hDE` holds with the maximal cross degree (the certificates use an exact `Λ_D ≤ max_k r_k`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`hLpos`** from the error conditions (WP-P's `lowerProd_pos`). -/
theorem lowerProd_pos_cut {nn Δ : ℕ}
    (he : ∀ t ≤ Δ, TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn < 1)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (l : D.cut.Half → List W) (i : D.cut.Half) :
    0 < Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i) := by
  have hq : (1 : ℝ) ≤ (Fintype.card (ZMod p) : ℕ) := by exact_mod_cast Fintype.card_pos
  exact Cuts.SpecData.lowerProd_pos D.G hq he hdeg (l i) (fixSet D i)

/-- **`hρ`** with `ρ = (∑_l (2^{r_l} − 1))²`. -/
theorem rhoRow_le (j : D.cut.Half) :
    ((2 : ℝ) ^ (D.Nset j).card - 1) * ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤
      (∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1)) ^ 2 := by
  have h0 : ∀ j' : D.cut.Half, (0 : ℝ) ≤ (2 : ℝ) ^ (D.Nset j').card - 1 := fun j' => by
    have : (1 : ℝ) ≤ 2 ^ (D.Nset j').card := one_le_pow₀ (by norm_num)
    linarith
  have h1 : (2 : ℝ) ^ (D.Nset j).card - 1 ≤ ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) :=
    single_le_sum (f := fun j' => (2 : ℝ) ^ (D.Nset j').card - 1) (fun j' _ => h0 j')
      (mem_univ j)
  rw [sq]
  exact mul_le_mul_of_nonneg_right h1 (sum_nonneg fun j' _ => h0 j')

/-- **`hDE`**: `‖Δ^E‖ ≤ Λ` for `Λ ≥ max_k r_k` (Schur test). -/
theorem deltaE_normLe {Λ : ℝ} (hΛ : ∀ k : D.cut.Half, ((D.Nset k).card : ℝ) ≤ Λ) :
    NormLe (deltaE (sgnZ (p := p) D)) Λ := by
  classical
  refine normLe_schur _ (fun k l => if D.sgn k l ≠ 0 then 1 else 0) (fun k l => by
    split_ifs <;> norm_num) (fun k l => ?_) (fun k l => ?_) (fun k => ?_)
  · have h : D.sgn k l ≠ 0 ↔ D.sgn l k ≠ 0 := by
      rw [D.sgn_antisymm l k, neg_ne_zero]
    by_cases hkl : D.sgn k l ≠ 0
    · simp only [hkl, h.mp hkl, ne_eq, not_false_eq_true, ↓reduceIte]
    · have hlk : ¬ D.sgn l k ≠ 0 := fun h' => hkl (h.mpr h')
      simp only [hkl, hlk, ↓reduceIte]
  · unfold deltaE
    by_cases hz : sgnZ (p := p) D k l ≠ 0
    · have hs : D.sgn k l ≠ 0 := by
        intro h0; apply hz; unfold sgnZ; rw [h0]; simp
      simp only [hz, hs, ne_eq, not_false_eq_true, ↓reduceIte]
      rw [norm_chiC hz]
    · simp only [hz, ↓reduceIte, norm_zero]
      split_ifs <;> norm_num
  · have e : ∑ l, (if D.sgn k l ≠ 0 then (1 : ℝ) else 0) = (D.Nset k).card := by
      rw [sum_boole]
      congr 1
      have hset : (univ.filter (fun l => D.sgn k l ≠ 0)).card = (D.Nset k).card := by
        unfold Cuts.SpecData.Nset
        congr 1
        ext l
        simp only [mem_filter, mem_univ, true_and]
        rw [D.sgn_antisymm l k, neg_ne_zero]
      exact_mod_cast hset
    rw [e]
    exact hΛ k

end Sarkozy.SpectralD.Cx
