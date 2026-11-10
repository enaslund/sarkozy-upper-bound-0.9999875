module

public import Sarkozy.L20Cap.CollX1
public import Sarkozy.L20Cap.Sanity

/-!
# Non-vacuity of the X1 and WP-FI bridges

The hypotheses of `l20_prime_caps_X1`, `hXns_of_compressed` and `hD_of_incident` on the graph
`G6 = G_{F,2}` that do not involve class data can be met:

* `rowsDeg0_G6`, `sup_rowsDeg0_G6`: the degrees of `G_{F,2}` are `2` (the `a_i`, `c_j`) and `0`
  (the `b_l`);
* `coarseError_G6_lt`, `leafEhat_G6_lt`: `e_{d_v}(Q, 6) < 1` and `ê = e_2(Q, 6) < 1` for
  `Q ≥ 64` (the hypotheses `hS1` of `hD_of_incident` and `l20_prime_caps_X1`);
* at `p = 11`, `G_{F,2}` has labellings (`injLabellings_G6_eleven`);
* `card_nonstars_Ex16`: `supp D₂₀` has `2^16 - 1 - 42 - 42 + 16 = 65467` nonstars, from the
  general identity `sum_nonstars_eq` with `w = 1` (a check of that identity; `Ex8` has `221`,
  `card_nonstars_Ex8`, by `decide`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap.SanityX1

open Sarkozy Sarkozy.L20Cap Sarkozy.Extraction Sarkozy.ExtractionK Sarkozy.Labellings

/-- The degrees of `G_{F,2}`. -/
theorem rowsDeg0_G6 : ∀ v : Fin 6, rowsDeg0 G6 v = 0 ∨ rowsDeg0 G6 v = 2 := by decide

theorem sup_rowsDeg0_G6 : univ.sup (rowsDeg0 G6) = 2 := by decide

theorem coarseError_two_lt {Q : ℝ} (hQ : 64 ≤ Q) : coarseError 2 Q 6 < 1 := by
  have hs : 8 ≤ Real.sqrt Q := by
    rw [show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hQ
  have hr0 : 0 < (Real.sqrt Q)⁻¹ := inv_pos.mpr (by linarith)
  have hr : (Real.sqrt Q)⁻¹ ≤ 1 / 8 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hs
  have hrr : (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ ≤ 1 / 8 * (1 / 8) :=
    mul_le_mul hr hr hr0.le (by norm_num)
  have e : coarseError 2 Q 6 = 4 * ((1 / 4) * (Real.sqrt Q)⁻¹ + 6 * ((Real.sqrt Q)⁻¹ *
      (Real.sqrt Q)⁻¹)) := by
    unfold coarseError coarseH
    ring
  rw [e]
  nlinarith

theorem coarseError_zero_lt {Q : ℝ} (hQ : 64 ≤ Q) : coarseError 0 Q 6 < 1 := by
  have hs : 8 ≤ Real.sqrt Q := by
    rw [show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hQ
  have hr0 : 0 < (Real.sqrt Q)⁻¹ := inv_pos.mpr (by linarith)
  have hr : (Real.sqrt Q)⁻¹ ≤ 1 / 8 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hs
  have hrr : (Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹ ≤ 1 / 8 * (1 / 8) :=
    mul_le_mul hr hr hr0.le (by norm_num)
  have e : coarseError 0 Q 6 = 6 * ((Real.sqrt Q)⁻¹ * (Real.sqrt Q)⁻¹) := by
    unfold coarseError coarseH
    ring
  rw [e]
  nlinarith

/-- `hS1` of `hD_of_incident` holds for `p ≥ 64`. -/
theorem coarseError_G6_lt {Q : ℝ} (hQ : 64 ≤ Q) : ∀ v, coarseError (rowsDeg0 G6 v) Q 6 < 1 := by
  intro v
  rcases rowsDeg0_G6 v with h | h <;> rw [h]
  · exact coarseError_zero_lt hQ
  · exact coarseError_two_lt hQ

/-- `hS1` of `l20_prime_caps_X1` holds for `Q ≥ 64`. -/
theorem leafEhat_G6_lt {Q : ℝ} (hQ : 64 ≤ Q) : leafEhat G6 Q 6 < 1 := by
  unfold leafEhat
  rw [sup_rowsDeg0_G6]
  exact coarseError_two_lt hQ

/-- `G_{F,2}` has labellings at `p = 11`. -/
theorem injLabellings_G6_eleven : (injLabellings (ZMod 11) G6).Nonempty :=
  injLabellings_G6_nonempty Sanity.six_le_eleven

/-- The nonstars of `supp D₂₀`, counted by `sum_nonstars_eq`. -/
theorem card_nonstars_Ex16 : (nonstars Ex16).card = 65467 := by
  have h := sum_nonstars_eq Ex16 (fun _ => (1 : ℝ))
  have hr : ∀ i : Fin 6, (Ex16.filter fun e => e.1 = i).card = ![2, 2, 4, 4, 2, 2] i := by
    decide
  have hc : ∀ j : Fin 6, (Ex16.filter fun e => e.2 = j).card = ![2, 2, 4, 4, 2, 2] j := by
    decide
  simp only [prod_const_one, sum_const, nsmul_eq_mul, mul_one, prod_const, card_Ex16, hr, hc,
    Fin.sum_univ_six] at h
  norm_num at h
  exact_mod_cast h

end Sarkozy.L20Cap.SanityX1
