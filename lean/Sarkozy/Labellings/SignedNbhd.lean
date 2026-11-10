module

public import Sarkozy.Labellings.Extension

/-!
# Signed neighbourhoods (`lem:record:signed-nbhd`)

`paper/sections/12_labellings.tex`: the case `t = 4` of `lem:extension`, with `a_4 = 10`,
`b_4 = 7`. For distinct `x_1, …, x_4` and signs `s`, with `r = q^{-1/2}`, `q' = 1/q`
(the paper's `q = 1/p`), `υ₊ = 11r + 6q'` and `υ₋ = 11r + 70q'`:

* `signed_soft_count`: `|𝔖 - q| ≤ 10√q + 7 ≤ 11√q + 6`;
* `signed_nbhd_bounds`: the signed neighbourhood `{z ∉ {x_i} : χ(z - x_i) = s_i}` has between
  `q/16 (1 - υ₋)` and `q/16 (1 + υ₊)` elements, and after excluding `k` further labels at least
  `q/16 (1 - υ₋ - 16 k q')` remain.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem gradedA_four : gradedA 4 = 10 := by norm_num [gradedA]

theorem gradedB_four : gradedB 4 = 7 := by norm_num [gradedB]

/-- `lem:record:signed-nbhd`, soft count: `|𝔖 - q| ≤ 10√q + 7 ≤ 11√q + 6`. -/
theorem signed_soft_count (hW : WeilBound F) (x : Fin 4 → F) (hx : Function.Injective x)
    (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    |((∑ z, ∏ i, (1 + s i * quadraticChar F (z - x i)) : ℤ) : ℝ) - Fintype.card F| ≤
        10 * Real.sqrt (Fintype.card F) + 7 ∧
      10 * Real.sqrt (Fintype.card F) + 7 ≤ 11 * Real.sqrt (Fintype.card F) + 6 := by
  have h := soft_count_bound hW x hx s hs
  rw [Fintype.card_fin, gradedA_four, gradedB_four] at h
  refine ⟨h, ?_⟩
  have : (1 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast Fintype.card_pos)
  linarith

/-- **`lem:record:signed-nbhd`.** With `r = q^{-1/2}` and `q' = 1/q`, the signed neighbourhood of
four distinct labels has between `q/16 (1 - (11r + 70q'))` and `q/16 (1 + (11r + 6q'))`
elements; removing `k` further labels leaves at least `q/16 (1 - (11r + 70q') - 16 k q')`. -/
theorem signed_nbhd_bounds (hW : WeilBound F) (x : Fin 4 → F) (hx : Function.Injective x)
    (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (K : Finset F) :
    ((admissible x s (univ.image x)).card : ℝ) ≤ (Fintype.card F : ℝ) / 16 *
        (1 + (11 * (1 / Real.sqrt (Fintype.card F)) + 6 / (Fintype.card F : ℝ))) ∧
      (Fintype.card F : ℝ) / 16 *
          (1 - (11 * (1 / Real.sqrt (Fintype.card F)) + 70 / (Fintype.card F : ℝ))) ≤
        (admissible x s (univ.image x)).card ∧
      (Fintype.card F : ℝ) / 16 *
          (1 - (11 * (1 / Real.sqrt (Fintype.card F)) + 70 / (Fintype.card F : ℝ)) -
            16 * K.card / (Fintype.card F : ℝ)) ≤
        ((admissible x s (univ.image x)) \ K).card := by
  have hroots : ∀ i, x i ∈ univ.image x := fun i => mem_image_of_mem x (mem_univ i)
  have hb := extension_bounds hW x hx s hs (univ.image x) hroots
  rw [Fintype.card_fin, gradedA_four, gradedB_four] at hb
  have hcardX : ((univ.image x).card : ℝ) = 4 := by
    rw [card_image_of_injective _ hx, card_univ, Fintype.card_fin]; norm_num
  rw [hcardX] at hb
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set Φ := admissible x s (univ.image x)
  obtain ⟨hup, hlo⟩ := hb
  norm_num at hup hlo
  have hq0 : 0 < q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have h1 : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    rw [hqdef]; exact_mod_cast Fintype.card_pos
  have hrq : 1 / Real.sqrt q * q = Real.sqrt q := by
    rw [one_div_mul_eq_div, Real.div_sqrt]
  have e1 : q / 16 * (1 + (11 * (1 / Real.sqrt q) + 6 / q)) =
      (q + 11 * (1 / Real.sqrt q * q) + 6) / 16 := by
    field_simp
    ring
  have e2 : q / 16 * (1 - (11 * (1 / Real.sqrt q) + 70 / q)) =
      (q - 11 * (1 / Real.sqrt q * q) - 70) / 16 := by
    field_simp
    ring
  have hupper : (Φ.card : ℝ) ≤ q / 16 * (1 + (11 * (1 / Real.sqrt q) + 6 / q)) := by
    rw [e1, hrq]; linarith
  have hlower : q / 16 * (1 - (11 * (1 / Real.sqrt q) + 70 / q)) ≤ Φ.card := by
    rw [e2, hrq]; linarith
  refine ⟨hupper, hlower, ?_⟩
  have hsd : (Φ.card : ℝ) - K.card ≤ (Φ \ K).card := by
    have h := card_sdiff_add_card_inter Φ K
    have hi : (Φ ∩ K).card ≤ K.card := card_le_card inter_subset_right
    have h' : ((Φ \ K).card : ℝ) + (Φ ∩ K).card = Φ.card := by exact_mod_cast h
    have hi' : ((Φ ∩ K).card : ℝ) ≤ K.card := by exact_mod_cast hi
    linarith
  have hk : q / 16 * (1 - (11 * (1 / Real.sqrt q) + 70 / q) - 16 * K.card / q) =
      q / 16 * (1 - (11 * (1 / Real.sqrt q) + 70 / q)) - K.card := by
    field_simp
  rw [hk]
  linarith

end Sarkozy.Labellings
