module

public import Sarkozy.SecondOrder.MovingRoot

/-!
# The star-trace dictionary (`lem:star-trace`) and the star expansion (`eq:star-function`)

`paper/sections/15_second_order.tex`. For a labelling `x : U → 𝔽_p` and `T ⊆ U`, the star mean is
`w_T(x) = E_z ∏_{j∈T} χ(z - x_j)` (`starW`).

* `starW_singleton`: `w_{{j}} = 0`.
* `starW_pair`: `w_{{j,k}} = -1/p` for injective `x` and `j ≠ k` (by `eq:two-root`).
* `starW_eq_tau`: for injective `x` and `i ∈ T`, `w_T(x) = τ_{x(T∖{i})}(x_i) - [|T| even]/p`. The
  paper states this for `|T| ≥ 3`; the identity holds for every `T ∋ i`.
* `starW_signs`: `E_z ∏_{j∈T} χ(ς_j(z - x_j)) = (∏_{j∈T} χ(ς_j)) w_T(x)`.
* `star_expand`: the expansion of one centre's contribution to the star function
  (`eq:star-function`), `E_z ∏_{j∈N}(1 + χ(ς_j(z - x_j))) - 1 = ∑_{∅≠T⊆N} (∏_{j∈T} χ(ς_j)) w_T(x)`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target Sarkozy.Labellings

variable {p : ℕ} [hp : Fact p.Prime] {U : Type*} [DecidableEq U]

/-- The star mean `w_T(x) = E_z ∏_{j∈T} χ(z - x_j)`. -/
noncomputable def starW (x : U → ZMod p) (T : Finset U) : ℝ :=
  (1 / (p : ℝ)) * ∑ z, ∏ j ∈ T, ((quadraticChar (ZMod p) (z - x j) : ℤ) : ℝ)

omit [DecidableEq U] in
theorem prod_chi_eq (x : U → ZMod p) (T : Finset U) (z : ZMod p) :
    ∏ j ∈ T, ((quadraticChar (ZMod p) (z - x j) : ℤ) : ℝ) =
      ((quadraticChar (ZMod p) (∏ j ∈ T, (z - x j)) : ℤ) : ℝ) := by
  rw [map_prod, Int.cast_prod]

theorem sum_chi_sub (hp2 : p ≠ 2) (a : ZMod p) :
    ∑ z, quadraticChar (ZMod p) (z - a) = 0 :=
  (Equiv.sum_comp (Equiv.subRight a) (fun z => quadraticChar (ZMod p) z)).trans
    (quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; exact hp2))

omit [DecidableEq U] in
/-- `w_{{j}} = 0`. -/
theorem starW_singleton (hp2 : p ≠ 2) (x : U → ZMod p) (j : U) : starW x {j} = 0 := by
  unfold starW
  simp only [prod_singleton]
  rw [show ∑ z, ((quadraticChar (ZMod p) (z - x j) : ℤ) : ℝ) =
      ((∑ z, quadraticChar (ZMod p) (z - x j) : ℤ) : ℝ) by push_cast; rfl, sum_chi_sub hp2]
  simp

/-- `w_{{j,k}} = -1/p` for injective `x` and `j ≠ k`. -/
theorem starW_pair (hp2 : p ≠ 2) {x : U → ZMod p} (hx : Function.Injective x) {j k : U}
    (hjk : j ≠ k) : starW x {j, k} = -1 / p := by
  unfold starW
  have h := two_root (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2) (hx.ne hjk)
  unfold rootSum at h
  have hprod : ∀ z, ∏ i ∈ ({j, k} : Finset U), ((quadraticChar (ZMod p) (z - x i) : ℤ) : ℝ) =
      ((quadraticChar (ZMod p) (∏ c ∈ ({x j, x k} : Finset (ZMod p)), (z - c)) : ℤ) : ℝ) := by
    intro z
    rw [prod_pair hjk, prod_pair (hx.ne hjk), map_mul, Int.cast_mul]
  rw [sum_congr rfl fun z _ => hprod z, ← Int.cast_sum, h]
  push_cast
  ring

/-- **`lem:star-trace`**: `w_T(x) = τ_{x(T∖{i})}(x_i) - [|T| even]/p` for injective `x`, `i ∈ T`. -/
theorem starW_eq_tau {x : U → ZMod p} (hx : Function.Injective x) {T : Finset U} {i : U}
    (hi : i ∈ T) :
    starW x T =
      tau p ((T.erase i).image x) (x i) - (if Even T.card then 1 / (p : ℝ) else 0) := by
  have hT1 : 1 ≤ T.card := card_pos.mpr ⟨i, hi⟩
  have hcard : ((T.erase i).image x).card = T.card - 1 := by
    rw [card_image_of_injective _ hx, card_erase_of_mem hi]
  have hodd : Odd ((T.erase i).image x).card ↔ Even T.card := by
    rw [hcard]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m + 1, by omega⟩
    · rintro ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
  have hfac : ∀ z, ∏ j ∈ T, (z - x j) = (∏ a ∈ (T.erase i).image x, (z - a)) * (z - x i) := by
    intro z
    rw [prod_image (fun a _ b _ h => hx h)]
    exact (prod_erase_mul T (fun j => z - x j) hi).symm
  have hsum : ∑ z, ∏ j ∈ T, ((quadraticChar (ZMod p) (z - x j) : ℤ) : ℝ) =
      ((∑ y, quadraticChar (ZMod p) ((∏ a ∈ (T.erase i).image x, (y - a)) * (y - x i)) : ℤ) :
        ℝ) := by
    push_cast
    refine sum_congr rfl fun z _ => ?_
    rw [prod_chi_eq, hfac z]
  unfold starW tau
  rw [hsum]
  by_cases he : Even T.card
  · have ho : Odd ((T.erase i).image x).card := hodd.mpr he
    simp only [ho, he, ↓reduceIte]
    ring
  · have ho : ¬ Odd ((T.erase i).image x).card := fun h => he (hodd.mp h)
    simp only [ho, he, ↓reduceIte]
    ring

omit [DecidableEq U] in
/-- **`lem:star-trace`, signs**: `E_z ∏_{j∈T} χ(ς_j(z - x_j)) = (∏_{j∈T} χ(ς_j)) w_T(x)`. -/
theorem starW_signs (x : U → ZMod p) (T : Finset U) (ς : U → ZMod p) :
    (1 / (p : ℝ)) * ∑ z, ∏ j ∈ T, ((quadraticChar (ZMod p) (ς j * (z - x j)) : ℤ) : ℝ) =
      (∏ j ∈ T, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * starW x T := by
  have h : ∀ z, ∏ j ∈ T, ((quadraticChar (ZMod p) (ς j * (z - x j)) : ℤ) : ℝ) =
      (∏ j ∈ T, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
        ∏ j ∈ T, ((quadraticChar (ZMod p) (z - x j) : ℤ) : ℝ) := by
    intro z
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [map_mul, Int.cast_mul]
  unfold starW
  simp_rw [h, ← mul_sum]
  ring

omit [DecidableEq U] in
theorem starW_empty (x : U → ZMod p) : starW x ∅ = 1 := by
  unfold starW
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [prod_empty, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  field_simp

/-- **The star expansion** (`eq:star-function`) for one centre with neighbourhood `N` and signs
`ς`: `E_z ∏_{j∈N}(1 + χ(ς_j(z - x_j))) - 1 = ∑_{∅≠T⊆N} (∏_{j∈T} χ(ς_j)) w_T(x)`. -/
theorem star_expand (x : U → ZMod p) (N : Finset U) (ς : U → ZMod p) :
    (1 / (p : ℝ)) * ∑ z, ∏ j ∈ N, (1 + ((quadraticChar (ZMod p) (ς j * (z - x j)) : ℤ) : ℝ)) -
        1 =
      ∑ T ∈ N.powerset.erase ∅, (∏ j ∈ T, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) *
        starW x T := by
  have hexp : (1 / (p : ℝ)) *
      ∑ z, ∏ j ∈ N, (1 + ((quadraticChar (ZMod p) (ς j * (z - x j)) : ℤ) : ℝ)) =
      ∑ T ∈ N.powerset, (∏ j ∈ T, ((quadraticChar (ZMod p) (ς j) : ℤ) : ℝ)) * starW x T := by
    simp_rw [prod_one_add]
    rw [sum_comm, mul_sum]
    exact sum_congr rfl fun T _ => starW_signs x T ς
  rw [hexp, ← add_sum_erase _ _ (empty_mem_powerset N), prod_empty, starW_empty]
  ring

end Sarkozy.SecondOrder
