module

public import Sarkozy.L20Cap.RectX1
public import Sarkozy.L20Cap.Caps
public import Sarkozy.L20Cap.StarMatrix
public import Sarkozy.ExtractionK.Defs

/-!
# The eight-edge nonstar kernel in X1's form (`prop:l20-rectangular`(b))

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-rectangular`(b): "Expand
`𝖱 = ∏(1 + s_kχ(b_l - x_k))` over the eight cross pairs … into its `256` subset terms: the
constant, `34` stars … and `221` nonstars". Here the eight cross pairs are
`Ex8 = {0, 1, 4, 5} × {2, 3}` (core coordinates of `x`, pair coordinates of `x'`, in the
coordinates `(a₀, a₁, b₀, b₁, c₀, c₁)` of the half), with the signs of `D₂₀` (`D20Z`), in the
notation of X1's `ExtractionK` (`chiPair`, WP-FI's `nonstars`, `IsStar`).

* `chiPair_Ex8`: `χ_e(x, x') = (D₂₀)_e χ(x'_j - x_i)` for `e = (i, j) ∈ Ex8` (`χ(-1) = -1`);
* `emptyOrStar_Ex8`: the empty set and the `34` stars of `Ex8` are the subsets of the two columns
  and the four row pairs `{(i, 2), (i, 3)}` (`decide`); `card_nonstars_Ex8 = 221`;
* `sum_nonstars_Ex8`: for any weights `w`,
  `∑_{S nonstar} ∏_{e∈S} w_e = (∏_i(1 + w_{i2}) - 1)(∏_i(1 + w_{i3}) - 1) - ∑_i w_{i2}w_{i3}`;
* **`nonstar_eq_Nrect`**: X1's soft nonstar class sum of the eight-edge kernel at the halves `x`,
  `x'` (`Dsk = 1`) is `N(C(x); b(x'))` (`Nrect`): the kernel `NrectH` of `RectX1` is exactly the
  kernel to which `cor:soft-kernels`(a) applies.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Extraction Sarkozy.ExtractionK

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The core coordinates `0, 1, 4, 5` of a half. -/
def coreIdx : Finset (Fin 6) := {0, 1, 4, 5}

/-- The two columns of `Ex8`: the pairs `(i, j)`, `i` a core coordinate. -/
def col8 (j : Fin 6) : Finset (Fin 6 × Fin 6) := coreIdx ×ˢ {j}

/-- **The eight cross pairs** of the rectangle: core coordinates of `x` × pair coordinates of
`x'`. -/
def Ex8 : Finset (Fin 6 × Fin 6) := coreIdx ×ˢ {2, 3}

/-- The row pairs `{(i, 2), (i, 3)}`. -/
def rowPairs8 : Finset (Finset (Fin 6 × Fin 6)) := coreIdx.image fun i => {(i, 2), (i, 3)}

theorem Ex8_eq : Ex8 = col8 2 ∪ col8 3 := by decide

theorem col8_disj : Disjoint (col8 2) (col8 3) := by decide

/-- **The empty set and the stars of `Ex8`**: the subsets of a column, and the four row pairs. -/
theorem emptyOrStar_Ex8 :
    (Ex8.powerset.filter fun S => S = ∅ ∨ IsStar S) =
      ((col8 2).powerset ∪ (col8 3).powerset) ∪ rowPairs8 := by
  decide +kernel

theorem card_nonstars_Ex8 : (nonstars Ex8).card = 221 := by decide +kernel

theorem cols_inter : (col8 2).powerset ∩ (col8 3).powerset = {∅} := by decide

theorem cols_rows_disj : Disjoint ((col8 2).powerset ∪ (col8 3).powerset) rowPairs8 := by
  decide +kernel

/-- **The nonstar sum of the eight cross pairs**, for any weights `w`. -/
theorem sum_nonstars_Ex8 (w : Fin 6 × Fin 6 → ℝ) :
    ∑ S ∈ nonstars Ex8, ∏ e ∈ S, w e =
      ((∏ e ∈ col8 2, (1 + w e)) - 1) * ((∏ e ∈ col8 3, (1 + w e)) - 1) -
        ∑ i ∈ coreIdx, w (i, 2) * w (i, 3) := by
  -- the full sum
  have hall : ∑ S ∈ Ex8.powerset, ∏ e ∈ S, w e =
      (∏ e ∈ col8 2, (1 + w e)) * ∏ e ∈ col8 3, (1 + w e) := by
    rw [← prod_one_add, Ex8_eq, prod_union col8_disj]
  -- the empty set and the stars
  have hstar : ∑ S ∈ Ex8.powerset.filter (fun S => S = ∅ ∨ IsStar S), ∏ e ∈ S, w e =
      (∏ e ∈ col8 2, (1 + w e)) + (∏ e ∈ col8 3, (1 + w e)) - 1 +
        ∑ i ∈ coreIdx, w (i, 2) * w (i, 3) := by
    rw [emptyOrStar_Ex8, sum_union cols_rows_disj]
    have hu := sum_union_inter (s₁ := (col8 2).powerset) (s₂ := (col8 3).powerset)
      (f := fun S => ∏ e ∈ S, w e)
    rw [cols_inter, sum_singleton, prod_empty, ← prod_one_add, ← prod_one_add] at hu
    have hr : ∑ S ∈ rowPairs8, ∏ e ∈ S, w e = ∑ i ∈ coreIdx, w (i, 2) * w (i, 3) := by
      unfold rowPairs8
      rw [sum_image (by decide)]
      refine sum_congr rfl fun i _ => ?_
      rw [prod_pair (by simp)]
    rw [hr]
    linarith
  have hsplit := sum_filter_add_sum_filter_not Ex8.powerset (fun S => S = ∅ ∨ IsStar S)
    (fun S => ∏ e ∈ S, w e)
  have hns : (Ex8.powerset.filter fun S => ¬(S = ∅ ∨ IsStar S)) = nonstars Ex8 := by
    ext S
    simp only [nonstars, mem_filter, isNonstar_iff_not]
  rw [hns, hstar, hall] at hsplit
  linarith

/-- `χ_e(x, x') = (D₂₀)_e χ(x'_j - x_i)` on the eight cross pairs. -/
theorem chiPair_Ex8 (hm1 : quadraticChar F (-1) = -1) {e : Fin 6 × Fin 6} (he : e ∈ Ex8)
    (x x' : Fin 6 → F) :
    chiPair D20Z e x x' = (D20Z e.1 e.2 : ℝ) * chi (x' e.2 - x e.1) := by
  have hpm : D20Z e.1 e.2 = 1 ∨ D20Z e.1 e.2 = -1 := by
    revert he; revert e; decide
  unfold chiPair
  rcases hpm with h | h
  · rw [h]; simp [chi]
  · rw [h]
    have e1 : ((-1 : ℤ) : F) * (x' e.2 - x e.1) = -(x' e.2 - x e.1) := by push_cast; ring
    rw [e1]
    have := chi_neg hm1 (x' e.2 - x e.1)
    simp only [chi] at this
    rw [this]
    simp [chi]

/-- **X1's soft nonstar class sum of the eight-edge kernel is `N(C(x); b(x'))`**
(`prop:l20-rectangular`(b): "the eight-edge kernel uses the same `221` subsets"), with `Dsk = 1`
and the signs of `D₂₀`. -/
theorem nonstar_eq_Nrect (hm1 : quadraticChar F (-1) = -1) (x x' : CoreT F × PairT F) :
    ∑ S ∈ nonstars Ex8, ∏ e ∈ S, ((1 : ℝ) * chiPair D20Z e (labels x) (labels x')) =
      NrectH x x' := by
  have hS : ∀ S ∈ nonstars Ex8, ∏ e ∈ S, ((1 : ℝ) * chiPair D20Z e (labels x) (labels x')) =
      ∏ e ∈ S, (D20Z e.1 e.2 : ℝ) * chi (labels x' e.2 - labels x e.1) := by
    intro S hS
    have hsub : S ⊆ Ex8 := by
      simp only [nonstars, mem_filter, mem_powerset] at hS
      exact hS.1
    refine prod_congr rfl fun e he => ?_
    rw [one_mul, chiPair_Ex8 hm1 (hsub he)]
  rw [sum_congr rfl hS,
    sum_nonstars_Ex8 (fun e => (D20Z e.1 e.2 : ℝ) * chi (labels x' e.2 - labels x e.1))]
  obtain ⟨⟨C, hC⟩, ⟨b, hb⟩⟩ := x
  obtain ⟨⟨C', hC'⟩, ⟨b', hb'⟩⟩ := x'
  simp only [NrectH, Nrect, col8, coreIdx, labels, emb, Kz_four]
  simp [Fin.sum_univ_four, D20Z, sum_insert, prod_insert]
  ring

end Sarkozy.L20Cap
