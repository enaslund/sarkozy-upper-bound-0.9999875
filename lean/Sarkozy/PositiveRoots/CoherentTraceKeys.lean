module

public import Sarkozy.PositiveRoots.CoherentTraceMatrix

/-!
# The physical score coefficients as an explicit key list

`chamberCoeff a b` maps over the whole dictionary for every pair of features. Each entry of
`dictionary39` has the chamber codes `leftCode`, `rightCode` and the sign of its coefficient;
these keys are evaluated once (`traceKeys_eq`), and every coefficient numerator is a sum over
the keys (`coefficientNumerator_eq_keys`). The row sums are checked on the keys of each row
(`traceKeys_rows`), and symmetry follows because the keys are invariant, up to order, under
swapping the two codes (`traceKeys_swap`).
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV.CoherentDictionary

/-- The left code, right code and coefficient sign of each entry of `dictionary39`. -/
def traceKeys : List (ℕ × ℕ × ℤ) :=
  [(15, 52, -1), (15, 60, 1), (15, 56, -1), (15, 28, -1), (15, 44, -1), (7, 60, 1),
    (7, 56, -1), (11, 52, -1), (11, 60, 1), (51, 49, -1), (51, 51, 1), (51, 50, -1),
    (51, 19, 1), (51, 35, 1), (19, 51, 1), (19, 50, -1), (35, 49, -1), (35, 51, 1),
    (13, 60, 1), (13, 44, -1), (49, 51, -1), (49, 35, -1), (14, 60, 1), (14, 28, -1),
    (50, 51, -1), (50, 19, -1), (60, 13, 1), (60, 15, 1), (60, 14, 1), (60, 7, 1),
    (60, 11, 1), (28, 15, -1), (28, 14, -1), (44, 13, -1), (44, 15, -1), (52, 15, -1),
    (52, 11, -1), (56, 15, -1), (56, 7, -1)]

theorem traceKeys_eq :
    dictionary39.map (fun sc => (CoherentMatrix.leftCode sc.1, CoherentMatrix.rightCode sc.1,
      if 0 < sc.2 then (1 : ℤ) else -1)) = traceKeys := by
  decide +kernel

/-- The sum of the signs of the keys with codes `i` and `j`. -/
def keyCell (K : List (ℕ × ℕ × ℤ)) (i j : ℕ) : ℤ :=
  (K.map fun k => if k.1 = i ∧ k.2.1 = j then k.2.2 else 0).sum

/-- The keys with left code `i`. -/
def keyRow (K : List (ℕ × ℕ × ℤ)) (i : ℕ) : List (ℕ × ℕ × ℤ) :=
  K.filter fun k => k.1 = i

theorem keyCell_keyRow (K : List (ℕ × ℕ × ℤ)) (i j : ℕ) :
    keyCell K i j = keyCell (keyRow K i) i j := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    unfold keyCell keyRow at *
    rw [List.filter_cons]
    by_cases h : k.1 = i
    · simp [h, ih]
    · simp [h, ih]

theorem keyCell_swap (K : List (ℕ × ℕ × ℤ)) (i j : ℕ) :
    keyCell K i j = keyCell (K.map fun k => (k.2.1, k.1, k.2.2)) j i := by
  unfold keyCell
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_apply, and_comm]

theorem keyCell_perm {K K' : List (ℕ × ℕ × ℤ)} (h : K'.Perm K) (i j : ℕ) :
    keyCell K' i j = keyCell K i j := by
  unfold keyCell
  exact (h.map _).sum_eq

theorem coefficientNumerator_eq_keys (i j : Fin 64) :
    CoherentMatrix.coefficientNumerator i j = keyCell traceKeys i.val j.val := by
  rw [← traceKeys_eq]
  unfold CoherentMatrix.coefficientNumerator keyCell
  rw [List.map_map]
  rfl

theorem traceKeys_rows : ∀ i : Fin 64,
    ∑ j : Fin 64, (keyCell (keyRow traceKeys i.val) i.val j.val).natAbs ≤ 5 := by
  decide +kernel

theorem traceKeys_swap : (traceKeys.map fun k => (k.2.1, k.1, k.2.2)).Perm traceKeys := by
  decide +kernel

theorem chamberCoeff_eq_keys (a b : Feature) :
    chamberCoeff a b = (keyCell traceKeys (CoherentOldChamber.index a).val
      (CoherentOldChamber.index b).val : ℚ) / 15 := by
  rw [chamberCoeff_eq, CoherentMatrix.coefficient_eq, coefficientNumerator_eq_keys]

theorem chamberCoeff_symm_keys (a b : Feature) : chamberCoeff a b = chamberCoeff b a := by
  rw [chamberCoeff_eq_keys, chamberCoeff_eq_keys, keyCell_swap, keyCell_perm traceKeys_swap]

theorem chamberCoeff_row_keys (a : Feature) : (∑ b, |chamberCoeff a b|) ≤ 1 / 3 := by
  have h1 : ∀ b, |chamberCoeff a b| = ((keyCell traceKeys (CoherentOldChamber.index a).val
      (CoherentOldChamber.index b).val).natAbs : ℚ) / 15 := by
    intro b
    rw [chamberCoeff_eq_keys, abs_div, ← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hm : ∀ f : Fin 64 → ℕ,
      ∑ b : Feature, f (CoherentOldChamber.index b) ≤ ∑ j, f j := by
    intro f
    calc ∑ b : Feature, f (CoherentOldChamber.index b)
        = ∑ x ∈ univ.map CoherentOldChamber.embedding, f x := by rw [Finset.sum_map]; rfl
      _ ≤ ∑ j, f j := Finset.sum_le_sum_of_subset (subset_univ _)
  have h3 := hm (fun j => (keyCell traceKeys (CoherentOldChamber.index a).val j.val).natAbs)
  have h4 := traceKeys_rows (CoherentOldChamber.index a)
  simp only [← keyCell_keyRow] at h4
  rw [Finset.sum_congr rfl (fun b _ => h1 b), ← Finset.sum_div]
  have h5 : (∑ b : Feature, ((keyCell traceKeys (CoherentOldChamber.index a).val
      (CoherentOldChamber.index b).val).natAbs : ℚ)) ≤ 5 := by
    exact_mod_cast h3.trans h4
  linarith

end Sarkozy.PositiveRoots.CoherentFrame
