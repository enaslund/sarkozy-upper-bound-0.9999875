module

public import Sarkozy.PartV.CoherentDictionary
public import Sarkozy.SpectralD.GaussianCertificate

/-!
# The selected coherent-root chamber matrix

The half coordinates are `(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)`.
All 64 subsets are included; the empty and inactive supports have zero
leading entries. The dictionary coefficients are collected in the reflected
chart of `check_coherent_39_selected_matrix.py`, directly from `dictionary39`.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentMatrix

open Finset Sarkozy.PartV.CoherentDictionary Sarkozy.Labellings

def halfVertex (i : Fin 6) : Vertex :=
  ((i.val / 2 : ℕ), ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩)

def sign (i j : Fin 6) : ℤ :=
  (if (halfVertex i, reflect (halfVertex j)) ∈ (recordGraph (Fin 2)).E then 1 else 0) -
    (if (reflect (halfVertex j), halfVertex i) ∈ (recordGraph (Fin 2)).E then 1 else 0)

def support (i : Fin 64) : Finset (Fin 6) := univ.filter fun a => i.val.testBit a.val

def starReal (i j : Fin 64) : ℤ :=
  (if 2 ≤ (support i).card ∧ (support j).card = 1 then
    ∑ b ∈ support j, ∏ a ∈ support i, sign a b else 0) +
  (if (support i).card = 1 ∧ 2 ≤ (support j).card then
    ∑ a ∈ support i, ∏ b ∈ support j, sign b a else 0)

def starImag (i j : Fin 64) : ℤ :=
  if (support i).card = 1 ∧ (support j).card = 1 then
    ∑ a ∈ support i, ∑ b ∈ support j, sign a b else 0

def leftCode (s : Support) : ℕ :=
  ∑ v ∈ s, if v.1.val < 3 then 2 ^ (2 * v.1.val + v.2.val) else 0

def rightCode (s : Support) : ℕ :=
  ∑ v ∈ s, if 3 ≤ v.1.val then 2 ^ (2 * (5 - v.1.val) + v.2.val) else 0

def coefficient (i j : Fin 64) : ℚ :=
  (dictionary39.map fun sc =>
    if leftCode sc.1 = i.val ∧ rightCode sc.1 = j.val then sc.2 else 0).sum

def coefficientNumerator (i j : Fin 64) : ℤ :=
  (dictionary39.map fun sc =>
    if leftCode sc.1 = i.val ∧ rightCode sc.1 = j.val then
      (if 0 < sc.2 then 1 else -1) else 0).sum

theorem coefficient_eq : ∀ i j : Fin 64,
    coefficient i j = (coefficientNumerator i j : ℚ) / 15 := by
  have hc : ∀ sc ∈ dictionary39, sc.2 = (if 0 < sc.2 then (1 : ℤ) else -1) / (15 : ℚ) := by
    decide +kernel
  intro i j
  unfold coefficient coefficientNumerator
  rw [Int.cast_list_sum, div_eq_mul_inv, List.map_map, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc hsc
  dsimp only [Function.comp_def]
  split_ifs with h hpos
  · simpa only [hpos, ite_true, Int.cast_one, one_mul, one_div] using hc sc hsc
  · simpa only [hpos, ite_false, Int.cast_neg, Int.cast_one, div_eq_mul_inv] using hc sc hsc
  · simp

def denominator : ℤ := 1122231250000
def cap : ℚ := 541674864 / 100000000
def strength : ℚ := 402000 / 179557

def modelReal (i j : Fin 64) : ℤ :=
  denominator * starReal i j + 167500000000 * coefficientNumerator i j +
    (if i = j then 6078844597203 else 0)

def modelImag (i j : Fin 64) : ℤ := denominator * starImag i j

noncomputable def leading (i j : Fin 64) : ℂ :=
  Sarkozy.SpectralD.gaussian (starReal i j) (starImag i j) +
    ((strength * coefficient i j : ℚ) : ℂ)

end Sarkozy.PositiveRoots.CoherentMatrix
