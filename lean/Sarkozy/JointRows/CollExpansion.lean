module

public import Sarkozy.JointRows.CollBridge
public import Sarkozy.ExtractionK.PinnedExtraction

/-!
# The expansion of a pinned row kernel (`lem:spec:expansion`, pinned form)

Sources: `paper/sections/14_spectral.tex`, `lem:spec:expansion` (`∏_e (1 + χ_e) = ∑_S χ_S`, with
`χ_∅ = 1`, the star part and the nonstar part); `paper/sections/16_extraction.tex`,
`prop:conditional-star` (the star part: single pairs, row stars and column stars) and
`lem:joint-rows` (`K_•`, `K^st_•`, `T^•_ns`, `T^•_coll`).

For sign data `ς` (`E_× = pairSet ς`, the pairs with `ς_ij ≠ 0`):
* `starKer ς = ∑_{S ⊆ E_× star} χ_S` and `nsKer ς = ∑_{S ⊆ E_× nonstar} χ_S`, with
  `χ_S = ∏_{e ∈ S} χ_e` and X1's `ExtractionK.chiPair` for `χ_e`. The stars and nonstars are those
  of `Extraction.IsStar`, `Extraction.nonstars`; a star is nonempty, so `∅` is neither.
* `prod_pinOmega`: `∏_j ω_j(y_j) = ∏_{e ∈ E_×} (1 + χ_e)`.
* `expansion`: `∏_{e ∈ E_×} (1 + χ_e) = 1 + starKer ς + nsKer ς`.
* `rawKer_expansion`: `K_• = 1 + K^st_• + T^•_ns - T^•_coll` for `K_• = rawKer ς`,
  `K^st_• = starKer ς`, `T^•_ns = nsKer ς`, `T^•_coll = pinKer ς`. This is the hypothesis `hexpE`
  of `lem:joint-rows`(a), now proved for the concrete kernels.
* `chiPair_eq`: `χ_ij(x, y) = ς_ij χ(y_j - x_i)` at `p ≡ 3 (mod 4)`, the link to the kernel
  `∏ (1 + D_ij χ(y_j - x_i))` of `prop:conditional-star`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

namespace Coll

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {nv : ℕ}

/-- `E_×`: the pairs `(i, j)` with `ς_ij ≠ 0`. -/
def pairSet (ς : Fin nv → Fin nv → ℤ) : Finset (Fin nv × Fin nv) :=
  Finset.univ.filter fun e => ς e.1 e.2 ≠ 0

/-- The star sets of `E_×`. -/
def starSets (ς : Fin nv → Fin nv → ℤ) : Finset (Finset (Fin nv × Fin nv)) :=
  (pairSet ς).powerset.filter Extraction.IsStar

/-- **The star part `K^st`**: `∑_{S ⊆ E_× star} χ_S`. -/
noncomputable def starKer (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → F) : ℝ :=
  ∑ S ∈ starSets ς, ∏ e ∈ S, ExtractionK.chiPair ς e x y

/-- **The nonstar part `T_ns`**: `∑_{S ⊆ E_× nonstar} χ_S`. -/
noncomputable def nsKer (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → F) : ℝ :=
  ∑ S ∈ Extraction.nonstars (pairSet ς), ∏ e ∈ S, ExtractionK.chiPair ς e x y

/-- `∏_j ω_j(y_j) = ∏_{e ∈ E_×} (1 + χ_e)`. -/
theorem prod_pinOmega (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → F) :
    ∏ j, ExtractionK.pinOmega ς x j (y j) =
      ∏ e ∈ pairSet ς, (1 + ExtractionK.chiPair ς e x y) := by
  unfold pairSet ExtractionK.pinOmega ExtractionK.pinNY
  rw [Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_filter]
  rfl

/-- The powerset of `E_×` is `{∅}`, the stars and the nonstars, disjointly. -/
theorem sum_powerset_split (s : Finset (Fin nv × Fin nv)) (G : Finset (Fin nv × Fin nv) → ℝ) :
    ∑ t ∈ s.powerset, G t = G ∅ + ∑ t ∈ s.powerset.filter Extraction.IsStar, G t +
      ∑ t ∈ Extraction.nonstars s, G t := by
  have h1 : ¬ Extraction.IsStar (∅ : Finset (Fin nv × Fin nv)) := by
    simp [Extraction.IsStar, Extraction.IsRowStar, Extraction.IsColStar]
  have h2 : ¬ Extraction.IsNonstar (∅ : Finset (Fin nv × Fin nv)) := by
    simp [Extraction.IsNonstar]
  have h : ∀ t, G t = (if t = ∅ then G t else 0) + (if Extraction.IsStar t then G t else 0) +
      (if Extraction.IsNonstar t then G t else 0) := by
    intro t
    by_cases h0 : t = ∅
    · subst h0
      simp only [h1, h2, ↓reduceIte, add_zero]
    · by_cases hs : Extraction.IsStar t
      · have hn : ¬ Extraction.IsNonstar t := fun h => h.2 hs
        simp only [h0, hs, hn, ↓reduceIte, zero_add, add_zero]
      · have hn : Extraction.IsNonstar t := ⟨Finset.nonempty_iff_ne_empty.mpr h0, hs⟩
        simp only [h0, hs, hn, ↓reduceIte, zero_add]
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.empty_mem_powerset, ↓reduceIte, Extraction.nonstars]

/-- **`lem:spec:expansion` for a pinned row**: `∏_{e ∈ E_×} (1 + χ_e) = 1 + K^st + T_ns`. -/
theorem expansion (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → F) :
    ∏ e ∈ pairSet ς, (1 + ExtractionK.chiPair ς e x y) = 1 + starKer ς x y + nsKer ς x y := by
  rw [Finset.prod_one_add, sum_powerset_split, Finset.prod_empty]
  rfl

/-- **The expansion `K_• = 1 + K^st_• + T^•_ns - T^•_coll`** (`lem:spec:expansion`) for the
concrete kernels of a pinned row. -/
theorem rawKer_expansion (ς : Fin nv → Fin nv → ℤ) (x y : Fin nv → F) :
    rawKer ς x y = 1 + starKer ς x y + nsKer ς x y - ExtractionK.pinKer ς x y := by
  have h := rawKer_add_pinKer ς x y
  rw [prod_pinOmega, expansion] at h
  linarith

/-- **`χ_ij(x, y) = D_ij χ(y_j - x_i)`** at `p ≡ 3 (mod 4)` for signs `D_ij ∈ {0, ±1}` (the
remark in `prop:conditional-star`: `χ(ς_ij) = ς_ij`), with `PaleyGauss.chiR` the real quadratic
character. So `starKer D_•` is the star part of `∏_{i,j} (1 + D_ij χ(y_j - x_i))` in the sense
of `prop:conditional-star`. -/
theorem chiPair_eq {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (ς : Fin nv → Fin nv → ℤ)
    {i j : Fin nv} (hς : ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (x y : Fin nv → ZMod p) :
    ExtractionK.chiPair ς (i, j) x y = (ς i j : ℝ) * PaleyGauss.chiR p (y j - x i) := by
  unfold ExtractionK.chiPair PaleyGauss.chiR
  rw [map_mul]
  rcases hς with h | h | h <;> rw [h]
  · simp
  · simp
  · rw [Int.cast_neg, Int.cast_one, PaleyGauss.chi_neg_one hp]
    push_cast
    ring

end Coll

end Sarkozy.JointRows
