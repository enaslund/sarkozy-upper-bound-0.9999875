module

public import Sarkozy.CompSharp.Form
public import Sarkozy.SignedDecomp.Main2

@[expose] public section

/-!
# The component norms of the paper's fold records at `34 r + 1000 q` and `38 r` (C38)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 1 ("every centred component
`Π_⊥ T[P_{uv,p}] Π_⊥` has norm at most `c_+ r`").

At every prime of every middle block, with SGA's components `compP` (B8's repaired `P_{uv}`, any
repair constants with the defect bound), at the same generality as SD2's `comp80_blockComponents`,
`comp80_paper`:
* **`comp34_blockComponents`**, **`comp34_paper`**: centred norm `≤ 34 r + 1000 q`
  (`r = p^{-1/2} = rP`, `q = 1/p = rP²`);
* **`comp38_blockComponents`**, **`comp38_paper`**: centred norm `≤ 38 r`;
* `comp35_paper`: `≤ 35 r`.

These have the shape of FD's field `FoldInputs.comp` (`CentredNorm (mP hne i) (compP hne C c i) _`)
with `c_+ r` replaced by `34 r + 1000 q` (resp. `38 r`); see `Sarkozy.CompSharp.FoldGen` for
the fold inputs at such a constant.
-/

open Finset

namespace Sarkozy.CompSharp

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents Sarkozy.Labellings
open Sarkozy.SignedDecomp
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
/-- `compP` of SGA's `blockComponents` is the repaired component at the prime. -/
theorem compP_blockComponents (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ι → Fin 3 → ℝ)
    (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c))
    (c : Fin 3) (i : ι) :
    compP hne (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) c i =
      fun a b => (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).repair (M i c) (a, b) := by
  funext a b
  change ((compLaw (h3 i) (h19 i) (hne.F2 i) ht0 ht1 (M i) (hM0 i) (hM i) c).map
    (placeEquiv 0)).weight (toY (a, b)) = _
  rw [map_equiv_weight, placeEquiv_zero_symm, lay_toY_zero, lay_toY_one]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **The centred components of a middle block have norm at most `δ(√p)`** for any `δ` with
`CompNumeric δ`, at primes `≥ 2²⁴`, for B8's components with any repair constants satisfying the
defect bound (`comp_centred_of`). -/
theorem compOf_blockComponents {δ : ℝ → ℝ} (hδ : CompNumeric δ) (h3 : ∀ i, pr i % 4 = 3)
    (h19 : ∀ i, 19 ≤ pr i) (hne : MiddleNonempty pr) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (M : ι → Fin 3 → ℝ) (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c))
    (h24 : ∀ i, 2 ^ 24 ≤ pr i) (c : Fin 3) (i : ι) :
    CentredNorm (mP hne i) (compP hne (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) c i)
      (δ (√(pr i : ℝ))) := by
  rw [compP_blockComponents]
  have hp : (2 : ℝ) ^ 24 ≤ (Fintype.card (ZMod (pr i)) : ℝ) := by
    rw [ZMod.card]; exact_mod_cast h24 i
  have h := comp_centred_of (ringChar_zmod_ne_two (h3 i)) (card_zmod_mod (h3 i))
    (card_zmod_ge (h19 i)) (hne.F2 i) ht0 ht1 hδ hp c (hM0 i c) (hM i c)
  rw [ZMod.card] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- **`34 r + 1000 q`** for the centred components of a middle block (`compOf_blockComponents` at
`compNumeric_34`). -/
theorem comp34_blockComponents (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ι → Fin 3 → ℝ)
    (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c))
    (h24 : ∀ i, 2 ^ 24 ≤ pr i) (c : Fin 3) (i : ι) :
    CentredNorm (mP hne i) (compP hne (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) c i)
      (34 * rP pr i + 1000 * rP pr i ^ 2) := by
  have h := compOf_blockComponents compNumeric_34 h3 h19 hne ht0 ht1 M hM0 hM h24 c i
  have e : 34 / √(pr i : ℝ) + 1000 / √(pr i : ℝ) ^ 2 = 34 * rP pr i + 1000 * rP pr i ^ 2 := by
    rw [rP, div_eq_mul_inv, div_eq_mul_inv, inv_pow]
  rw [← e]
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- **`38 r`** for the centred components of a middle block (`compOf_blockComponents` at
`compNumeric_38`). -/
theorem comp38_blockComponents (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ι → Fin 3 → ℝ)
    (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c))
    (h24 : ∀ i, 2 ^ 24 ≤ pr i) (c : Fin 3) (i : ι) :
    CentredNorm (mP hne i) (compP hne (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) c i)
      (38 * rP pr i) := by
  have h := compOf_blockComponents compNumeric_38 h3 h19 hne ht0 ht1 M hM0 hM h24 c i
  rwa [div_eq_mul_inv] at h

omit [Fintype ι] [DecidableEq ι] in
/-- **`35 r`** for the centred components of a middle block. -/
theorem comp35_blockComponents (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (hne : MiddleNonempty pr) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (M : ι → Fin 3 → ℝ)
    (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c))
    (h24 : ∀ i, 2 ^ 24 ≤ pr i) (c : Fin 3) (i : ι) :
    CentredNorm (mP hne i) (compP hne (blockComponents h3 h19 hne ht0 ht1 M hM0 hM) c i)
      (35 * rP pr i) := by
  have h := compOf_blockComponents compNumeric_35 h3 h19 hne ht0 ht1 M hM0 hM h24 c i
  rwa [div_eq_mul_inv] at h

end Block

section Paper

open Sarkozy.MainFinalF1 (bOf Blk)
open Sarkozy.PartVLaws (blockPrimes)

/-- The primes of a middle block of the F1 data are `≥ 2²⁴` (they are `≥ Q₃`). -/
theorem blockPrimes_ge24 (b : Blk) (j) : 2 ^ 24 ≤ blockPrimes bOf b j :=
  le_trans (by norm_num [PartV.Q3]) (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).2

/-- **`prop:signed-bounds`(c), Step 1, at `34 r + 1000 q`**: the centred components of the
paper's fold records (`paperComponents`, any defect constants) have norm at most
`34 r + 1000 q` at every prime of every middle block of the F1 data. This is the shape of FD's
`FoldInputs.comp` with `c_+ r` replaced by `34 r + 1000 q`. -/
theorem comp34_paper {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) (c : Fin 3) (i) :
    CentredNorm (mP hne i) (compP hne (paperComponents Dc) c i)
      (34 * rP (blockPrimes bOf b) i + 1000 * rP (blockPrimes bOf b) i ^ 2) :=
  comp34_blockComponents (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1)
    (blockPrimes_ge19 b) hne tPaper_nonneg tPaper_le_one Dc.M Dc.nonneg Dc.bound
    (blockPrimes_ge24 b) c i

/-- **`prop:signed-bounds`(c), Step 1, at `38 r`**: the centred components of the paper's fold
records have norm at most `38 r` at every prime of every middle block of the F1 data (FD's
`FoldInputs.comp` with `c_+ = 38`, remainder `0`). -/
theorem comp38_paper {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) (c : Fin 3) (i) :
    CentredNorm (mP hne i) (compP hne (paperComponents Dc) c i) (38 * rP (blockPrimes bOf b) i) :=
  comp38_blockComponents (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1)
    (blockPrimes_ge19 b) hne tPaper_nonneg tPaper_le_one Dc.M Dc.nonneg Dc.bound
    (blockPrimes_ge24 b) c i

/-- **`prop:signed-bounds`(c), Step 1, at `35 r`** for the paper's fold records. -/
theorem comp35_paper {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) (c : Fin 3) (i) :
    CentredNorm (mP hne i) (compP hne (paperComponents Dc) c i) (35 * rP (blockPrimes bOf b) i) :=
  comp35_blockComponents (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1)
    (blockPrimes_ge19 b) hne tPaper_nonneg tPaper_le_one Dc.M Dc.nonneg Dc.bound
    (blockPrimes_ge24 b) c i

end Paper

end Sarkozy.CompSharp
