module

public import Sarkozy.NormBoundsPaper.Merge2
public import Sarkozy.MainFinalF1.K2

@[expose] public section

/-!
# `NormBounds` and the field `hN` from the remaining families

B8's `NormBounds` (10 fields; twelve changed records, two parts each) with the constant fields
`Cs`, `Ca` (`lem:record:accepting-c2`, `Sarkozy.NormBoundsPaper.Const`) and the first-coordinate
merge skew field `Ma₂` (`lem:merge-repair`, `Sarkozy.NormBoundsPaper.Merge2`) proved:

* **`NormBoundsRest`**: the seven remaining fields, verbatim from `NormBounds`:
  `Fs`, `Fa` (`prop:signed-bounds`(a),(b),(e)), `Es`, `Ea` (`lem:record:exact-marginal-e`(ii)),
  `Ms`, `Ma`, `Ms₂` (the table of `lem:merge-repair`). *Hypotheses.*
* **`NormBoundsRest.toNormBounds`**: `NormBounds` from them, for `r = b^{-1/2}` and `b ≥ 7` below
  every prime of the block.
* **`SpecNormBoundsRest`**, **`specNormBounds_of_rest`**: the same at the level of K2's
  `SpecNormBounds` (any root), with the scale `r² b = 1` of the block specification.
* **`hN_of_rest`**: the field `hN` of `Sarkozy.MainCombined.MainFinalObligationsG` (and of every
  statement taking `SpecNormBounds` at the paper's partition) from the seven remaining families at
  the same piece constants `κ` (in particular at `paperKappa`). The proved fields do not depend on
  `κ`.
-/

namespace Sarkozy.NormBoundsPaper

open Finset
open scoped BigOperators

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords

/-! ## The frame -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **The seven families of `NormBounds` not proved here** (all hypotheses):
* `Fs`, `Fa`: the folds, `prop:signed-bounds`(a),(b),(e): `s_F r²` and `ℓ r + a_F r²`;
* `Es`, `Ea`: the matchings, `lem:record:exact-marginal-e`(ii): `s_E r` and `a_E r`;
* `Ms`, `Ma`: the mirror-edge merges, the table of `lem:merge-repair`: `s^G_b`, `a^G_b`;
* `Ms₂`: the first-coordinate merges, symmetric part, the table of `lem:merge-repair`:
  `d_b + η_b`.
The constants `Cs`, `Ca` (`lem:record:accepting-c2`) and the first-coordinate skew part `Ma₂`
(`lem:merge-repair`) are proved (`const_sym_paper`, `const_skew_paper`, `merge2_skew_paper`). -/
structure NormBoundsRest (C : FoldComponents pr hne) (t b' sF aF ℓ sE aE : ℝ) : Prop where
  Fs : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .sym) (sF * (1 / Real.sqrt b') ^ 2)
  Fa : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .skew)
    (ℓ * (1 / Real.sqrt b') + aF * (1 / Real.sqrt b') ^ 2)
  Es : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl i)))
    (foldChange pr h hne root W I hr b C t (.inr (.inl i)) .sym) (sE * (1 / Real.sqrt b'))
  Ea : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl i)))
    (foldChange pr h hne root W I hr b C t (.inr (.inl i)) .skew) (aE * (1 / Real.sqrt b'))
  Ms : ∀ s k, k ≠ 2 → FormBound reservedCut
    (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, k)))))
    (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .sym) (sG b')
  Ma : ∀ s k, k ≠ 2 → FormBound reservedCut
    (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, k)))))
    (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .skew) (aG b')
  Ms₂ : ∀ s, FormBound reservedCut
    (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
    (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .sym) (dG b' + etaG b')

variable {pr h hne root W I hr b} in
/-- **B8's `NormBounds` from the seven remaining families**, with `Cs`, `Ca`
(`lem:record:accepting-c2`, `const_sym_paper`, `const_skew_paper`) and `Ma₂` (`lem:merge-repair`,
`merge2_skew_paper`) proved, for `r = b^{-1/2}` and `7 ≤ b ≤ p` at every prime `p` of the block. -/
theorem NormBoundsRest.toNormBounds {C : FoldComponents pr hne} {t b' sF aF ℓ sE aE : ℝ}
    (R : NormBoundsRest pr h hne root W I hr b C t b' sF aF ℓ sE aE) (hb7 : 7 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (hrb : r = 1 / Real.sqrt b') :
    NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE where
  Fs := R.Fs
  Fa := R.Fa
  Es := R.Es
  Ea := R.Ea
  Ms := R.Ms
  Ma := R.Ma
  Ms₂ := R.Ms₂
  Ma₂ := merge2_skew_paper pr h hne root W I hr b C t hb7 hbp
  Cs := const_sym_paper pr h hne root W I hr b C t hb7 hbp hrb
  Ca := const_skew_paper pr h hne root W I hr b C t hb7 hbp hrb

end Frame

/-! ## The block specification -/

section Spec

open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.MainFinal2 (tPaper)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The seven remaining norm families of a block specification** (`True` on an upper block),
at the piece constants `κ` and the least prime `bl`: K2's `SpecNormBounds` without `Cs`, `Ca`. -/
def SpecNormBoundsRest (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk} (κ : MiddleConsts)
    (bl : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => NormBoundsRest (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (uniformRoot _ M.hne) M.W M.I M.hr (In.bmin b) (paperComponents E.down.toDC) tPaper bl
      κ.sF κ.aF κ.ℓ κ.sE κ.aE
  | .middleIndividual M, E => NormBoundsRest (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (individualBlockRoot _ M.u M.hne.L2) M.W M.I M.hr (In.bmin b) (paperComponents E.down.toDC)
      tPaper bl κ.sF κ.aF κ.ℓ κ.sE κ.aE
  | .middleCoherent M, E => NormBoundsRest (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (coherentBlockRoot _ M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ κ.sE κ.aE

/-- The least prime of a block is at least `7` and below every prime of the block. -/
theorem blockLeast_facts (b : Blk) :
    (7 : ℝ) ≤ (blockLeast b : ℝ) ∧ ∀ j, (blockLeast b : ℝ) ≤ (blockPrimes bOf b j : ℝ) := by
  obtain ⟨j, hj⟩ := blockLeast_mem b
  have h7 := (classThree_blockPrimes (blockOf := bOf) b).ge7 j
  rw [hj] at h7
  exact ⟨by exact_mod_cast h7, fun j => by exact_mod_cast blockLeast_le b j⟩

/-- `r = b^{-1/2}` from `r² b = 1`, `r ≥ 0`. -/
theorem r_eq_of_scale {r B : ℝ} (hr : 0 ≤ r) (hB : 0 < B) (h : r ^ 2 * B = 1) :
    r = 1 / Real.sqrt B := by
  have h2 : r ^ 2 = 1 / B := by field_simp; linarith
  rw [← Real.sqrt_sq hr, h2, one_div, Real.sqrt_inv, one_div]

/-- **K2's `SpecNormBounds` from the seven remaining families** on a block with the scale
`r² b_𝔅 = 1` and `bmin = b_𝔅`. -/
theorem specNormBounds_of_rest (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) (hbl : In.bmin b = blockLeast b) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → specScale In S →
      SpecNormBoundsRest hW In κ (blockLeast b) S E → SpecNormBounds hW In κ (blockLeast b) S E
  | .upper _, _, _, _ => trivial
  | .middleUniform M, _, hsc, R => by
      obtain ⟨h7, hbp⟩ := blockLeast_facts b
      have hsc' : M.r ^ 2 * (blockLeast b : ℝ) = 1 := by rw [← hbl]; exact hsc
      exact R.toNormBounds h7 hbp (r_eq_of_scale M.hr (by linarith) hsc')
  | .middleIndividual M, _, hsc, R => by
      obtain ⟨h7, hbp⟩ := blockLeast_facts b
      have hsc' : M.r ^ 2 * (blockLeast b : ℝ) = 1 := by rw [← hbl]; exact hsc
      exact R.toNormBounds h7 hbp (r_eq_of_scale M.hr (by linarith) hsc')
  | .middleCoherent M, _, hsc, R => by
      obtain ⟨h7, hbp⟩ := blockLeast_facts b
      have hsc' : M.r ^ 2 * (blockLeast b : ℝ) = 1 := by rw [← hbl]; exact hsc
      exact R.toNormBounds h7 hbp (r_eq_of_scale M.hr (by linarith) hsc')

/-- **The field `hN` from the seven remaining families** at the paper's partition and block
specification, for any per-block signed estimates `blk` and any piece constants `κ` (in
particular `paperKappa`, as in `MainCombined.MainFinalObligationsG.hN`). The constant families
`Cs`, `Ca` (`lem:record:accepting-c2`) are proved. -/
theorem hN_of_rest (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts)
    (R : ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBounds hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) :=
  fun b i hs => specNormBounds_of_rest hW (paperIn f1Cell) (κ i) rfl (specF hW A b) (blk b)
    (paperSpec_scale hW A b) (R b i hs)

end Spec

end Sarkozy.NormBoundsPaper
