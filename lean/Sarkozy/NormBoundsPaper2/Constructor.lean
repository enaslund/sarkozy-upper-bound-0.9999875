module

public import Sarkozy.NormBoundsPaper2.MirrorBlock
public import Sarkozy.NormBoundsPaper.Constructor

@[expose] public section

/-!
# HN's `NormBoundsRest` from the four families still open (NB2)

HN's `NormBoundsRest` (seven fields) with the three merge fields of `lem:merge-repair` proved:
`Ms₂` (first-coordinate, symmetric, `d_b + η_b`, `Merge2Sym.merge2_sym_paper`, every `b ≥ 7`),
`Ms`, `Ma` (mirror-edge, `s_b`, `a_b`, `MirrorBlock.mirror_sym_paper`, `mirror_skew_paper`, for
`b ≥ 2^24` as in the paper):

* **`NormBoundsRest2`**: the four remaining fields, verbatim from `NormBoundsRest`:
  `Fs`, `Fa` (`prop:signed-bounds`(a),(b),(e)), `Es`, `Ea` (`lem:record:exact-marginal-e`(ii)).
  *Hypotheses.*
* **`NormBoundsRest2.toRest`**: `NormBoundsRest` from them, for `2^24 ≤ b` below every prime of
  the block.
* **`SpecNormBoundsRest2`**, **`specRest_of_rest2`**: the same at the level of HN's
  `SpecNormBoundsRest` (any root), with `2^24 ≤ b_𝔅` from the paper's partition
  (`two_pow_24_le_blockLeast`).
* **`hNr_of_rest2`**: the field `hNr` of `Sarkozy.MainCombined.MainFinalObligationsGPN` (the
  obligations of `main_goal_f1i`) from the four remaining families at the same piece constants `κ`
  (in particular `paperKappa`). The proved fields do not depend on `κ`.
-/

namespace Sarkozy.NormBoundsPaper2

open Finset
open scoped BigOperators

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords
open Sarkozy.NormBoundsPaper (NormBoundsRest SpecNormBoundsRest blockLeast_facts)

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **The four families of `NormBounds` not proved by HN or NB2** (all hypotheses):
* `Fs`, `Fa`: the folds, `prop:signed-bounds`(a),(b),(e): `s_F r²` and `ℓ r + a_F r²`;
* `Es`, `Ea`: the matchings, `lem:record:exact-marginal-e`(ii): `s_E r` and `a_E r`.
The merge fields `Ms`, `Ma`, `Ms₂` (`lem:merge-repair`) are proved (`mirror_sym_paper`,
`mirror_skew_paper`, `merge2_sym_paper`); `Cs`, `Ca`, `Ma₂` are HN's. -/
structure NormBoundsRest2 (C : FoldComponents pr hne) (t b' sF aF ℓ sE aE : ℝ) : Prop where
  Fs : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .sym) (sF * (1 / Real.sqrt b') ^ 2)
  Fa : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .skew)
    (ℓ * (1 / Real.sqrt b') + aF * (1 / Real.sqrt b') ^ 2)
  Es : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl i)))
    (foldChange pr h hne root W I hr b C t (.inr (.inl i)) .sym) (sE * (1 / Real.sqrt b'))
  Ea : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl i)))
    (foldChange pr h hne root W I hr b C t (.inr (.inl i)) .skew) (aE * (1 / Real.sqrt b'))

variable {pr h hne root W I hr b} in
/-- **HN's `NormBoundsRest` from the four remaining families**, with `Ms`, `Ma`, `Ms₂`
(`lem:merge-repair`) proved, for `2^24 ≤ b ≤ p` at every prime `p` of the block. -/
theorem NormBoundsRest2.toRest {C : FoldComponents pr hne} {t b' sF aF ℓ sE aE : ℝ}
    (R : NormBoundsRest2 pr h hne root W I hr b C t b' sF aF ℓ sE aE) (hb : (2 : ℝ) ^ 24 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) :
    NormBoundsRest pr h hne root W I hr b C t b' sF aF ℓ sE aE where
  Fs := R.Fs
  Fa := R.Fa
  Es := R.Es
  Ea := R.Ea
  Ms := mirror_sym_paper pr h hne root W I hr b C t hb hbp
  Ma := mirror_skew_paper pr h hne root W I hr b C t hb hbp
  Ms₂ := merge2_sym_paper pr h hne root W I hr b C t (le_trans (by norm_num) hb) hbp

end Frame

/-! ## The block specification -/

section Spec

open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.MainFinal2 (tPaper)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The four remaining norm families of a block specification** (`True` on an upper block), at
the piece constants `κ` and the least prime `bl`: HN's `SpecNormBoundsRest` without the merge
fields `Ms`, `Ma`, `Ms₂`. -/
def SpecNormBoundsRest2 (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) (bl : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => NormBoundsRest2 (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (uniformRoot _ M.hne) M.W M.I M.hr (In.bmin b) (paperComponents E.down.toDC) tPaper bl
      κ.sF κ.aF κ.ℓ κ.sE κ.aE
  | .middleIndividual M, E => NormBoundsRest2 (blockPrimes bOf b) (classThree_blockPrimes b)
      M.hne (individualBlockRoot _ M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ κ.sE κ.aE
  | .middleCoherent M, E => NormBoundsRest2 (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (coherentBlockRoot _ M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ κ.sE κ.aE

/-- `2^24 ≤ b_𝔅` and `b_𝔅` is below every prime of the block. -/
theorem blockLeast_facts24 (b : Blk) :
    (2 : ℝ) ^ 24 ≤ (blockLeast b : ℝ) ∧ ∀ j, (blockLeast b : ℝ) ≤ (blockPrimes bOf b j : ℝ) := by
  refine ⟨?_, (blockLeast_facts b).2⟩
  have := two_pow_24_le_blockLeast b
  exact_mod_cast this

/-- **HN's `SpecNormBoundsRest` from the four remaining families**, at the least prime of the
block. -/
theorem specRest_of_rest2 (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) →
      SpecNormBoundsRest2 hW In κ (blockLeast b) S E →
        SpecNormBoundsRest hW In κ (blockLeast b) S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, R => by
      obtain ⟨h24, hbp⟩ := blockLeast_facts24 b
      exact R.toRest h24 hbp
  | .middleIndividual _, _, R => by
      obtain ⟨h24, hbp⟩ := blockLeast_facts24 b
      exact R.toRest h24 hbp
  | .middleCoherent _, _, R => by
      obtain ⟨h24, hbp⟩ := blockLeast_facts24 b
      exact R.toRest h24 hbp

/-- **The field `hNr` of `main_goal_f1i` from the four remaining families** at the paper's
partition and block specification, for any per-block signed estimates `blk` and any piece
constants `κ` (in particular `paperKappa`). The merge families `Ms`, `Ma`, `Ms₂`
(`lem:merge-repair`) are proved. -/
theorem hNr_of_rest2 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts)
    (R : ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest2 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) :=
  fun b i hs => specRest_of_rest2 hW (paperIn f1Cell) (κ i) (specF hW A b) (blk b) (R b i hs)

end Spec

end Sarkozy.NormBoundsPaper2
