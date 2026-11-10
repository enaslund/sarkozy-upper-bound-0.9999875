module

public import Sarkozy.NormBoundsPaper3.MatchSkew
public import Sarkozy.HsumProof.PaperKappa

@[expose] public section

/-!
# NB2's `NormBoundsRest2` from the three families still open (NB3)

NB2's `NormBoundsRest2` (four fields) with the skew field `Ea` of the matching records proved
(`lem:record:exact-marginal-e`(ii), `MatchSkew.match_skew_paper`, at `a_E · b^{-1/2}` for any `a_E`
above `fX X`, `X` the piece start):

* **`NormBoundsRest3`**: the three remaining fields, verbatim from `NormBoundsRest2`:
  `Fs`, `Fa` (`prop:signed-bounds`(a),(b),(e)), `Es` (`lem:record:exact-marginal-e`(ii), symmetric
  part). *Hypotheses.*
* **`NormBoundsRest3.toRest2`**: `NormBoundsRest2` from them, for a piece start `16 ≤ X ≤ b`,
  `2^8 ≤ b` below every prime of the block and `fX X ≤ a_E`.
* **`kAE_ge`**, **`fX_le_paperKappa`**: the paper's table constant `a_E(X_i)` (`paperKappa i`) is at
  least `fX X_i` at each of the 33 piece starts (a rational check by `decide +kernel`).
* **`SpecNormBoundsRest3`**, **`specRest2_of_rest3`**: the same at the level of NB2's
  `SpecNormBoundsRest2` (any root), with `X_i ≤ b_𝔅` (`siteStart_le_blockLeast`) and
  `2^24 ≤ b_𝔅` (`blockLeast_facts24`).
* **`hNr2_of_rest3`**: the field `hNr2` of `MainCombined2.FrontK` (and of NB2's
  `MainFinalObligationsNB2`) at `paperKappa` from the three remaining families.
-/

namespace Sarkozy.NormBoundsPaper3

open Finset
open scoped BigOperators

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords
open Sarkozy.NormBoundsPaper2 (NormBoundsRest2 SpecNormBoundsRest2 blockLeast_facts24)

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **The three families of `NormBounds` not proved by HN, NB2 or NB3** (all hypotheses):
* `Fs`, `Fa`: the folds, `prop:signed-bounds`(a),(b),(e): `s_F r²` and `ℓ r + a_F r²`;
* `Es`: the matchings, symmetric part, `lem:record:exact-marginal-e`(ii): `s_E r`.
The skew field `Ea` of the matchings is proved (`match_skew_paper`). -/
structure NormBoundsRest3 (C : FoldComponents pr hne) (t b' sF aF ℓ sE : ℝ) : Prop where
  Fs : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .sym) (sF * (1 / Real.sqrt b') ^ 2)
  Fa : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .skew)
    (ℓ * (1 / Real.sqrt b') + aF * (1 / Real.sqrt b') ^ 2)
  Es : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl i)))
    (foldChange pr h hne root W I hr b C t (.inr (.inl i)) .sym) (sE * (1 / Real.sqrt b'))

variable {pr h hne root W I hr b} in
/-- **NB2's `NormBoundsRest2` from the three remaining families**, with `Ea`
(`lem:record:exact-marginal-e`(ii)) proved, for a piece start `16 ≤ X ≤ b'`, `2^8 ≤ b' ≤ p` at
every prime `p` of the block and `fX X ≤ a_E`. -/
theorem NormBoundsRest3.toRest2 {C : FoldComponents pr hne} {t b' sF aF ℓ sE aE X : ℝ}
    (R : NormBoundsRest3 pr h hne root W I hr b C t b' sF aF ℓ sE) (hX : 16 ≤ X) (hXb : X ≤ b')
    (hb : (2 : ℝ) ^ 8 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) (haE : fX X ≤ aE) :
    NormBoundsRest2 pr h hne root W I hr b C t b' sF aF ℓ sE aE where
  Fs := R.Fs
  Fa := R.Fa
  Es := R.Es
  Ea := match_skew_paper pr h hne root W I hr b C t hX hXb hb hbp haE

end Frame

/-! ## The paper's constants -/

open Sarkozy.HsumProof (paperKappa kAE)

/-- **The table constant `a_E(X_i)` is at least `X(X + 2)/(X² − 3X + 4)` at every piece start**
(exact rational check). -/
theorem kAE_ge : ∀ i : Fin 33, (pieceStart i : ℚ) * ((pieceStart i : ℚ) + 2) ≤
    kAE i * ((pieceStart i : ℚ) ^ 2 - 3 * (pieceStart i : ℚ) + 4) := by
  decide +kernel

theorem fX_le_paperKappa (i : Fin 33) : fX (pieceStart i) ≤ (paperKappa i).aE := by
  unfold fX
  rw [div_le_iff₀ (fX_den_pos _)]
  have h := kAE_ge i
  have h' : (((pieceStart i : ℚ) * ((pieceStart i : ℚ) + 2) : ℚ) : ℝ) ≤
      ((kAE i * ((pieceStart i : ℚ) ^ 2 - 3 * (pieceStart i : ℚ) + 4) : ℚ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  change (pieceStart i : ℝ) * ((pieceStart i : ℝ) + 2) ≤
    ((kAE i : ℚ) : ℝ) * ((pieceStart i : ℝ) ^ 2 - 3 * (pieceStart i : ℝ) + 4)
  exact h'

/-! ## The block specification -/

section Spec

open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.MainFinal2 (tPaper)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The three remaining norm families of a block specification** (`True` on an upper block), at
the piece constants `κ` and the least prime `bl`: NB2's `SpecNormBoundsRest2` without `Ea`. -/
def SpecNormBoundsRest3 (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) (bl : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => NormBoundsRest3 (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (uniformRoot _ M.hne) M.W M.I M.hr (In.bmin b) (paperComponents E.down.toDC) tPaper bl
      κ.sF κ.aF κ.ℓ κ.sE
  | .middleIndividual M, E => NormBoundsRest3 (blockPrimes bOf b) (classThree_blockPrimes b)
      M.hne (individualBlockRoot _ M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ κ.sE
  | .middleCoherent M, E => NormBoundsRest3 (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (coherentBlockRoot _ M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ κ.sE

/-- **NB2's `SpecNormBoundsRest2` from the three remaining families**, at the least prime of the
block, for a piece start `16 ≤ X ≤ b_𝔅` with `fX X ≤ a_E`. -/
theorem specRest2_of_rest3 (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) {X : ℝ} (hX : 16 ≤ X) (hXb : X ≤ (blockLeast b : ℝ)) (haE : fX X ≤ κ.aE) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) →
      SpecNormBoundsRest3 hW In κ (blockLeast b) S E →
        SpecNormBoundsRest2 hW In κ (blockLeast b) S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, R => by
      obtain ⟨h24, hbp⟩ := blockLeast_facts24 b
      exact R.toRest2 hX hXb (le_trans (by norm_num) h24) hbp haE
  | .middleIndividual _, _, R => by
      obtain ⟨h24, hbp⟩ := blockLeast_facts24 b
      exact R.toRest2 hX hXb (le_trans (by norm_num) h24) hbp haE
  | .middleCoherent _, _, R => by
      obtain ⟨h24, hbp⟩ := blockLeast_facts24 b
      exact R.toRest2 hX hXb (le_trans (by norm_num) h24) hbp haE

/-- **The field `hNr2` of `MainCombined2.FrontK` from the three remaining families** at the
paper's partition and block specification, for any per-block signed estimates `blk`, at
`paperKappa`. The skew field `Ea` (`lem:record:exact-marginal-e`(ii)) is proved. -/
theorem hNr2_of_rest3 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b))
    (R : ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest3 hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
        (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
        (blk b) := by
  intro b i hs
  have hX : (16 : ℝ) ≤ pieceStart i := by
    have := pieceStart_ge_Q3 i
    have h16 : 16 ≤ pieceStart i := le_trans (by norm_num [Q3]) this
    exact_mod_cast h16
  have hXb : (pieceStart i : ℝ) ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact_mod_cast h
  exact specRest2_of_rest3 hW (paperIn f1Cell) (paperKappa i) hX hXb (fX_le_paperKappa i)
    (specF hW A b) (blk b) (R b i hs)

end Spec

end Sarkozy.NormBoundsPaper3
