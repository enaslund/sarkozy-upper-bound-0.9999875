module

public import Sarkozy.NormBoundsPaper3.MatchSym
public import Sarkozy.NormBoundsPaper3.Constructor

@[expose] public section

/-!
# `hNr2` from the folds and the one-prime matching input (NB3)

NB2's `NormBoundsRest2` (four fields) with both matching fields reduced:

* `Ea` proved (`match_skew_paper`, `lem:record:exact-marginal-e`(ii), skew);
* `Es` proved from the **one-prime** statement `EOrthPrime p (s_E(X) p^{-1/2})`
  (`lem:record:e-orthogonal`(c) with the monotonicity of `lem:record:exact-marginal-e`(i)),
  `match_sym_paper`: the block structure, the old and new couplings, their marginals and centred
  norms, and the sectors of two or more primes are proved.

* **`EsPrimeInput κ`**: at every prime `p ≡ 3 (mod 4)` with `p ≥ X_i`,
  `‖Sym(K₁ − K^E_0)‖ ≤ s_E(X_i) p^{-1/2}` on `L²(ν_E)`. *Hypothesis* (the paper's
  `lem:record:e-orthogonal`(c), `s^E_p ≤ s_E(X) r_p`).
* **`NormBoundsRest4`** (`Fs`, `Fa`, verbatim) and `NormBoundsRest4.toRest2`;
* `kSE_ge`: `2 ≤ s_E(X_i)² X_i` at the 33 piece starts (`decide +kernel`; the paper's value is
  about `(1 + √2)² ≈ 5.83`);
* **`SpecNormBoundsRest4`**, `specRest2_of_rest4`, **`hNr2_of_rest4`**: the field `hNr2` of
  `MainCombined2.FrontK` at `paperKappa` from the folds (`Fs`, `Fa`) and `EsPrimeInput paperKappa`.
-/

namespace Sarkozy.NormBoundsPaper3

open Finset
open scoped BigOperators

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords
open Sarkozy.NormBoundsPaper2 (NormBoundsRest2 SpecNormBoundsRest2 blockLeast_facts24)
open Sarkozy.MainFinal (MiddleConsts)

/-- **The one-prime input of `Es`** (`lem:record:e-orthogonal`(c), with the monotonicity of
`lem:record:exact-marginal-e`(i), `s^E_p ≤ s_E(X) r_p`): at every prime `p ≡ 3 (mod 4)` of the
piece `i` (`p ≥ X_i`), the symmetric part of `K₁ − K^E_0` has norm at most `s_E(X_i) p^{-1/2}` on
mean-zero functions of `L²(ν_E)`. *Hypothesis.* -/
def EsPrimeInput (κ : Fin 33 → MiddleConsts) : Prop :=
  ∀ (i : Fin 33) (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p →
    EOrthPrime p ((κ i).sE * (1 / Real.sqrt p))

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **The two fold families of `NormBounds`** (hypotheses): `Fs`, `Fa`,
`prop:signed-bounds`(a),(b),(e): `s_F r²` and `ℓ r + a_F r²`. -/
structure NormBoundsRest4 (C : FoldComponents pr hne) (t b' sF aF ℓ : ℝ) : Prop where
  Fs : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .sym) (sF * (1 / Real.sqrt b') ^ 2)
  Fa : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
    (foldChange pr h hne root W I hr b C t (.inl i) .skew)
    (ℓ * (1 / Real.sqrt b') + aF * (1 / Real.sqrt b') ^ 2)

variable {pr h hne root W I hr b} in
/-- **NB2's `NormBoundsRest2` from the folds and the one-prime matching input**: `Ea` proved,
`Es` from `EOrthPrime` at the primes of the block. -/
theorem NormBoundsRest4.toRest2 {C : FoldComponents pr hne} {t b' sF aF ℓ sE aE X : ℝ}
    (R : NormBoundsRest4 pr h hne root W I hr b C t b' sF aF ℓ) (hX : 10 ^ 6 ≤ X) (hXb : X ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (hsE0 : 0 ≤ sE) (hsE : 2 ≤ sE ^ 2 * X)
    (hin : ∀ i, EOrthPrime (pr i) (sE * (1 / Real.sqrt (pr i)))) (haE : fX X ≤ aE) :
    NormBoundsRest2 pr h hne root W I hr b C t b' sF aF ℓ sE aE where
  Fs := R.Fs
  Fa := R.Fa
  Es := match_sym_paper pr h hne root W I hr b C t hX hXb hbp hsE0 hsE hin
  Ea := match_skew_paper pr h hne root W I hr b C t (by linarith) hXb (by linarith) hbp haE

end Frame

/-! ## The paper's constants -/

open Sarkozy.HsumProof (paperKappa kSE)

/-- `2 ≤ s_E(X_i)² X_i` at every piece start (exact rational check). -/
theorem kSE_ge : ∀ i : Fin 33, 2 ≤ kSE i ^ 2 * (pieceStart i : ℚ) := by
  decide +kernel

theorem sE_facts (i : Fin 33) :
    0 ≤ (paperKappa i).sE ∧ 2 ≤ (paperKappa i).sE ^ 2 * (pieceStart i : ℝ) := by
  refine ⟨?_, ?_⟩
  · change (0 : ℝ) ≤ ((kSE i : ℚ) : ℝ)
    have : (0 : ℚ) ≤ kSE i := by unfold kSE; positivity
    exact_mod_cast this
  · change (2 : ℝ) ≤ ((kSE i : ℚ) : ℝ) ^ 2 * (pieceStart i : ℝ)
    have h := kSE_ge i
    have h' : ((2 : ℚ) : ℝ) ≤ ((kSE i ^ 2 * (pieceStart i : ℚ) : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'

/-! ## The block specification -/

section Spec

open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinal2 (tPaper)
open Sarkozy.AnalyticCells (f1Cell)

/-- **The two fold families of a block specification** (`True` on an upper block), at the piece
constants `κ` and the least prime `bl`. -/
def SpecNormBoundsRest4 (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) (bl : ℝ) : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => NormBoundsRest4 (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (uniformRoot _ M.hne) M.W M.I M.hr (In.bmin b) (paperComponents E.down.toDC) tPaper bl
      κ.sF κ.aF κ.ℓ
  | .middleIndividual M, E => NormBoundsRest4 (blockPrimes bOf b) (classThree_blockPrimes b)
      M.hne (individualBlockRoot _ M.u M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ
  | .middleCoherent M, E => NormBoundsRest4 (blockPrimes bOf b) (classThree_blockPrimes b) M.hne
      (coherentBlockRoot _ M.D M.u M.hη M.hne.L2) M.W M.I M.hr (In.bmin b)
      (paperComponents E.down.toDC) tPaper bl κ.sF κ.aF κ.ℓ

/-- **NB2's `SpecNormBoundsRest2` from the folds and the one-prime matching input.** -/
theorem specRest2_of_rest4 (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) {X : ℕ} (hX : 10 ^ 6 ≤ X) (hXb : X ≤ blockLeast b) (hsE0 : 0 ≤ κ.sE)
    (hsE : 2 ≤ κ.sE ^ 2 * (X : ℝ)) (haE : fX X ≤ κ.aE)
    (hin : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → X ≤ p → EOrthPrime p (κ.sE * (1 / Real.sqrt p))) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) →
      SpecNormBoundsRest4 hW In κ (blockLeast b) S E →
        SpecNormBoundsRest2 hW In κ (blockLeast b) S E := by
  have hX' : (10 : ℝ) ^ 6 ≤ X := by exact_mod_cast hX
  have hXb' : (X : ℝ) ≤ blockLeast b := by exact_mod_cast hXb
  obtain ⟨-, hbp⟩ := blockLeast_facts24 b
  have hp : ∀ j, X ≤ blockPrimes bOf b j := fun j => by
    have := hXb'.trans (hbp j)
    exact_mod_cast this
  have hin' : ∀ j, EOrthPrime (blockPrimes bOf b j)
      (κ.sE * (1 / Real.sqrt (blockPrimes bOf b j))) :=
    fun j => hin _ ((classThree_blockPrimes b).mod4 j) (hp j)
  intro S E R
  match S, E, R with
  | .upper _, _, _ => trivial
  | .middleUniform _, _, R => exact R.toRest2 hX' hXb' hbp hsE0 hsE hin' haE
  | .middleIndividual _, _, R => exact R.toRest2 hX' hXb' hbp hsE0 hsE hin' haE
  | .middleCoherent _, _, R => exact R.toRest2 hX' hXb' hbp hsE0 hsE hin' haE

/-- **The field `hNr2` of `MainCombined2.FrontK` from the folds and the one-prime matching
input**, at the paper's partition and `paperKappa`. The matching fields `Ea` (proved) and `Es`
(from `EsPrimeInput`, `lem:record:e-orthogonal`(c)) are discharged. -/
theorem hNr2_of_rest4 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (hEs : EsPrimeInput paperKappa)
    (R : ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
        (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest2 hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
        (blk b) := by
  intro b i hs
  have hX : 10 ^ 6 ≤ pieceStart i := le_trans (by norm_num [Q3]) (pieceStart_ge_Q3 i)
  have hXb : pieceStart i ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact h
  obtain ⟨hsE0, hsE⟩ := sE_facts i
  exact specRest2_of_rest4 hW (paperIn f1Cell) (paperKappa i) hX hXb hsE0 hsE
    (fX_le_paperKappa i) (fun p _ h3 hp => hEs i p h3 hp) (specF hW A b) (blk b) (R b i hs)

end Spec

end Sarkozy.NormBoundsPaper3
