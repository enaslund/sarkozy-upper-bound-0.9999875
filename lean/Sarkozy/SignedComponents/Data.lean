module

public import Sarkozy.SignedComponents.Fold
public import Sarkozy.MiddleComparison.Prices
public import Sarkozy.MiddleComparison.PaperData

@[expose] public section

/-!
# B7's `ReplacementData` of a middle block, constructed from the fold components

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`, `def:record:mixture`,
`lem:middle-comparison-prices`; `paper/sections/09_comparison_theorem.tex`, `rem:cp:charging`(ii).

B7's `ReplacementData pr h D` (8 fields) is what remained open of the comparison law of a middle
block. On the paper's frame `D = middleFrame pr hne root W I hr b h` (any root) this file builds
it from the per-prime fold components alone:

* `t`: any `t ∈ [0, 1]` (the paper's `t = 127/500`);
* `P`, `accept`, `unif`: `foldRec C`, the block components `⊗_p P_{c,p}` placed by `F₁`, `F₂`
  (`Sarkozy.SignedComponents.Fold`), from `C : FoldComponents pr hne`;
* `N`, `N_nonneg`, `norm`: **the optimal norms** of the twelve changes (`optNorm`). They are
  finite because every replacement and every replaced record charges only halves in the support
  of the record's actual half marginal (`change_bounded`, from `Sarkozy.SignedComponents.Support`
  and `foldRec_halves`).

**`ofFold`** is the constructor. Its norms are the true operator norms, so the paper's norm bounds
are statements about concrete changes: **`ofFold_N_le`** turns a bound `FormBound … K` with the
paper's constant `K` into `N ≤ K`, and **`ofFold_price_sum_le`** gives B7's `price_sum_le` (the
per-block price `M_𝔅` of B2's `SAExplicit_of_bands`) from the twelve norm bounds of
`prop:signed-bounds`(a),(b),(e), `lem:record:exact-marginal-e`(ii), the table of
`lem:merge-repair` and `lem:record:accepting-c2`, stated as `FormBound` of the changes of the
constructed replacements.

For B7's paper-level inputs: `FoldSpec` (B2's `UpperAtomInputs` on an upper block, `FoldComponents`
on a middle block), `FoldSpec.toSpecData` (B7's `SpecData`) and **`comparisonInputsOfFold`** (B2's
`ComparisonInputs`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords

/-- The actual half marginal at `ι` of the changed record `t`. -/
noncomputable abbrev mOf {X : Type} [Fintype X] [DecidableEq X] (D : FrameData X) (t : Chg) :
    (reservedCut.Half → X) → ℝ :=
  plusMarginal reservedCut (midComponent D.F (true, chgPat t)).weight

theorem mOf_nonneg {X : Type} [Fintype X] [DecidableEq X] (D : FrameData X) (t : Chg)
    (x : reservedCut.Half → X) : 0 ≤ mOf D t x :=
  plusMarginal_nonneg reservedCut (fun z => (midComponent D.F (true, chgPat t)).nonneg z) x

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **The replaced records charge only halves in their own support** (the `F` and `E` laws are
invariant under the layer swap). -/
theorem record_bounded (t : Chg) :
    FormBounded reservedCut (mOf (middleFrame pr hne root W I hr b h) t)
      (recM (middleFrame pr hne root W I hr b h).F (true, chgPat t)) := by
  refine formBounded_signedIntegral (mOf_nonneg _ t) fun z hz => ?_
  rcases t with j | s | φ | k
  · exact record_halves (lawF pr hne) _ (lawF_swap pr hne) z hz
  · exact record_halves (lawE pr hne) _ (lawE_swap pr hne) z hz
  · exact record_halves (lawE pr hne) _ (lawE_swap pr hne) z hz
  · exact record_halves (lawE pr hne) _ (lawE_swap pr hne) z hz

/-- **The replacements charge only halves in the support of the replaced record.** -/
theorem new_bounded (C : FoldComponents pr hne) (t : ℝ) (t' : Chg) :
    FormBounded reservedCut (mOf (middleFrame pr hne root W I hr b h) t')
      (newOf pr h t (foldRec C) t') := by
  have hm := mOf_nonneg (middleFrame pr hne root W I hr b h) t'
  rcases t' with j | s | φ | k
  · change FormBounded _ _ (∑ c, signedCoef t c • signedIntegral (foldRec C j c).weight)
    exact FormBounded.sum _ _ fun c _ =>
      (formBounded_signedIntegral hm fun z hz => foldRec_halves C j c z hz).smul _
  · exact formBounded_signedIntegral hm fun z hz => matchRec_halves pr h hne s z hz
  · exact formBounded_signedIntegral hm fun z hz => mergeRec_halves pr h hne φ z hz
  · exact formBounded_signedIntegral hm fun z hz => constRec_halves pr h hne k z hz

/-- **Every change has a finite norm** relative to the actual half marginal of its record. -/
theorem change_bounded (C : FoldComponents pr hne) (t : ℝ) (t' : Chg) (e : ChangeType) :
    FormBounded reservedCut (mOf (middleFrame pr hne root W I hr b h) t')
      (changePart e (newOf pr h t (foldRec C) t' -
        recM (middleFrame pr hne root W I hr b h).F (true, chgPat t'))) := by
  obtain ⟨K, hK⟩ := (new_bounded pr h hne root W I hr b C t t').sub
    (record_bounded pr h hne root W I hr b t')
  cases e
  · exact ⟨K, hK.symPart⟩
  · exact ⟨K, hK.skewPart⟩

/-- **B7's `ReplacementData` of a middle block**, from the fold components `C` and `t ∈ [0, 1]`:
the fold records `foldRec C`, and the optimal norms of the twelve changes. -/
noncomputable def ofFold (C : FoldComponents pr hne) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ReplacementData pr h (middleFrame pr hne root W I hr b h) where
  t := t
  t_nonneg := ht0
  t_le_one := ht1
  P := foldRec C
  accept j c z hz e := foldRec_accepts C j c z hz e
  unif j c := foldRec_uniform C j c
  N t' e := optNorm reservedCut (mOf (middleFrame pr hne root W I hr b h) t')
    (changePart e (newOf pr h t (foldRec C) t' -
      recM (middleFrame pr hne root W I hr b h).F (true, chgPat t')))
  N_nonneg _ _ := optNorm_nonneg _ _
  norm t' e F G := (optNorm_spec (change_bounded pr h hne root W I hr b C t t' e)).2 F G

/-- The replacement of the fold `F_{j+1}` in `ofFold`: the signed record
`⊗P_{++} + (t/2)⊗P_{-+} - (t/2)⊗P_{--}` of `def:record:mixture`(c),(d). -/
theorem ofFold_newMeas_fold (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (j : Fin 2) :
    (ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.newMeas (.inl j) =
      ∑ c, signedCoef t c • signedIntegral (foldRec C j c).weight :=
  ReplacementData.toReplacements_newMeas _ _

/-- The replacement of the matching `E_s` in `ofFold`: `⊗_p K₁` placed by `E_s`. -/
theorem ofFold_newMeas_match (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (s : Fin 2) :
    (ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.newMeas (.inr (.inl s)) =
      signedIntegral (matchRec pr h s).weight :=
  ReplacementData.toReplacements_newMeas_match _ _

/-- The change `ν'_t - Π_t` of the record `t` (part `e`) in `ofFold`. -/
noncomputable abbrev foldChange (C : FoldComponents pr hne) (t : ℝ) (t' : Chg) (e : ChangeType) :
    SlotMeasure (BlockLabel pr) :=
  changePart e (newOf pr h t (foldRec C) t' -
    recM (middleFrame pr hne root W I hr b h).F (true, chgPat t'))

/-- **The norms of `ofFold` are below the paper's bounds**: a bound `K` of the change gives
`N ≤ K`. -/
theorem ofFold_N_le (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {t' : Chg}
    {e : ChangeType} {K : ℝ}
    (hK : FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) t')
      (foldChange pr h hne root W I hr b C t t' e) K) :
    (ofFold pr h hne root W I hr b C t ht0 ht1).N t' e ≤ K :=
  optNorm_le hK

/-- **`lem:middle-comparison-prices` for the constructed atom, from the paper's norm bounds.**
For a piece starting at `X ≥ 4` and a block of it with least prime `b' ≥ X`, `r = b'^{-1/2}`,
`sel ≥ 0`, `f₁ + h₁ ≥ 0`: if the twelve changes of the constructed replacements satisfy the
paper's norm bounds, stated as `FormBound` relative to the actual half marginals
(folds: `prop:signed-bounds`(a),(b),(e); matchings: `lem:record:exact-marginal-e`(ii); merges:
the table of `lem:merge-repair`; constants: `lem:record:accepting-c2`; these twelve families are
hypotheses), then the block price `s_𝔅 + a_𝔅` is at most B7's `price_sum_le` bound. -/
theorem ofFold_price_sum_le (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : FrameFacts (middleFrame pr hne root W I hr b h) (blockSquareAccepted pr)
      MainAnchor.paperQueries)
    {Xn : ℕ} {b' sel : ℝ} (hX : 4 ≤ Xn) (hb : (Xn : ℝ) ≤ b') (hrb : r = 1 / Real.sqrt b')
    (hsel : 0 ≤ sel) (hfh : 0 ≤ I.f₁ + I.h₁) {sF aF ℓ sE aE : ℝ}
    (hFs : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
      (foldChange pr h hne root W I hr b C t (.inl i) .sym) (sF * (1 / Real.sqrt b') ^ 2))
    (hFa : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inl i))
      (foldChange pr h hne root W I hr b C t (.inl i) .skew)
      (ℓ * (1 / Real.sqrt b') + aF * (1 / Real.sqrt b') ^ 2))
    (hEs : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl i)))
      (foldChange pr h hne root W I hr b C t (.inr (.inl i)) .sym) (sE * (1 / Real.sqrt b')))
    (hEa : ∀ i, FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl i)))
      (foldChange pr h hne root W I hr b C t (.inr (.inl i)) .skew) (aE * (1 / Real.sqrt b')))
    (hMs : ∀ s k, k ≠ 2 → FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, k)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .sym) (sG b'))
    (hMa : ∀ s k, k ≠ 2 → FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, k)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .skew) (aG b'))
    (hMs₂ : ∀ s, FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .sym)
      (dG b' + etaG b'))
    (hMa₂ : ∀ s, FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .skew) (gammaG b'))
    (hCs : ∀ k, FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .sym)
      (r ^ 2 / (1 - 1 / b') ^ 2))
    (hCa : ∀ k, FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .skew) (r / (1 - 1 / b'))) :
    ((ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.toAtom hF).sprice sel +
        ((ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.toAtom hF).aprice sel ≤
      ((coefS2 W sE * (1 / Real.sqrt b') ^ 2 + coefS3 W I sF * (1 / Real.sqrt b') ^ 3 +
          coefS4 W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b') ^ 4 +
          coefS5 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 5) +
        (coefA2 W ℓ aE * (1 / Real.sqrt b') ^ 2 +
          coefA3 W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b') ^ 3 +
          coefA4 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 4)) * sel := by
  set R := ofFold pr h hne root W I hr b C t ht0 ht1
  have hN : ∀ {t' : Chg} {e : ChangeType} {K : ℝ},
      FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) t')
        (foldChange pr h hne root W I hr b C t t' e) K → R.toReplacements.N t' e ≤ K :=
    fun hK => ofFold_N_le pr h hne root W I hr b C ht0 ht1 hK
  have hM : MergeRepairBounds b' (fun j => R.toReplacements.N (.inr (.inr (.inl j))) .sym)
      (fun j => R.toReplacements.N (.inr (.inr (.inl j))) .skew) :=
    { sym_nonneg := fun _ => R.N_nonneg _ _
      skew_nonneg := fun _ => R.N_nonneg _ _
      sym_mirror := fun s k hk => hN (hMs s k hk)
      skew_mirror := fun s k hk => hN (hMa s k hk)
      sym_first := fun s => hN (hMs₂ s)
      skew_first := fun s => hN (hMa₂ s) }
  exact R.toReplacements.price_sum_le hF hX hb hrb hsel hfh (fun i => hN (hFs i))
    (fun i => hN (hFa i)) (fun i => hN (hEs i)) (fun i => hN (hEa i)) hM
    (fun k => hN (hCs k)) (fun k => hN (hCa k))

/-- **The paper's twelve norm bounds of a middle block**, as `FormBound`s of the changes of the
constructed replacements relative to the actual half marginals (all hypotheses):
* `Fs`, `Fa`: the folds, `prop:signed-bounds`(a),(b),(e): `s_F r²` and `ℓ r + a_F r²`;
* `Es`, `Ea`: the matchings, `lem:record:exact-marginal-e`(ii): `s_E r` and `a_E r`;
* `Ms`, `Ma`, `Ms₂`, `Ma₂`: the merges, the table of `lem:merge-repair`;
* `Cs`, `Ca`: the constants, `lem:record:accepting-c2`: `r²/(1 - 1/b)²` and `r/(1 - 1/b)`;
with `r = b^{-1/2}`, `b` the least prime of the block. -/
structure NormBounds (C : FoldComponents pr hne) (t b' sF aF ℓ sE aE : ℝ) : Prop where
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
  Ma₂ : ∀ s, FormBound reservedCut
    (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
    (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .skew) (gammaG b')
  Cs : ∀ k, FormBound reservedCut
    (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
    (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .sym)
    (r ^ 2 / (1 - 1 / b') ^ 2)
  Ca : ∀ k, FormBound reservedCut
    (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
    (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .skew) (r / (1 - 1 / b'))

/-- **`lem:middle-comparison-prices` from `NormBounds`** (the bundled form of
`ofFold_price_sum_le`). -/
theorem ofFold_price_sum_le_of (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : FrameFacts (middleFrame pr hne root W I hr b h) (blockSquareAccepted pr)
      MainAnchor.paperQueries)
    {Xn : ℕ} {b' sel : ℝ} (hX : 4 ≤ Xn) (hb : (Xn : ℝ) ≤ b') (hrb : r = 1 / Real.sqrt b')
    (hsel : 0 ≤ sel) (hfh : 0 ≤ I.f₁ + I.h₁) {sF aF ℓ sE aE : ℝ}
    (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE) :
    ((ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.toAtom hF).sprice sel +
        ((ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.toAtom hF).aprice sel ≤
      ((coefS2 W sE * (1 / Real.sqrt b') ^ 2 + coefS3 W I sF * (1 / Real.sqrt b') ^ 3 +
          coefS4 W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b') ^ 4 +
          coefS5 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 5) +
        (coefA2 W ℓ aE * (1 / Real.sqrt b') ^ 2 +
          coefA3 W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b') ^ 3 +
          coefA4 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 4)) * sel :=
  ofFold_price_sum_le pr h hne root W I hr b C ht0 ht1 hF hX hb hrb hsel hfh NB.Fs NB.Fa NB.Es
    NB.Ea NB.Ms NB.Ma NB.Ms₂ NB.Ma₂ NB.Cs NB.Ca

end Frame

/-! ## B7's paper-level inputs -/

section Paper

open Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.FirstStagePaper Sarkozy.PartVLaws
open Sarkozy.TargetLedger (targetDecay)
open Sarkozy.CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **The (CP4) inputs of a class-three block with the fold components as the only middle-block
input**: B2's `UpperAtomInputs` on an upper block; the per-prime fold components
(`lem:signed-components`(a),(d)) on a middle block. -/
def FoldSpec (hW : Target.Weil) {b : B} : PaperBlockSpec blockOf b → Type 1
  | .upper U => ULift (UpperAtomInputs (blockPrimes blockOf b) (upperNe hW U) U.W U.r)
  | .middleUniform M => ULift (FoldComponents (blockPrimes blockOf b) M.hne)
  | .middleIndividual M => ULift (FoldComponents (blockPrimes blockOf b) M.hne)
  | .middleCoherent M => ULift (FoldComponents (blockPrimes blockOf b) M.hne)

/-- **B7's `SpecData` from the fold components** (`ofFold` on every middle block, with one
`t ∈ [0, 1]`). -/
noncomputable def FoldSpec.toSpecData (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (S : PaperBlockSpec blockOf b) → FoldSpec hW S → SpecData hW In S
  | .upper _, U => U
  | .middleUniform M, C => ⟨ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      C.down t ht0 ht1⟩
  | .middleIndividual M, C => ⟨ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr
      (In.bmin b) C.down t ht0 ht1⟩
  | .middleCoherent M, C => ⟨ofFold _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr
      (In.bmin b) C.down t ht0 ht1⟩

variable (blockOf) in
/-- **B2's `ComparisonInputs` with every middle atom built from the fold components**: B7's
`comparisonInputsOfData` with `FoldSpec.toSpecData`. -/
noncomputable def comparisonInputsOfFold (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (In : FirstStageInputs blockOf)
    (clique : ∀ q : PrefixCoord, DeletionInputs ((v2Reference blockOf hW spec hC).μ₀ (.inl q))
      (paperPrefixAccepted blockOf (.inl q)) MainAnchor.paperQueries)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (blk : ∀ b : B, FoldSpec hW (spec b))
    (tail : ∀ (q : ℕ) [Fact q.Prime] (h4 : PartV.P4 ≤ q),
      TailAtomInputs q (tailNe hW h4)
        (signedIntegral ((v2Reference blockOf hW spec hC).μp q).weight))
    (St At : ℝ)
    (tail_S : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.sprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ St)
    (tail_A : ∀ L, ∑ j : PaperJt L, (tail (paperTail L j) (P4_le_paperTail j)).toAtom.aprice
      (((paperTail L j : ℕ) : ℝ) ^ (2 * targetDecay)) ≤ At) :
    ComparisonInputs blockOf hW spec hC In :=
  comparisonInputsOfData blockOf hW spec hC In clique
    (fun b => FoldSpec.toSpecData hW In ht0 ht1 (spec b) (blk b)) tail St At tail_S tail_A

end Paper

end Sarkozy.SignedComponents
