module

public import Sarkozy.SignedComponents.Data

@[expose] public section





open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords

/-- **The twelve norm bounds of a middle block as a function of the change** (`NormBounds`):
folds `s_F r²`, `ℓ r + a_F r²`; matchings `s_E r`, `a_E r`; merges `sG`, `aG` (`k ≠ 2`),
`dG + etaG`, `gammaG` (`k = 2`); constants `r²/(1 - 1/b)²`, `r/(1 - 1/b)`, with `r = b'^{-1/2}`
for the folds and matchings. -/
noncomputable def boundN (r b' sF aF ℓ sE aE : ℝ) : Chg → ChangeType → ℝ
  | .inl _, .sym => sF * (1 / Real.sqrt b') ^ 2
  | .inl _, .skew => ℓ * (1 / Real.sqrt b') + aF * (1 / Real.sqrt b') ^ 2
  | .inr (.inl _), .sym => sE * (1 / Real.sqrt b')
  | .inr (.inl _), .skew => aE * (1 / Real.sqrt b')
  | .inr (.inr (.inl j)), .sym => if j.2 = 2 then dG b' + etaG b' else sG b'
  | .inr (.inr (.inl j)), .skew => if j.2 = 2 then gammaG b' else aG b'
  | .inr (.inr (.inr _)), .sym => r ^ 2 / (1 - 1 / b') ^ 2
  | .inr (.inr (.inr _)), .skew => r / (1 - 1 / b')

/-- **The bounds are monotone in the five constants** (the merges and constants do not depend on
them). -/
theorem boundN_mono {r b' sF aF ℓ sE aE sF' aF' ℓ' sE' aE' : ℝ} (hsF : sF ≤ sF') (haF : aF ≤ aF')
    (hℓ : ℓ ≤ ℓ') (hsE : sE ≤ sE') (haE : aE ≤ aE') (t' : Chg) (e : ChangeType) :
    boundN r b' sF aF ℓ sE aE t' e ≤ boundN r b' sF' aF' ℓ' sE' aE' t' e := by
  have h0 : 0 ≤ 1 / Real.sqrt b' := by positivity
  rcases t' with i | i | ⟨s, k⟩ | k <;> cases e
  · exact mul_le_mul_of_nonneg_right hsF (pow_nonneg h0 2)
  · exact add_le_add (mul_le_mul_of_nonneg_right hℓ h0)
      (mul_le_mul_of_nonneg_right haF (pow_nonneg h0 2))
  · exact mul_le_mul_of_nonneg_right hsE h0
  · exact mul_le_mul_of_nonneg_right haE h0
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- Every change satisfies its bound. -/
theorem boundN_formBound (C : FoldComponents pr hne) {t b' sF aF ℓ sE aE : ℝ}
    (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE) (t' : Chg) (e : ChangeType) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) t')
      (foldChange pr h hne root W I hr b C t t' e) (boundN r b' sF aF ℓ sE aE t' e) := by
  rcases t' with i | i | ⟨s, k⟩ | k <;> cases e
  · exact NB.Fs i
  · exact NB.Fa i
  · exact NB.Es i
  · exact NB.Ea i
  · by_cases hk : k = 2
    · subst hk; simpa [boundN] using NB.Ms₂ s
    · simpa [boundN, hk] using NB.Ms s k hk
  · by_cases hk : k = 2
    · subst hk; simpa [boundN] using NB.Ma₂ s
    · simpa [boundN, hk] using NB.Ma s k hk
  · exact NB.Cs k
  · exact NB.Ca k

/-- **B7's `ReplacementData` of a middle block priced at the paper's bounds**: the records of
`ofFold` (the fold components `C`, any `t ∈ [0, 1]`), with `N := max(optNorm, boundN)` at the
constants `b' sF aF ℓ sE aE` (the least prime and the piece constants). Only the constants enter
the construction; the `norm` field comes from the optimal norm. Under `NormBounds` at the same
constants the prices are the bounds (`ofFoldM_N_eq`). -/
noncomputable def ofFoldM (C : FoldComponents pr hne) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (b' sF aF ℓ sE aE : ℝ) : ReplacementData pr h (middleFrame pr hne root W I hr b h) where
  t := t
  t_nonneg := ht0
  t_le_one := ht1
  P := foldRec C
  accept j c z hz e := foldRec_accepts C j c z hz e
  unif j c := foldRec_uniform C j c
  N t' e := max ((ofFold pr h hne root W I hr b C t ht0 ht1).N t' e)
    (boundN r b' sF aF ℓ sE aE t' e)
  N_nonneg t' e := le_max_of_le_left ((ofFold pr h hne root W I hr b C t ht0 ht1).N_nonneg t' e)
  norm t' e F G := by
    refine ((ofFold pr h hne root W I hr b C t ht0 ht1).norm t' e F G).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- **Under the paper's twelve bounds the prices of `ofFoldM` are exactly the bounds.** -/
theorem ofFoldM_N_eq (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' sF aF ℓ sE aE : ℝ} (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE)
    (t' : Chg) (e : ChangeType) :
    (ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF aF ℓ sE aE).N t' e =
      boundN r b' sF aF ℓ sE aE t' e :=
  max_eq_right (ofFold_N_le pr h hne root W I hr b C ht0 ht1
    (boundN_formBound pr h hne root W I hr b C NB t' e))

/-- **The prices of `ofFoldM` at constants `κ⁰` are below the bounds at any larger constants `κ`
at which the twelve norm bounds hold.** -/
theorem ofFoldM_N_le (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' sF₀ aF₀ ℓ₀ sE₀ aE₀ sF aF ℓ sE aE : ℝ}
    (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE)
    (hle : ∀ t' e, boundN r b' sF₀ aF₀ ℓ₀ sE₀ aE₀ t' e ≤ boundN r b' sF aF ℓ sE aE t' e)
    (t' : Chg) (e : ChangeType) :
    (ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF₀ aF₀ ℓ₀ sE₀ aE₀).N t' e ≤
      boundN r b' sF aF ℓ sE aE t' e :=
  max_le (ofFold_N_le pr h hne root W I hr b C ht0 ht1
    (boundN_formBound pr h hne root W I hr b C NB t' e)) (hle t' e)

/-- The replacements of `ofFoldM` are those of `ofFold`. -/
theorem ofFoldM_newMeas (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (b' sF aF ℓ sE aE : ℝ) :
    (ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.newMeas =
      (ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.newMeas :=
  rfl

/-- The record laws of the atom of `ofFoldM` are those of `ofFold`. -/
theorem ofFoldM_D (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (b' sF aF ℓ sE aE : ℝ)
    (hF : FrameFacts (middleFrame pr hne root W I hr b h) (blockSquareAccepted pr)
      MainAnchor.paperQueries) :
    ((ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.toAtom hF).D =
      ((ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.toAtom hF).D :=
  rfl

/-- The changes of the atom of `ofFoldM` are those of `ofFold`. -/
theorem ofFoldM_Δ (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (b' sF aF ℓ sE aE : ℝ)
    (hF : FrameFacts (middleFrame pr hne root W I hr b h) (blockSquareAccepted pr)
      MainAnchor.paperQueries) :
    ((ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.toAtom hF).Δ =
      ((ofFold pr h hne root W I hr b C t ht0 ht1).toReplacements.toAtom hF).Δ :=
  rfl

/-- **The block price bound for `ofFoldM`** (`lem:middle-comparison-prices`), with the right side
of `ofFold_price_sum_le_of`, from `NormBounds` at the pricing constants. -/
theorem ofFoldM_price_sum_le_of (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : FrameFacts (middleFrame pr hne root W I hr b h) (blockSquareAccepted pr)
      MainAnchor.paperQueries)
    {Xn : ℕ} {b' sel : ℝ} (hX : 4 ≤ Xn) (hb : (Xn : ℝ) ≤ b') (hrb : r = 1 / Real.sqrt b')
    (hsel : 0 ≤ sel) (hfh : 0 ≤ I.f₁ + I.h₁) {sF aF ℓ sE aE : ℝ}
    (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE) :
    ((ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.toAtom
        hF).sprice sel +
        ((ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.toAtom
          hF).aprice sel ≤
      ((coefS2 W sE * (1 / Real.sqrt b') ^ 2 + coefS3 W I sF * (1 / Real.sqrt b') ^ 3 +
          coefS4 W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b') ^ 4 +
          coefS5 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 5) +
        (coefA2 W ℓ aE * (1 / Real.sqrt b') ^ 2 +
          coefA3 W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b') ^ 3 +
          coefA4 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 4)) * sel := by
  set R := ofFoldM pr h hne root W I hr b C t ht0 ht1 b' sF aF ℓ sE aE
  have hE : ∀ t' e, R.toReplacements.N t' e = boundN r b' sF aF ℓ sE aE t' e :=
    ofFoldM_N_eq pr h hne root W I hr b C ht0 ht1 NB
  have hM : MergeRepairBounds b' (fun j => R.toReplacements.N (.inr (.inr (.inl j))) .sym)
      (fun j => R.toReplacements.N (.inr (.inr (.inl j))) .skew) :=
    { sym_nonneg := fun j => R.N_nonneg (.inr (.inr (.inl j))) .sym
      skew_nonneg := fun j => R.N_nonneg (.inr (.inr (.inl j))) .skew
      sym_mirror := fun s k hk => by simp [hE, boundN, hk]
      skew_mirror := fun s k hk => by simp [hE, boundN, hk]
      sym_first := fun s => by simp [hE, boundN]
      skew_first := fun s => by simp [hE, boundN] }
  exact R.toReplacements.price_sum_le hF hX hb hrb hsel hfh (fun _ => (hE _ _).le)
    (fun _ => (hE _ _).le) (fun _ => (hE _ _).le) (fun _ => (hE _ _).le) hM
    (fun _ => (hE _ _).le) (fun _ => (hE _ _).le)

end Frame

/-! ## B7's `SpecData` at the bound prices -/

section Paper

open Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.FirstStagePaper Sarkozy.PartVLaws
open Sarkozy.CancellationSteps

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **B7's `SpecData` from the fold components, priced at given bounds** (`ofFoldM` on every
middle block, with one `t ∈ [0, 1]`, the least prime `bl` and the constants `sF aF ℓ sE aE`): the
records are those of `FoldSpec.toSpecData`, the prices `max(optNorm, boundN)`. -/
noncomputable def FoldSpec.toSpecDataM (hW : Target.Weil) (In : FirstStageInputs blockOf) {b : B}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (bl sF aF ℓ sE aE : ℝ) :
    (S : PaperBlockSpec blockOf b) → FoldSpec hW S → SpecData hW In S
  | .upper _, U => U
  | .middleUniform M, C => ⟨ofFoldM _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b)
      C.down t ht0 ht1 bl sF aF ℓ sE aE⟩
  | .middleIndividual M, C => ⟨ofFoldM _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr
      (In.bmin b) C.down t ht0 ht1 bl sF aF ℓ sE aE⟩
  | .middleCoherent M, C => ⟨ofFoldM _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr
      (In.bmin b) C.down t ht0 ht1 bl sF aF ℓ sE aE⟩

end Paper

end Sarkozy.SignedComponents
