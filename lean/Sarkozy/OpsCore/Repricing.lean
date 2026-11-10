module

public import Sarkozy.SignedComponents.Priced

@[expose] public section





open Finset

namespace Sarkozy.OpsCore

open Sarkozy.SignedComponents
open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **B7's `ReplacementData` of a middle block priced at the paper's bounds**: the records of
`ofFold`, with `N := boundN` (the bounds of `NormBounds` at the block's constants). -/
noncomputable def ofFoldK (C : FoldComponents pr hne) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' sF aF ℓ sE aE : ℝ} (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE) :
    ReplacementData pr h (middleFrame pr hne root W I hr b h) where
  t := t
  t_nonneg := ht0
  t_le_one := ht1
  P := foldRec C
  accept j c z hz e := foldRec_accepts C j c z hz e
  unif j c := foldRec_uniform C j c
  N := boundN r b' sF aF ℓ sE aE
  N_nonneg t' e := (boundN_formBound pr h hne root W I hr b C NB t' e).1
  norm t' e F G := (boundN_formBound pr h hne root W I hr b C NB t' e).2 F G

/-- The norms of `ofFoldK` are the bounds. -/
theorem ofFoldK_N (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' sF aF ℓ sE aE : ℝ} (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE)
    (t' : Chg) (e : ChangeType) :
    (ofFoldK pr h hne root W I hr b C t ht0 ht1 NB).N t' e = boundN r b' sF aF ℓ sE aE t' e :=
  rfl

/-- **The price of a fold skew record of `ofFoldK`** is the closed form
`P⁻¹ chgCoef (ℓ r_b + a_F r_b²)` (`MiddleComparison.Atom.piT`). -/
theorem ofFoldK_piT_fold_skew (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' sF aF ℓ sE aE : ℝ} (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE)
    (i : Fin 2) :
    (ofFoldK pr h hne root W I hr b C t ht0 ht1 NB).N (.inl i) .skew =
      ℓ * (1 / Real.sqrt b') + aF * (1 / Real.sqrt b') ^ 2 :=
  rfl

/-- The prices of `ofFold` are below those of `ofFoldK`. -/
theorem ofFold_N_le_ofFoldK (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' sF aF ℓ sE aE : ℝ} (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE)
    (t' : Chg) (e : ChangeType) :
    (ofFold pr h hne root W I hr b C t ht0 ht1).N t' e ≤
      (ofFoldK pr h hne root W I hr b C t ht0 ht1 NB).N t' e :=
  ofFold_N_le pr h hne root W I hr b C ht0 ht1 (boundN_formBound pr h hne root W I hr b C NB t' e)

/-- **The block price bound for `ofFoldK`** (`lem:middle-comparison-prices`): B7's `price_sum_le`
with the same right side as `ofFold_price_sum_le_of`. -/
theorem ofFoldK_price_sum_le_of (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hF : FrameFacts (middleFrame pr hne root W I hr b h) (blockSquareAccepted pr)
      MainAnchor.paperQueries)
    {Xn : ℕ} {b' sel : ℝ} (hX : 4 ≤ Xn) (hb : (Xn : ℝ) ≤ b') (hrb : r = 1 / Real.sqrt b')
    (hsel : 0 ≤ sel) (hfh : 0 ≤ I.f₁ + I.h₁) {sF aF ℓ sE aE : ℝ}
    (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE) :
    ((ofFoldK pr h hne root W I hr b C t ht0 ht1 NB).toReplacements.toAtom hF).sprice sel +
        ((ofFoldK pr h hne root W I hr b C t ht0 ht1 NB).toReplacements.toAtom hF).aprice sel ≤
      ((coefS2 W sE * (1 / Real.sqrt b') ^ 2 + coefS3 W I sF * (1 / Real.sqrt b') ^ 3 +
          coefS4 W (gS (1 / (Xn : ℝ))) * (1 / Real.sqrt b') ^ 4 +
          coefS5 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 5) +
        (coefA2 W ℓ aE * (1 / Real.sqrt b') ^ 2 +
          coefA3 W aF (gA (1 / (Xn : ℝ)) (rXof Xn)) * (1 / Real.sqrt b') ^ 3 +
          coefA4 W (1 / (Xn : ℝ)) * (1 / Real.sqrt b') ^ 4)) * sel := by
  set R := ofFoldK pr h hne root W I hr b C t ht0 ht1 NB
  have hM : MergeRepairBounds b' (fun j => R.toReplacements.N (.inr (.inr (.inl j))) .sym)
      (fun j => R.toReplacements.N (.inr (.inr (.inl j))) .skew) :=
    { sym_nonneg := fun j => R.N_nonneg (.inr (.inr (.inl j))) .sym
      skew_nonneg := fun j => R.N_nonneg (.inr (.inr (.inl j))) .skew
      sym_mirror := fun s k hk => by
        change boundN r b' sF aF ℓ sE aE (.inr (.inr (.inl (s, k)))) .sym ≤ _
        simp [boundN, hk]
      skew_mirror := fun s k hk => by
        change boundN r b' sF aF ℓ sE aE (.inr (.inr (.inl (s, k)))) .skew ≤ _
        simp [boundN, hk]
      sym_first := fun s => by
        change boundN r b' sF aF ℓ sE aE (.inr (.inr (.inl (s, 2)))) .sym ≤ _
        simp [boundN]
      skew_first := fun s => by
        change boundN r b' sF aF ℓ sE aE (.inr (.inr (.inl (s, 2)))) .skew ≤ _
        simp [boundN] }
  exact R.toReplacements.price_sum_le hF hX hb hrb hsel hfh (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) hM (fun _ => le_rfl) (fun _ => le_rfl)

end Frame

end Sarkozy.OpsCore
