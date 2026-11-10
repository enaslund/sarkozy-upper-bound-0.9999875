module

public import Sarkozy.FoldSymSkew.Constructor
public import Sarkozy.Rebase.Collision
public import Sarkozy.Rebase.Folds

@[expose] public section

/-!
# All four fold bounds from the signed decomposition alone, at the rebased table (RG + FS)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(a),(b),(c),(e), `cert:signed-local`.

FS (`FoldSymSkew`) proved the one-prime fold statements `sym`, `skew` (FD's) from the signed
decomposition `NewDecomp` (`prop:signed-bounds`(c) for the centred signed record, at `e_sg`) and
C38's component norms, given the side conditions `SymSkewSides κ esgX` and `FoldSides κ 38 0`
(`hNr4_of_newDecomp38`); its `hNr4_of_SDB38` takes SD2's two-statement `SDB`. Here:

* **`paperKappa_symSkewSides`** (kernel, exact rationals): FS's `SymSkewSides paperKappa esgX` at
  the official rebased table (RB's `kappaTab′`, `HsumProof.PaperKappaData`):
  `e_o(X) + e_sg(X) ≤ s_F` (`e_o` at `c_col = 73`), `e_sg(X) ≤ a_F`, `a_ν Γ_X ≤ ℓ_t`. (The `ℓ_t`
  side needs `ℓ_t × 1.00022`; the table has `× 1.01`.) With `Rebase.foldSides38_paperKappa`, both
  of FS's side conditions hold.
* **`specNewDecomp_of_new`**, **`hNr4_of_new38`**: NB3's `hNr4` (the four fold bounds) at any table
  satisfying the side conditions, from RG's one-statement `Rebase.SignedDecompNew` (the `new` half
  of SD2's `SDB`; the collision bound is proved at `c_col = 73`);
* **`hNr4_paperKappa`**: `hNr4` at `paperKappa` from `SignedDecompNew` alone.

So the companion's front needs no fold input at all: FD's `hFold` is dropped
(`Companion.CompanionFront`).
-/

namespace Sarkozy.Rebase

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedGram
open Sarkozy.PrimeGram
open Sarkozy.SignedDecomp
open Sarkozy.FoldSymSkew
open Sarkozy.NormBoundsPaper4 (eo73)
open Sarkozy.CompSharp (FoldSides)
open Sarkozy.HsumProof (paperKappa kSF kAF kL)
open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.NormBoundsPaper3 (SpecNormBoundsRest4)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)

/-- **FS's `SymSkewSides` on the rebased table** (kernel, exact rationals). -/
theorem symSkewSides_check : ∀ k : Fin 33,
    eo73 k + esgX k ≤ kSF k ∧ esgX k ≤ kAF k ∧ aNU * gamX k ≤ kL k := by
  decide +kernel

/-- **`SymSkewSides paperKappa esgX k`** at every piece. -/
theorem paperKappa_symSkewSides (k : Fin 33) : SymSkewSides paperKappa esgX k := by
  obtain ⟨h1, h2, h3⟩ := symSkewSides_check k
  refine ⟨?_, ?_, ?_⟩
  · change (((eo73 k + esgX k : ℚ)) : ℝ) ≤ (kSF k : ℝ); exact_mod_cast h1
  · change ((esgX k : ℚ) : ℝ) ≤ (kAF k : ℝ); exact_mod_cast h2
  · change ((aNU * gamX k : ℚ) : ℝ) ≤ (kL k : ℝ); exact_mod_cast h3

variable (hW : Target.Weil)

/-- RG's `SpecNew` gives FS's `SpecNewDecomp` at the piece majorant `esgX k`. -/
theorem specNewDecomp_of_new {b : Blk} (k : Fin 33) (hXb : XQ k ≤ blockLeast b) :
    (S : PaperBlockSpec bOf b) → (E' : SignedSpec hW S) → SpecNew hW S E' →
      SpecNewDecomp hW ((esgX k : ℚ) : ℝ) S E'
  | .upper _, _, _ => trivial
  | .middleUniform _, _, H => fun i =>
      newDecomp_mono (H i) (esgP_le_esgX k (blockPrimes_ge b k hXb) i)
  | .middleIndividual _, _, H => fun i =>
      newDecomp_mono (H i) (esgP_le_esgX k (blockPrimes_ge b k hXb) i)
  | .middleCoherent _, _, H => fun i =>
      newDecomp_mono (H i) (esgP_le_esgX k (blockPrimes_ge b k hXb) i)

variable {hW}

/-- **All four fold bounds from the signed decomposition alone** (`c_B = 38`): NB3's `hNr4` at a
piece table `κ` from RG's `SignedDecompNew`, given C38's `FoldSides κ 38 0` and FS's
`SymSkewSides κ esgX`. -/
theorem hNr4_of_new38 {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs f1Cell} {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompNew C) (κ : Fin 33 → MiddleConsts) (hS : ∀ k, FoldSides κ 38 0 k)
    (hT : ∀ k, SymSkewSides κ esgX k) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b) :=
  hNr4_of_newDecomp38 hW A C.blk κ esgX hS hT fun b i hs =>
    specNewDecomp_of_new hW i (xq_le_of_site b i hs) _ _ (H.an b i hs)

/-- **`hNr4` at the rebased table from `SignedDecompNew` alone.** -/
theorem hNr4_paperKappa {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs f1Cell} {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompNew C) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (paperKappa i) (blockLeast b) (specF hW A b)
        (C.blk b) :=
  hNr4_of_new38 H paperKappa foldSides38_paperKappa paperKappa_symSkewSides

end Sarkozy.Rebase
