module

public import Sarkozy.CompSharp.FoldGen
public import Sarkozy.NormBoundsPaper4.Constructor

@[expose] public section

/-!
# NB3's `hNr4` (the fold families) from `sym`, `skew` alone, at a crude component constant (C38)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(a),(b),(e), and (c) Step 1.

FD's `hNr4_of_inputs` (at `paperKappa`, component norms at the paper's `c_+`) with:
* any piece table `κ : Fin 33 → MiddleConsts` (e.g. a rebased one), and
* the component norms proved, at `c_B r + R q`.

* **`SpecFoldInputsC`**: `FoldInputsC` on a middle block, `True` on an upper block;
* **`SpecSymSkew`**: only the fields `sym`, `skew` of FD's `FoldInputs` (the one-prime
  `prop:signed-bounds`(c) statements); `specFoldInputsC_of34`, `specFoldInputsC_of38` add `comp`;
* `specRest4_of_inputsC`: NB3's `SpecNormBoundsRest4` on a block of piece `k`;
* **`hNr4_of_inputsC`**: the field `hNr4` at a piece table `κ`, from `SpecFoldInputsC`, given the
  side conditions `(Γ_X + e_o r_X)² + (1 + t)c'² ≤ s_F(k)`, `(1 + t)c'² ≤ a_F(k)`, `c' r_X ≤ 1`,
  `c' = c_B + R r_X`, at the 33 pieces;
* **`hNr4_of_symSkew34`**, **`hNr4_of_symSkew38`**: the same from `SpecSymSkew` alone, at
  `c_B = 34`, `R = 1000` and at `c_B = 38`, `R = 0`.
-/

namespace Sarkozy.CompSharp

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedGram
open Sarkozy.PrimeGram (rP)
open Sarkozy.SignedDecomp (XQ gamX rX)
open Sarkozy.NormBoundsPaper4 (eo73 SymPrime SkewPrime paper_reflected)
open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.NormBoundsPaper2 (blockLeast_facts24)
open Sarkozy.NormBoundsPaper3 (SpecNormBoundsRest4)

/-- **`FoldInputsC` of a block specification** (`True` on an upper block), at the piece
constants `κ` and the component constant `c_B r + R q`. -/
def SpecFoldInputsC (hW : Target.Weil) {b : Blk} (κ : MiddleConsts) (cB R : ℝ) :
    (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => FoldInputsC (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
      κ.sF κ.aF κ.ℓ cB R
  | .middleIndividual M, E => FoldInputsC (blockPrimes bOf b) M.hne
      (paperComponents E.down.toDC) κ.sF κ.aF κ.ℓ cB R
  | .middleCoherent M, E => FoldInputsC (blockPrimes bOf b) M.hne (paperComponents E.down.toDC)
      κ.sF κ.aF κ.ℓ cB R

/-- **The one-prime fold statements only** (`sym`, `skew` of FD's `FoldInputs`;
`prop:signed-bounds`(c) at one prime, symmetric and skew parts), on a middle block; `True` on an
upper block. -/
def SymSkew {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) (κ : MiddleConsts) : Prop :=
  (∀ i, SymPrime (blockPrimes bOf b) hne (paperComponents Dc) tPaper
      (κ.sF * rP (blockPrimes bOf b) i ^ 2) i) ∧
    ∀ i, SkewPrime (blockPrimes bOf b) hne (paperComponents Dc) tPaper
      (κ.ℓ * rP (blockPrimes bOf b) i + κ.aF * rP (blockPrimes bOf b) i ^ 2) i

/-- `SymSkew` of a block specification (`True` on an upper block). -/
def SpecSymSkew (hW : Target.Weil) {b : Blk} (κ : MiddleConsts) :
    (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => SymSkew M.hne E.down.toDC κ
  | .middleIndividual M, E => SymSkew M.hne E.down.toDC κ
  | .middleCoherent M, E => SymSkew M.hne E.down.toDC κ

/-- `SpecSymSkew` gives `SpecFoldInputsC` at `c_B = 34`, `R = 1000` (`comp34_paper`). -/
theorem specFoldInputsC_of34 (hW : Target.Weil) {b : Blk} (κ : MiddleConsts) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecSymSkew hW κ S E →
      SpecFoldInputsC hW κ 34 1000 S E
  | .upper _, _, _ => trivial
  | .middleUniform _, E, H => FoldInputsC.ofPaper34 E.down.toDC H.1 H.2
  | .middleIndividual _, E, H => FoldInputsC.ofPaper34 E.down.toDC H.1 H.2
  | .middleCoherent _, E, H => FoldInputsC.ofPaper34 E.down.toDC H.1 H.2

/-- `SpecSymSkew` gives `SpecFoldInputsC` at `c_B = 38`, `R = 0` (`comp38_paper`). -/
theorem specFoldInputsC_of38 (hW : Target.Weil) {b : Blk} (κ : MiddleConsts) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecSymSkew hW κ S E →
      SpecFoldInputsC hW κ 38 0 S E
  | .upper _, _, _ => trivial
  | .middleUniform _, E, H => FoldInputsC.ofPaper38 E.down.toDC H.1 H.2
  | .middleIndividual _, E, H => FoldInputsC.ofPaper38 E.down.toDC H.1 H.2
  | .middleCoherent _, E, H => FoldInputsC.ofPaper38 E.down.toDC H.1 H.2

/-- **NB3's `SpecNormBoundsRest4` from `SpecFoldInputsC`** on a block of piece `k`
(`fold_paper_gen`). -/
theorem specRest4_of_inputsC (hW : Target.Weil) (In : FirstStageInputs bOf) {b : Blk}
    (κ : MiddleConsts) (k : Fin 33) {cB R : ℝ} (hcB : 0 ≤ cB) (hR0 : 0 ≤ R)
    (hXb : XQ k ≤ blockLeast b) (hℓ : 0 ≤ κ.ℓ)
    (hsF : (((gamX k + eo73 k * rX k) ^ 2 : ℚ) : ℝ) +
      627 / 500 * (cB + R * ((rX k : ℚ) : ℝ)) ^ 2 ≤ κ.sF)
    (haF : 627 / 500 * (cB + R * ((rX k : ℚ) : ℝ)) ^ 2 ≤ κ.aF)
    (hc1 : (cB + R * ((rX k : ℚ) : ℝ)) * ((rX k : ℚ) : ℝ) ≤ 1) :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) →
      SpecFoldInputsC hW κ cB R S E → SpecNormBoundsRest4 hW In κ (blockLeast b) S E := by
  have hXb' : (XQ k : ℝ) ≤ blockLeast b := by exact_mod_cast hXb
  obtain ⟨-, hbp⟩ := blockLeast_facts24 b
  intro S E R'
  match S, E, R' with
  | .upper _, _, _ => trivial
  | .middleUniform _, E, R' =>
    exact fold_paper_gen _ _ _ _ _ _ _ _ _ (paper_reflected E.down.toDC) k hcB hR0 hXb' hbp hℓ
      hsF haF hc1 R'
  | .middleIndividual _, E, R' =>
    exact fold_paper_gen _ _ _ _ _ _ _ _ _ (paper_reflected E.down.toDC) k hcB hR0 hXb' hbp hℓ
      hsF haF hc1 R'
  | .middleCoherent _, E, R' =>
    exact fold_paper_gen _ _ _ _ _ _ _ _ _ (paper_reflected E.down.toDC) k hcB hR0 hXb' hbp hℓ
      hsF haF hc1 R'

/-- The side conditions of `fold_paper_gen` at piece `k`, for a piece table `κ` and the component
constant `c' = c_B + R r_X`. -/
def FoldSides (κ : Fin 33 → MiddleConsts) (cB R : ℝ) (k : Fin 33) : Prop :=
  0 ≤ (κ k).ℓ ∧
    (((gamX k + eo73 k * rX k) ^ 2 : ℚ) : ℝ) + 627 / 500 * (cB + R * ((rX k : ℚ) : ℝ)) ^ 2 ≤
      (κ k).sF ∧
    627 / 500 * (cB + R * ((rX k : ℚ) : ℝ)) ^ 2 ≤ (κ k).aF ∧
    (cB + R * ((rX k : ℚ) : ℝ)) * ((rX k : ℚ) : ℝ) ≤ 1

/-- **The field `hNr4` at a piece table `κ` from `SpecFoldInputsC`** (FD's `hNr4_of_inputs` with
`κ` general and the component constant `c_B r + R q`), given the side conditions at the 33
pieces. -/
theorem hNr4_of_inputsC (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts) {cB R : ℝ}
    (hcB : 0 ≤ cB) (hR0 : 0 ≤ R) (hS : ∀ k, FoldSides κ cB R k)
    (Rin : ∀ b i, blockSite b = .inl i → SpecFoldInputsC hW (κ i) cB R (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) := by
  intro b i hs
  have hXb : XQ i ≤ blockLeast b := by
    have h := siteStart_le_blockLeast b
    rw [hs] at h
    exact h
  obtain ⟨hℓ, hsF, haF, hc1⟩ := hS i
  exact specRest4_of_inputsC hW (paperIn f1Cell) (κ i) i hcB hR0 hXb hℓ hsF haF hc1
    (specF hW A b) (blk b) (Rin b i hs)

/-- **`hNr4` from the one-prime statements `sym`, `skew` alone, at `c_B = 34`, `R = 1000`**: the
component norms are proved (`comp34_paper`). -/
theorem hNr4_of_symSkew34 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts)
    (hS : ∀ k, FoldSides κ 34 1000 k)
    (Rin : ∀ b i, blockSite b = .inl i → SpecSymSkew hW (κ i) (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) :=
  hNr4_of_inputsC hW A blk κ (by norm_num) (by norm_num) hS fun b i hs =>
    specFoldInputsC_of34 hW (κ i) _ _ (Rin b i hs)

/-- **`hNr4` from `sym`, `skew` alone, at `c_B = 38`, `R = 0`** (`comp38_paper`). -/
theorem hNr4_of_symSkew38 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts)
    (hS : ∀ k, FoldSides κ 38 0 k)
    (Rin : ∀ b i, blockSite b = .inl i → SpecSymSkew hW (κ i) (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) :=
  hNr4_of_inputsC hW A blk κ (by norm_num) le_rfl hS fun b i hs =>
    specFoldInputsC_of38 hW (κ i) _ _ (Rin b i hs)

end Sarkozy.CompSharp
