module

public import Sarkozy.FoldSymSkew.Block
public import Sarkozy.CompSharp.Constructor
public import Sarkozy.SignedDecomp.Main2

@[expose] public section

/-!
# All 24 middle norm bounds: NB3's `hNr4` from the signed decomposition (FS)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(a),(b),(c),(e).

C38's `hNr4_of_symSkew34/38` build NB3's `hNr4` (the fold families `Fs`, `Fa`) from FD's one-prime
statements `sym`, `skew` (`SpecSymSkew`) at any piece table `κ`, given `FoldSides`. This file
supplies `SpecSymSkew` from the decomposition of the centred signed record (PG's `NewDecomp`, the
last claim of `prop:signed-bounds`(c)), which is also an input of the block Grams (SD2's `SDB`):

* **`NewDecompAt`**, **`SpecNewDecomp`**: `NewDecomp` at a constant `E` at every prime of a middle
  block (`True` on an upper block);
* **`SymSkewSides κ E k`**: the three numerical side conditions at piece `k`:
  `e_o(X_k) + E_k ≤ s_F(k)` (`e_o` at the crude collision constant `73`, `eo73`),
  `E_k ≤ a_F(k)` and `aNU Γ_X ≤ ℓ(k)`;
* **`symSkew_of_newDecomp`**, **`specSymSkew_of_newDecomp`**: C38's `SymSkew` from `NewDecompAt`;
* **`hNr4_of_newDecomp38`**, **`hNr4_of_newDecomp34`**: `hNr4` at `κ` from `SpecNewDecomp` at
  every middle block, given `FoldSides` and `SymSkewSides` at the 33 pieces;
* **`specNewDecomp_of_analytic2`**, **`hNr4_of_SDB38`**, **`hNr4_of_SDB34`**: the same from SD2's
  front field `SDB : SignedDecompAnalytic2 C` (`NewDecomp` at the paper's `e_sg`, majorized by
  `esgX k`). With these, the fold families need no input beyond `SDB` and the numerical sides.
* **`SpecNewDecompF`**, `specNewDecomp_of_F`, **`hNr4_of_newDecompF38`**: the same from `NewDecomp`
  at a function `e_sg′ = esgF(p)` of the prime (the shape of a crude `SD`), with
  `esgF p ≤ E_k` for `p ≥ X_k`.
-/

namespace Sarkozy.FoldSymSkew

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedGram
open Sarkozy.PrimeGram
open Sarkozy.SignedDecomp
open Sarkozy.NormBoundsPaper4 (eo73)
open Sarkozy.CompSharp
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.MainFinalF1 Sarkozy.BlockSpecPaper Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinal (MiddleConsts)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.NormBoundsPaper3 (SpecNormBoundsRest4)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)

/-- **`prop:signed-bounds`(c), the centred signed record, at the constant `E`, at every prime of a
middle block** (PG's `NewDecomp`): `Π_⊥ T' Π_⊥ = O₀ + L^m_t + R^new`, `‖R^new‖ ≤ E q`. -/
def NewDecompAt {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) (E : ℝ) : Prop :=
  ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne (paperComponents Dc) c i)
    tPaper E

/-- `NewDecompAt` of a block specification (`True` on an upper block). -/
def SpecNewDecomp (hW : Target.Weil) {b : Blk} (E : ℝ) :
    (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E' => NewDecompAt M.hne E'.down.toDC E
  | .middleIndividual M, E' => NewDecompAt M.hne E'.down.toDC E
  | .middleCoherent M, E' => NewDecompAt M.hne E'.down.toDC E

/-- **The side conditions of `sym`, `skew` at piece `k`** for a piece table `κ` and a bound `E_k`
on `e_sg`: `e_o(X_k) + E_k ≤ s_F` (`e_o` at `c_col = 73`), `E_k ≤ a_F`, `aNU Γ_X ≤ ℓ`. -/
def SymSkewSides (κ : Fin 33 → MiddleConsts) (E : Fin 33 → ℚ) (k : Fin 33) : Prop :=
  ((eo73 k + E k : ℚ) : ℝ) ≤ (κ k).sF ∧ ((E k : ℚ) : ℝ) ≤ (κ k).aF ∧
    ((aNU * gamX k : ℚ) : ℝ) ≤ (κ k).ℓ

theorem blockPrimes_ge (b : Blk) (k : Fin 33) (hXb : XQ k ≤ blockLeast b) (j) :
    XQ k ≤ blockPrimes bOf b j :=
  hXb.trans (blockLeast_le b j)

/-- **C38's `SymSkew` (FD's `sym`, `skew`) on a middle block of piece `k`** from `NewDecompAt`. -/
theorem symSkew_of_newDecomp {b : Blk} (hne : MiddleNonempty (blockPrimes bOf b))
    (Dc : DefectConstants b hne tPaper_nonneg tPaper_le_one) (κ : Fin 33 → MiddleConsts)
    (E : Fin 33 → ℚ) (k : Fin 33) (hXb : XQ k ≤ blockLeast b) (hT : SymSkewSides κ E k)
    (H : NewDecompAt hne Dc (E k)) : SymSkew hne Dc (κ k) := by
  obtain ⟨hsF, haF, hℓ⟩ := hT
  push_cast at hsF
  exact symSkew_block hne (paperComponents Dc) (fun j => (blockPrimes_mod_ge b j).1) k
    (blockPrimes_ge b k hXb) H hsF haF hℓ

/-- `SpecNewDecomp` gives C38's `SpecSymSkew` on a block of piece `k`. -/
theorem specSymSkew_of_newDecomp (hW : Target.Weil) {b : Blk} (κ : Fin 33 → MiddleConsts)
    (E : Fin 33 → ℚ) (k : Fin 33) (hXb : XQ k ≤ blockLeast b) (hT : SymSkewSides κ E k) :
    (S : PaperBlockSpec bOf b) → (E' : SignedSpec hW S) → SpecNewDecomp hW (E k) S E' →
      SpecSymSkew hW (κ k) S E'
  | .upper _, _, _ => trivial
  | .middleUniform M, E', H => symSkew_of_newDecomp M.hne E'.down.toDC κ E k hXb hT H
  | .middleIndividual M, E', H => symSkew_of_newDecomp M.hne E'.down.toDC κ E k hXb hT H
  | .middleCoherent M, E', H => symSkew_of_newDecomp M.hne E'.down.toDC κ E k hXb hT H

theorem xq_le_of_site (b : Blk) (i : Fin 33) (hs : blockSite b = .inl i) : XQ i ≤ blockLeast b := by
  have h := siteStart_le_blockLeast b
  rw [hs] at h
  exact h

/-- **`hNr4` (all four fold bounds) at a piece table `κ` from the signed decomposition**, at the
component constant `c_B = 38` (`comp38_paper`): from `NewDecomp` at `E_k` at every prime of every
middle block, given C38's `FoldSides κ 38 0` and `SymSkewSides κ E` at the 33 pieces. -/
theorem hNr4_of_newDecomp38 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts) (E : Fin 33 → ℚ)
    (hS : ∀ k, FoldSides κ 38 0 k) (hT : ∀ k, SymSkewSides κ E k)
    (N : ∀ b i, blockSite b = .inl i → SpecNewDecomp hW (E i) (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) :=
  hNr4_of_symSkew38 hW A blk κ hS fun b i hs =>
    specSymSkew_of_newDecomp hW κ E i (xq_le_of_site b i hs) (hT i) _ _ (N b i hs)

/-- `hNr4_of_newDecomp38` at `c_B = 34`, `R = 1000` (`comp34_paper`). -/
theorem hNr4_of_newDecomp34 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts) (E : Fin 33 → ℚ)
    (hS : ∀ k, FoldSides κ 34 1000 k) (hT : ∀ k, SymSkewSides κ E k)
    (N : ∀ b i, blockSite b = .inl i → SpecNewDecomp hW (E i) (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) :=
  hNr4_of_symSkew34 hW A blk κ hS fun b i hs =>
    specSymSkew_of_newDecomp hW κ E i (xq_le_of_site b i hs) (hT i) _ _ (N b i hs)

/-- **SD2's per-block analytic statement gives `NewDecomp` at `esgX k`** on a block of piece `k`
(the paper's `e_sg` at `p ≥ X_k` is at most `esgX k`, `esgP_le_esgX`). -/
theorem specNewDecomp_of_analytic2 (hW : Target.Weil) {b : Blk} (k : Fin 33)
    (hXb : XQ k ≤ blockLeast b) :
    (S : PaperBlockSpec bOf b) → (E' : SignedSpec hW S) → SpecAnalytic2 hW S E' →
      SpecNewDecomp hW ((esgX k : ℚ) : ℝ) S E'
  | .upper _, _, _ => trivial
  | .middleUniform _, _, H => fun i =>
      newDecomp_mono (H.new i) (esgP_le_esgX k (blockPrimes_ge b k hXb) i)
  | .middleIndividual _, _, H => fun i =>
      newDecomp_mono (H.new i) (esgP_le_esgX k (blockPrimes_ge b k hXb) i)
  | .middleCoherent _, _, H => fun i =>
      newDecomp_mono (H.new i) (esgP_le_esgX k (blockPrimes_ge b k hXb) i)

/-- **All four fold bounds from SD2's front field `SDB`** (`c_B = 38`): NB3's `hNr4` at a piece
table `κ`, given `FoldSides κ 38 0` and `SymSkewSides κ esgX` (kernel-checkable rational
inequalities). With this, the fold families `Fs`, `Fa` need no analytic input beyond `SDB`. -/
theorem hNr4_of_SDB38 {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs f1Cell} {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompAnalytic2 C) (κ : Fin 33 → MiddleConsts) (hS : ∀ k, FoldSides κ 38 0 k)
    (hT : ∀ k, SymSkewSides κ esgX k) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b) :=
  hNr4_of_newDecomp38 hW A C.blk κ esgX hS hT fun b i hs =>
    specNewDecomp_of_analytic2 hW i (xq_le_of_site b i hs) _ _ (H.an b i hs)

/-- `hNr4_of_SDB38` at `c_B = 34`, `R = 1000`. -/
theorem hNr4_of_SDB34 {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
    {A : PaperAnalyticInputs f1Cell} {C : ComparisonPartsTC hW hMR hFour A}
    (H : SignedDecompAnalytic2 C) (κ : Fin 33 → MiddleConsts) (hS : ∀ k, FoldSides κ 34 1000 k)
    (hT : ∀ k, SymSkewSides κ esgX k) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (C.blk b) :=
  hNr4_of_newDecomp34 hW A C.blk κ esgX hS hT fun b i hs =>
    specNewDecomp_of_analytic2 hW i (xq_le_of_site b i hs) _ _ (H.an b i hs)

/-! ## A per-prime constant `e_sg′ = esgF(p)` -/

/-- **`NewDecomp` at a function `esgF` of the prime**, at every prime of a middle block (`True` on
an upper block): the shape of the input `new` of a crude `SD` with `e_sg′ = esgF(p)`. -/
def SpecNewDecompF (hW : Target.Weil) (esgF : ℕ → ℝ) {b : Blk} :
    (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E' => ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E'.down.toDC) c i) tPaper
      (esgF (blockPrimes bOf b i))
  | .middleIndividual M, E' => ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E'.down.toDC) c i) tPaper
      (esgF (blockPrimes bOf b i))
  | .middleCoherent M, E' => ∀ i, NewDecomp (mP M.hne i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E'.down.toDC) c i) tPaper
      (esgF (blockPrimes bOf b i))

/-- `SpecNewDecompF` gives `SpecNewDecomp` at `E` on a block of piece `k`, when `esgF p ≤ E` for
`p ≥ X_k`. -/
theorem specNewDecomp_of_F (hW : Target.Weil) {b : Blk} (esgF : ℕ → ℝ) (E : ℝ) (k : Fin 33)
    (hXb : XQ k ≤ blockLeast b) (hE : ∀ p, XQ k ≤ p → esgF p ≤ E) :
    (S : PaperBlockSpec bOf b) → (E' : SignedSpec hW S) → SpecNewDecompF hW esgF S E' →
      SpecNewDecomp hW E S E'
  | .upper _, _, _ => trivial
  | .middleUniform _, _, H => fun i => newDecomp_mono (H i) (hE _ (blockPrimes_ge b k hXb i))
  | .middleIndividual _, _, H => fun i => newDecomp_mono (H i) (hE _ (blockPrimes_ge b k hXb i))
  | .middleCoherent _, _, H => fun i => newDecomp_mono (H i) (hE _ (blockPrimes_ge b k hXb i))

/-- **`hNr4` from `NewDecomp` at `e_sg′ = esgF(p)`** (`c_B = 38`), with `esgF p ≤ E_k` for
`p ≥ X_k`, given `FoldSides κ 38 0` and `SymSkewSides κ E`. -/
theorem hNr4_of_newDecompF38 (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (blk : ∀ b, SignedSpec hW (specF hW A b)) (κ : Fin 33 → MiddleConsts) (esgF : ℕ → ℝ)
    (E : Fin 33 → ℚ) (hE : ∀ k p, XQ k ≤ p → esgF p ≤ (E k : ℝ))
    (hS : ∀ k, FoldSides κ 38 0 k) (hT : ∀ k, SymSkewSides κ E k)
    (N : ∀ b i, blockSite b = .inl i → SpecNewDecompF hW esgF (specF hW A b) (blk b)) :
    ∀ b i, blockSite b = .inl i →
      SpecNormBoundsRest4 hW (paperIn f1Cell) (κ i) (blockLeast b) (specF hW A b) (blk b) :=
  hNr4_of_newDecomp38 hW A blk κ E hS hT fun b i hs =>
    specNewDecomp_of_F hW esgF (E i) i (xq_le_of_site b i hs) (hE i) _ _ (N b i hs)

end Sarkozy.FoldSymSkew
