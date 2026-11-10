module

public import Sarkozy.FoldSymSkew.Block
public import Sarkozy.PrimeGram.Sanity

@[expose] public section

/-!
# Non-vacuity of FS's hypotheses, and why the route needs the rebased table (FS)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c).

* **`symSkew_crude`**: at every prime of every middle block (primes `≡ 3 (mod 4)`, `≥ 19`), for
  **every** fold components `C`, the hypotheses of `sym_of_decomp`, `skew_of_decomp` hold with
  PG's crude decompositions (`oldDecomp_crude`: `e_o = p(1 + 2Γ)`, `newDecomp_crude`:
  `e_sg = p(2 + 8Γ)`), and the conclusions are FD's `SymPrime`, `SkewPrime` at the resulting crude
  constants. So the decomposition hypotheses are jointly satisfiable at the paper's objects, and
  the content of FS's input is the size `E = O(1)` of `e_sg`.
* **`paper_table_fails`** (kernel): at the paper's table (HS's original `kappaTab` row at `Q₃`; RG's
  rebase replaced `paperKappa` by RB's loosened table) the side conditions of this route fail at
  `Q₃`, even with the paper's sharp `e_o` (`eoX`): `s_F = 11.166 < e_o + e_sg = 24.88` (`92.26` with
  `c_col = 73`), `a_F = 4.797 < e_sg = 17.25`, `ℓ_t = 1.273198 < aNU Γ_X = 1.273483`. The route is
  for the rebased table (`RebaseCheck`).
-/

open Finset Matrix

namespace Sarkozy.FoldSymSkew

open Sarkozy.PartV Sarkozy.SignedComponents Sarkozy.SignedGram Sarkozy.PrimeGram
open Sarkozy.SignedDecomp Sarkozy.NormBoundsPaper4
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.MainFinal2 (tPaper)

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
/-- **Non-vacuity at the paper's objects**: with PG's crude decompositions, `sym_of_decomp` and
`skew_of_decomp` give FD's one-prime statements at every prime of every middle block, for every
fold components. -/
theorem symSkew_crude (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) (i : ι) :
    SymPrime pr hne C tPaper
        (((pr i : ℝ) * (1 + 2 * gammaP pr i) + (pr i : ℝ) * (2 + 8 * gammaP pr i)) *
          (pr i : ℝ)⁻¹) i ∧
      SkewPrime pr hne C tPaper
        (aNorm tPaper * gammaP pr i * rP pr i + (pr i : ℝ) * (2 + 8 * gammaP pr i) *
          (pr i : ℝ)⁻¹) i := by
  have hcard : (Fintype.card (ZMod (pr i)) : ℝ) = (pr i : ℝ) := card_zmod i
  have hΓ0 := gammaP_nonneg h19 i
  have hold := oldDecomp_crude hΓ0 (mP_nonneg hne i) (fun a b => (K0 (hne.F2 i)).nonneg _)
    ((oldP_coupling hne).row i) ((oldP_coupling hne).col i) (frame_block hne h3 h19 i)
  have hnew := newDecomp_crude (P := fun c => compP hne C c i) hΓ0 (mP_nonneg hne i)
    (fun c a b => ((C i).law 0 c).nonneg _) (fun c => (compP_coupling hne C c).row i)
    (fun c => (compP_coupling hne C c).col i) (frame_block hne h3 h19 i)
  have hs := sym_of_decomp (P := fun c => compP hne C c i) (w := signedCoef tPaper) hold hnew
  have hk := skew_of_decomp (P := fun c => compP hne C c i) (C₀ := oldP hne i)
    (w := signedCoef tPaper) (mP_nonneg hne i) hΓ0 (frame_block hne h3 h19 i) hnew
  rw [hcard] at hs hk
  exact ⟨hs, hk⟩

end Block

/-- **The route fails at the paper's table** (kernel, exact rationals, at `Q₃`): even with the
paper's sharp `e_o` (`eoX`), `s_F < e_o + e_sg`, `a_F < e_sg` and `ℓ_t < aNU Γ_X`. The paper's
constants at `Q₃` are HS's original table row (`s_F = 11.166061543`, `a_F = 4.797398687`,
`ℓ_t = 1.273197782`); since RG's rebase (7 November 2026) `HsumProof.paperKappa` is RB's loosened
table, at which the route passes (`Rebase.paperKappa_symSkewSides`). -/
theorem paper_table_fails :
    (11166061543 / 10 ^ 9 : ℚ) < eoX 0 + esgX 0 ∧ (11166061543 / 10 ^ 9 : ℚ) < eo73 0 + esgX 0 ∧
      (4797398687 / 10 ^ 9 : ℚ) < esgX 0 ∧ (1273197782 / 10 ^ 9 : ℚ) < aNU * gamX 0 := by
  decide +kernel

end Sarkozy.FoldSymSkew
