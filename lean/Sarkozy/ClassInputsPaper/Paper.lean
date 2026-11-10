module

public import Sarkozy.ClassInputsPaper.FromEnergy
public import Sarkozy.ClassBoundsPaper.Sanity

@[expose] public section

/-!
# The class data at the paper's numbers

`paper/sections/28_closing.tex`, `prop:closing-data`(d), `def:closing-quantities`(2), (7);
`paper/sections/23_envelopes.tex`, `cor:envelope-costs`; `paper/sections/09_comparison_theorem.tex`,
`def:cp5`.

`ClassData.paper` fixes the fields of `ClassData` that the closing fixes:
* `N := paperN`, the 49 degree vectors of the sixteen classes of `cor:envelope-costs` (B4), with
  `hN := paperN_valid`;
* `Bp := targetLedger.B` (`def:closing-quantities`(2)), with `Bp_nonneg := targetLedger_B_nonneg`;
* `nmax := 6` (`def:cp5`): on the degree classes it is `paperN_deg_le` with
  `card_support_of_mem_kindMonos`; on the variance classes it is asked (`nmax_var`).

The class costs `C` (`def:closing-quantities`(7); `paperC`, or below it with the credit counted in
`PolynomialData.hDvar`), the kinds, the auxiliary prices and the variance classes remain
parameters. For these data B4's `PolynomialData.hBp` and `PolynomialData.hN` hold by `rfl`
(`paper_Bp`, `paper_N`).
-/

open Finset

namespace Sarkozy.ClassInputsPaper

open Sarkozy.ClassBoundsPaper
open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetLedger)

variable {a : ℝ} {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R}

/-- **The class data at the closing's numbers** (`prop:closing-data`(d)): `N = paperN`,
`B' = targetLedger.B`, `n_max = 6`; the costs, the kinds, the auxiliary prices and the variance
classes are parameters. -/
noncomputable def ClassData.paper (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS)
    (C : (Fin 3 → ℕ) → ℝ) (C_nonneg : ∀ n ∈ paperN, 0 ≤ C n)
    (π_nonneg : ∀ L b t e, 0 ≤ CL.π L b t e)
    (kind : ∀ L, PriceVar (CL.T L) → Option (Fin 3))
    (kind_skew : ∀ L v l, kind L v = some l → v.2.2 = .skew)
    (yarm ylead yrem : ∀ L, PriceVar (CL.T L) → ℝ) (yarm_nonneg : ∀ L v, 0 ≤ yarm L v)
    (ylead_nonneg : ∀ L v, 0 ≤ ylead L v) (yrem_nonneg : ∀ L v, 0 ≤ yrem L v)
    (V : ℕ → Type) [∀ L, Fintype (V L)] [∀ L, DecidableEq (V L)]
    (vcls : ∀ L, Choice (CL.T L) → Option (V L)) (vcost : ∀ L, Choice (CL.T L) → ℝ)
    (vcost_nonneg : ∀ L ω, 0 ≤ vcost L ω)
    (nmax_var : ∀ L (ω : Choice (CL.T L)), IsSelection ω → vcls L ω ≠ none →
      (Choice.support ω).card ≤ 6) :
    ClassData CL where
  N := paperN
  hN := paperN_valid
  C := C
  C_nonneg := C_nonneg
  Bp := targetLedger.B
  Bp_nonneg := targetLedger_B_nonneg
  π_nonneg := π_nonneg
  kind := kind
  kind_skew := kind_skew
  yarm := yarm
  ylead := ylead
  yrem := yrem
  yarm_nonneg := yarm_nonneg
  ylead_nonneg := ylead_nonneg
  yrem_nonneg := yrem_nonneg
  V := V
  vcls := vcls
  vcost := vcost
  vcost_nonneg := vcost_nonneg
  nmax := 6
  nmax_bound L ω hω h := by
    rcases h with h | h
    · obtain ⟨n, hn, hm⟩ := mem_biUnion.mp h
      rw [card_support_of_mem_kindMonos hm]
      exact paperN_deg_le n hn
    · exact nmax_var L ω hω h

section Facts

variable (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS)
    (C : (Fin 3 → ℕ) → ℝ) (C_nonneg : ∀ n ∈ paperN, 0 ≤ C n)
    (π_nonneg : ∀ L b t e, 0 ≤ CL.π L b t e)
    (kind : ∀ L, PriceVar (CL.T L) → Option (Fin 3))
    (kind_skew : ∀ L v l, kind L v = some l → v.2.2 = .skew)
    (yarm ylead yrem : ∀ L, PriceVar (CL.T L) → ℝ) (yarm_nonneg : ∀ L v, 0 ≤ yarm L v)
    (ylead_nonneg : ∀ L v, 0 ≤ ylead L v) (yrem_nonneg : ∀ L v, 0 ≤ yrem L v)
    (V : ℕ → Type) [∀ L, Fintype (V L)] [∀ L, DecidableEq (V L)]
    (vcls : ∀ L, Choice (CL.T L) → Option (V L)) (vcost : ∀ L, Choice (CL.T L) → ℝ)
    (vcost_nonneg : ∀ L ω, 0 ≤ vcost L ω)
    (nmax_var : ∀ L (ω : Choice (CL.T L)), IsSelection ω → vcls L ω ≠ none →
      (Choice.support ω).card ≤ 6)

/-- B4's `PolynomialData.hN` for the paper's class data: `N = paperN`. -/
theorem ClassData.paper_N (h : (ClassData.paper CL C C_nonneg π_nonneg kind kind_skew yarm ylead
      yrem yarm_nonneg ylead_nonneg yrem_nonneg V vcls vcost vcost_nonneg nmax_var).Robust) :
    ((ClassData.paper CL C C_nonneg π_nonneg kind kind_skew yarm ylead yrem yarm_nonneg
      ylead_nonneg yrem_nonneg V vcls vcost vcost_nonneg nmax_var).toInputs h).N = paperN := rfl

/-- B4's `PolynomialData.hBp` for the paper's class data: `B' = targetLedger.B`. -/
theorem ClassData.paper_Bp (h : (ClassData.paper CL C C_nonneg π_nonneg kind kind_skew yarm ylead
      yrem yarm_nonneg ylead_nonneg yrem_nonneg V vcls vcost vcost_nonneg nmax_var).Robust) :
    ((ClassData.paper CL C C_nonneg π_nonneg kind kind_skew yarm ylead yrem yarm_nonneg
      ylead_nonneg yrem_nonneg V vcls vcost vcost_nonneg nmax_var).toInputs h).Bp =
      targetLedger.B := rfl

end Facts

end Sarkozy.ClassInputsPaper
