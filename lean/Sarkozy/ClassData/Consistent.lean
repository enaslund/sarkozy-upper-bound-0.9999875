module

public import Sarkozy.ClassData.CostBound
public import Sarkozy.ClassInputsPaper.Paper

@[expose] public section

/-!
# K2's field 41 (`Cls.ES.consistent`) from its analytic inputs, at `a_T`

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i), `cor:envelope-costs`;
`paper/sections/22_variance.tex`, `cor:var-classes`, `cor:variance:final`(i).

`ConsistentInputs` collects, for every scale and class, the inputs of B10's `consistent_inl`
(degree classes) and `consistent_inr` (variance classes) **other than the numerical gate**, at the
class-cost parameters of `CostData.lean`. **`ConsistentInputs.consistent`** is then exactly the
field `consistent` of K2's `ClassEnergySteps`:
`∀ L i, ∑_j wc_{ij} u_j + ∑_{𝒞_i} ρ_ω ≤ ∑_{𝒞_i} φ_ω`.
The numerical gate `classCost ≤ C_n` is `paper_classCost_le` (kernel-checked), and `B ≤ B'` is the
ledger's `B`.
-/

open Finset

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The analytic inputs of the consistency at `a_T`** (`thm:envelopes`(i),
`lem:oct24:invariant-background`(v), `cor:var-classes`), for class data with `N ⊆ paperN`,
`C ≥ paperC` and `B' ≥ B^{ledger}`. On a degree class `n`: the weights `wt`, `C_X`, `υ` of
`consistent_degree`, the background gate `hbg` and the remainder bound `hρ` at the parameters of
`CostData.lean`, and the price identities `harm`, `hυ0`, `hυ`. On a variance class: no weight on
the diagonals (`hwc`) and `ρ_ω ≤ vcost(ω) π_ω` (`hρv`). *Hypotheses*, all analytic. -/
structure ConsistentInputs {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (cd : ClassInputsPaper.ClassData D.CL) (Θ : ℕ → Type) [∀ L, Fintype (Θ L)]
    (wc : ∀ L, cd.ι L → Θ L → ℝ) (u : ∀ L, Θ L → ℝ) (ρ : ∀ L, Choice (D.CL.T L) → ℝ) where
  hN : ∀ n ∈ cd.N, n ∈ paperN
  hC : ∀ n ∈ cd.N, paperC n ≤ cd.C n
  hBp : targetLedger.B ≤ cd.Bp
  wt : ∀ L, {n // n ∈ cd.N} → Choice (D.CL.T L) → ℝ
  CX : ∀ L, {n // n ∈ cd.N} → Choice (D.CL.T L) → ℝ
  υ : ∀ L, {n // n ∈ cd.N} → Choice (D.CL.T L) → ℝ
  hbg : ∀ L n, ∑ j, wc L (.inl n) j * u L j ≤ (paperκH n.1 * Real.exp paperU0 -
      (paperκH n.1 - paperκb n.1) * Real.exp paperTU) *
    ∑ ω ∈ cd.clsSel L (.inl n), mono (cd.yarm L) (selMono ω)
  hρ : ∀ L n, ∑ ω ∈ cd.clsSel L (.inl n), ρ L ω ≤
    (paperM n.1 * paperRerr - paperMinv n.1 * Real.exp paperTU * paperTδ) *
        (∑ ω ∈ cd.clsSel L (.inl n), wt L n ω * CX L n ω) +
      targetLedger.B * (∑ ω ∈ cd.clsSel L (.inl n), wt L n ω * υ L n ω * CX L n ω)
  harm : ∀ L n, ∀ ω ∈ cd.clsSel L (.inl n), wt L n ω * CX L n ω = mono (cd.yarm L) (selMono ω)
  hυ0 : ∀ L n, ∀ ω ∈ cd.clsSel L (.inl n), 0 ≤ wt L n ω * υ L n ω * CX L n ω
  hυ : ∀ L n, ∀ ω ∈ cd.clsSel L (.inl n), wt L n ω * υ L n ω * CX L n ω ≤
    mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) - mono (cd.ylead L) (selMono ω)
  hwc : ∀ L (v : cd.V L) j, wc L (.inr v) j = 0
  hρv : ∀ L (v : cd.V L), ∀ ω ∈ cd.clsSel L (.inr v), ρ L ω ≤ cd.vcost L ω * monomial (D.CL.π L) ω

/-- **K2's field 41** (`ClassEnergySteps.consistent`) from `ConsistentInputs`: B10's
`consistent_inl_paper` on the degree classes (with `classCost ≤ C_n` kernel-checked) and
`consistent_inr` on the variance classes. -/
theorem ConsistentInputs.consistent {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassInputsPaper.ClassData D.CL} {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
    {wc : ∀ L, cd.ι L → Θ L → ℝ} {u : ∀ L, Θ L → ℝ} {ρ : ∀ L, Choice (D.CL.T L) → ℝ}
    (H : ConsistentInputs cd Θ wc u ρ) (L : ℕ) (i : cd.ι L) :
    ∑ j, wc L i j * u L j + ∑ ω ∈ cd.clsSel L i, ρ L ω ≤ ∑ ω ∈ cd.clsSel L i, cd.φ L ω := by
  rcases i with n | v
  · exact consistent_inl_paper cd H.hN H.hC H.hBp L n (wc L (.inl n)) (u L) (ρ L) (H.wt L n)
      (H.CX L n) (H.υ L n) (H.hbg L n) (H.hρ L n) (H.harm L n) (H.hυ0 L n) (H.hυ L n)
  · exact consistent_inr cd L v (wc L (.inr v)) (u L) (ρ L) (H.hwc L v) (H.hρv L v)

/-- B10's `ClassData.paper` at `C = paperC` satisfies the three class-data conditions of
`ConsistentInputs` (`N = paperN`, `C = paperC`, `B' = B^{ledger}`, all by `rfl`). -/
theorem paper_data_conditions {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (π_nonneg : ∀ L b t e, 0 ≤ D.CL.π L b t e)
    (kind : ∀ L, PriceVar (D.CL.T L) → Option (Fin 3))
    (kind_skew : ∀ L v l, kind L v = some l → v.2.2 = .skew)
    (yarm ylead yrem : ∀ L, PriceVar (D.CL.T L) → ℝ) (yarm_nonneg : ∀ L v, 0 ≤ yarm L v)
    (ylead_nonneg : ∀ L v, 0 ≤ ylead L v) (yrem_nonneg : ∀ L v, 0 ≤ yrem L v)
    (V : ℕ → Type) [∀ L, Fintype (V L)] [∀ L, DecidableEq (V L)]
    (vcls : ∀ L, Choice (D.CL.T L) → Option (V L)) (vcost : ∀ L, Choice (D.CL.T L) → ℝ)
    (vcost_nonneg : ∀ L ω, 0 ≤ vcost L ω)
    (nmax_var : ∀ L (ω : Choice (D.CL.T L)), IsSelection ω → vcls L ω ≠ none →
      (Choice.support ω).card ≤ 6) :
    let cd := ClassInputsPaper.ClassData.paper D.CL paperC (fun n _ => paperC_nonneg n) π_nonneg
      kind kind_skew yarm ylead yrem yarm_nonneg ylead_nonneg yrem_nonneg V vcls vcost
      vcost_nonneg nmax_var
    (∀ n ∈ cd.N, n ∈ paperN) ∧ (∀ n ∈ cd.N, paperC n ≤ cd.C n) ∧ targetLedger.B ≤ cd.Bp :=
  ⟨fun _ hn => hn, fun _ _ => le_rfl, le_rfl⟩

end Sarkozy.ClassData
