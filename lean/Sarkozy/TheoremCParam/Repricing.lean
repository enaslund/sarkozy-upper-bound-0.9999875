module

public import Sarkozy.TheoremC.Repricing
public import Sarkozy.TheoremCParam.Main

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.Comparison Sarkozy.RecordExpansion

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] [DecidableEq P] (D : ComparisonData a m₀ p pr h E)

omit [DecidableEq P] in
/-- `cor:first-stage-repricing` for comparison data: if the totals of (CP2), (CP3) at the
exponent `a` are at most `t` times totals `P'`, `U₀'`, `d'_j`, `v'_j` computed at a smaller
exponent (`t = e^{2(a−a₀)L}`, `total_reprice_le`), then the cost of the first stage, the
error `R_err` and the energy factor `B` of the bracket are bounded by the repriced forms. -/
theorem firstStage_reprice {P' U₀' t : ℝ} {d' v' : D.FS.Tag → ℝ}
    (hP : D.FS.P ≤ t * P') (hU : D.GB.U₀ ≤ t * U₀') (hd : ∀ j, D.FS.dT j ≤ t * d' j)
    (hv : ∀ j, D.FS.vT j ≤ t * v' j) :
    D.L₀ ≤ Real.exp (t * P') * tagSeries (fun j => t * d' j) (fun j => t * v' j) ∧
      D.GB.Rerr ≤ Real.exp (t * U₀') * tagSeries (fun j => t * d' j) (fun j => t * v' j) ∧
      D.B ≤ Real.exp (t * U₀') * (1 + tagSeries (fun j => t * d' j) (fun j => t * v' j)) :=
  Sarkozy.TheoremC.firstStage_reprice D.dT_nonneg D.vT_nonneg hP hU hd hv

end ComparisonData

end Sarkozy.TheoremCParam
