module

public import Sarkozy.TheoremC.Main
public import Sarkozy.Comparison.Repricing

@[expose] public section

/-!
# The first stage at a larger exponent (`cor:first-stage-repricing`)

`paper/sections/09_comparison_theorem.tex`, `lem:record:repricing` and
`cor:first-stage-repricing`. Every first-stage price is an unpriced part times the
selection factor `q_𝔟^{2a}`; for atoms with `log q_𝔟 ≤ L`, raising the exponent from `a₀` to
`a ≥ a₀` multiplies every such price, hence every total, by at most `t = e^{2(a−a₀)L}`
(`Sarkozy.Comparison.total_reprice`, `lem:record:repricing`). The corollary then bounds the
closing quantities of (CP2), (CP3) through the monotonicity of `exp` and of the tag series
(`rem:cp:tags`, `Sarkozy.RecordExpansion.tagSeries_mono`):

  `L₀ ≤ e^{tP'} 𝔗(td', tv')`, `R_err ≤ e^{tU₀'} 𝔗(td', tv')`, `B ≤ e^{tU₀'}(1 + 𝔗(td', tv'))`.

`firstStage_reprice` is this scalar step for totals `P ≤ tP'`, `U₀ ≤ tU₀'`, `d_j ≤ td'_j`,
`v_j ≤ tv'_j`; `total_reprice_le` is the step from a total at `a₀` to one at `a`.
`ComparisonData.firstStage_reprice` applies it to comparison data. The totals at `a₀` are
not data of `ComparisonData` (its prices use the single exponent `a = decay`), so they enter
as numbers bounding the repriced totals.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.TheoremC

open Sarkozy.Comparison Sarkozy.RecordExpansion

/-- `lem:record:repricing` for a total over a finite set of atoms with `log q_𝔟 ≤ L`. -/
theorem total_reprice_le {ι : Type*} (s : Finset ι) (c q : ι → ℝ) {a₀ a L T' : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hq : ∀ i ∈ s, 1 ≤ q i) (hlog : ∀ i ∈ s, Real.log (q i) ≤ L)
    (ha : a₀ ≤ a) (hT' : ∑ i ∈ s, c i * q i ^ (2 * a₀) ≤ T') :
    ∑ i ∈ s, c i * q i ^ (2 * a) ≤ Real.exp (2 * (a - a₀) * L) * T' :=
  (total_reprice s c q hc hq hlog ha).trans
    (mul_le_mul_of_nonneg_left hT' (Real.exp_pos _).le)

/-- **`cor:first-stage-repricing`, the bounds of the closing quantities.** -/
theorem firstStage_reprice {Tag : Type} [Fintype Tag] [DecidableEq Tag] {P P' U₀ U₀' t : ℝ}
    {d v d' v' : Tag → ℝ} (hd0 : ∀ j, 0 ≤ d j) (hv0 : ∀ j, 0 ≤ v j)
    (hP : P ≤ t * P') (hU : U₀ ≤ t * U₀') (hd : ∀ j, d j ≤ t * d' j)
    (hv : ∀ j, v j ≤ t * v' j) :
    firstStageCost P d v ≤ Real.exp (t * P') * tagSeries (fun j => t * d' j) (fun j => t * v' j) ∧
      Real.exp U₀ * tagSeries d v ≤
        Real.exp (t * U₀') * tagSeries (fun j => t * d' j) (fun j => t * v' j) ∧
      Real.exp U₀ + Real.exp U₀ * tagSeries d v ≤
        Real.exp (t * U₀') * (1 + tagSeries (fun j => t * d' j) (fun j => t * v' j)) := by
  have hT : tagSeries d v ≤ tagSeries (fun j => t * d' j) (fun j => t * v' j) :=
    tagSeries_mono hd0 hv0 hd hv
  have hT0 : 0 ≤ tagSeries d v := tagSeries_nonneg hd0 hv0
  have hP' := Real.exp_le_exp.mpr hP
  have hU' := Real.exp_le_exp.mpr hU
  have h2 : Real.exp U₀ * tagSeries d v ≤
      Real.exp (t * U₀') * tagSeries (fun j => t * d' j) (fun j => t * v' j) :=
    mul_le_mul hU' hT hT0 (Real.exp_pos _).le
  refine ⟨mul_le_mul hP' hT hT0 (Real.exp_pos _).le, h2, ?_⟩
  rw [mul_add, mul_one]
  exact add_le_add hU' h2

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] [DecidableEq P] (D : ComparisonData m₀ p pr h E)

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

end Sarkozy.TheoremC
