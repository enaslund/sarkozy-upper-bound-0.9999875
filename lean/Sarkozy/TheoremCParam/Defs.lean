module

public import Sarkozy.TheoremC.Defs
public import Sarkozy.Param.All

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion

/-! ## Measures, records and prices (`def:cp:records`, `def:price`) -/

/-! ## The cuts, the queries and the index law (CP0) -/

section Standing

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

variable (a) in
/-- The selection factor `q_𝔟^{2a}` of an atom (`def:price`): `p^{2a}` at a tail prime
`p`, the given factor `selPre` at the prefix atom. -/
noncomputable def selectionFactor (selPre : ℝ) (L : ℕ) : PaperAtom J L → ℝ
  | none => selPre
  | some j => ((p L j : ℕ) : ℝ) ^ (2 * a)

end Standing

/-! ## Robust bounds (`def:robust`) -/

variable (a) in
/-- A robust upper bound `Ξ ≤ (c + o(1)) Y` (`def:robust`), in the form of
`Sarkozy.Comparison.Criterion`: at every least normalized counterexample of every large
scale, uniformly in `C ≥ 1`, with a relative error `ε(L) → 0` and a density-linear
remainder `c' L^{-σ} α`. -/
def RobustUpper (Y Ξ : ℕ → Finset ℤ → ℝ) (c : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c' : ℝ, 0 ≤ c' ∧
    Param.AtCounterexamples (Params.ofDecay a) Y fun L A => Ξ L A ≤
        (c + ε L) * Y L A + remainder c' L A

variable (a) in
/-- A robust lower bound `Ξ ≥ (c - o(1)) Y` (`def:robust`). -/
def RobustLower (Y Ξ : ℕ → Finset ℤ → ℝ) (c : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c' : ℝ, 0 ≤ c' ∧
    Param.AtCounterexamples (Params.ofDecay a) Y fun L A =>
        (c - ε L) * Y L A - remainder c' L A ≤ Ξ L A

end Sarkozy.TheoremCParam
