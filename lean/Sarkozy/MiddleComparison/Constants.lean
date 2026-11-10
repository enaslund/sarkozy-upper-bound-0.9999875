module

public import Sarkozy.MiddleComparison.Block

@[expose] public section

/-!
# The accepting constant replacements of a middle block (`lem:record:accepting-c2`)

`paper/sections/21_middle_records.tex`, `lem:record:accepting-c2` and its proof: "Write `(a_p, b_p)`
for the labels of the single object of either constant record in layers `0` and `1` at the prime
`p` … All six queries read `a_p → b_p`. Replace this law by the uniform strict Paley edge,
independently at every prime. It is square-affine invariant, accepts all six queries …".

* `layerEdgeGraph`: the graph on the two layers `{0, 1}` with the one edge `0 → 1`;
  `layerEdge_nonempty`: it has injective strict-square labellings at every prime (`(0, 1)`);
* **`constRec`**: the uniform strict Paley edge `λ_𝔅(0 → 1)` at every prime of the block, read by
  the slot `(u₀, u₁, ℓ)` at its layer `ℓ` (the constant pattern reads one object in both layers);
* `constRec_accepts` (every query reads the edge `0 → 1`), `constRec_uniform`.

The norms of `constRec - Π_{C_k}` (`r²/(1 - 1/b)²` and `r/(1 - 1/b)` in the paper) are not proved
here; W6's `accepting_c2_prices` turns them into the prices.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.Labellings

/-- The graph on the two layers with the single edge `0 → 1`. -/
def layerEdgeGraph : OrientedGraph (Fin 2) where
  E := {((0 : Fin 2), (1 : Fin 2))}
  loopless u := by revert u; decide
  oriented u v := by revert u v; decide

/-- The slot `(u₀, u₁, ℓ)` reads the label of the layer `ℓ`. -/
def layerEmission (v : Slot) : Fin 2 := layerFin v.2.2

theorem layerEdge_query (j : Chamber) :
    (layerEmission (querySource j), layerEmission (queryTarget j)) ∈ layerEdgeGraph.E := by
  revert j
  decide

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr)

omit [Fintype ι] [DecidableEq ι] in
/-- The strict Paley edge has labellings at every prime: `(0, 1)`. -/
theorem layerEdge_nonempty : ∀ i, (injLabellings (ZMod (pr i)) layerEdgeGraph).Nonempty := by
  intro i
  refine ⟨fun w => (w.val : ZMod (pr i)), ?_⟩
  rw [mem_injLabellings_iff_feasible]
  have h01 : ((0 : Fin 2).val : ZMod (pr i)) ≠ ((1 : Fin 2).val : ZMod (pr i)) := by
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
    exact zero_ne_one
  refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
  · fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab h01
    · exact absurd hab.symm h01
    · rfl
  · have he' : e = ((0 : Fin 2), (1 : Fin 2)) := Finset.mem_singleton.mp he
    subst he'
    change quadraticChar (ZMod (pr i)) (((1 : Fin 2).val : ZMod (pr i)) -
      ((0 : Fin 2).val : ZMod (pr i))) = 1
    rw [show (((1 : Fin 2).val : ZMod (pr i)) - ((0 : Fin 2).val : ZMod (pr i))) = 1 by simp]
    exact map_one _

/-- **The accepting constant replacement** (`lem:record:accepting-c2`): the uniform strict Paley
edge between the two layers, independently at every prime of the block. -/
noncomputable def constRec : FiniteLaw (Slot → BlockLabel pr) :=
  emit (blockGraphLaw pr layerEdgeGraph (layerEdge_nonempty pr)) layerEmission

/-- **The constant replacement accepts the six queries** (every query reads the edge `0 → 1`). -/
theorem constRec_accepts (z : Slot → BlockLabel pr) (hz : (constRec pr).weight z ≠ 0)
    (e : Chamber) :
    blockSquareAccepted pr (z (MainAnchor.paperQueries.source e))
      (z (MainAnchor.paperQueries.target e)) := by
  rw [paperQueries_source_eq, paperQueries_target_eq]
  exact blockSquareAccepted_of pr fun i =>
    emit_edge_accepts pr _ _ (blockGraphLaw_supported pr _ _) _ layerEdge_query hz e i

/-- **The constant replacement has uniform one-slot marginals.** -/
theorem constRec_uniform : HasUniformMarginals (constRec pr) :=
  emit_uniform _ _ fun o g => blockGraphLaw_vertex_uniform pr _ (layerEdge_nonempty pr) o g

end Block

end Sarkozy.MiddleComparison
