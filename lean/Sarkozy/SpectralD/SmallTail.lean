module

public import Sarkozy.SpectralD.SmallFiniteTests
public import Sarkozy.SpectralD.SmallModelBounds
public import Sarkozy.SpectralD.SmallTailCriterionTight

/-!
# The nine smaller spectral bounds at tail primes

Every analytic and finite numerical input is discharged. The resulting
bounds use the paper's constants, uniformly for all primes at least 2^512.
-/

@[expose] public section

namespace Sarkozy.SpectralD.SmallMatrices

open Sarkozy.PartVLaws.FieldGraphs Sarkozy.Labellings Sarkozy.SpectralC
open scoped InnerProductSpace

variable {p : ℕ} [Fact p.Prime]

theorem tail_bound (c : SmallCut) (hW : Target.Weil) (hMR : Target.MovingRoot)
    (h4 : Extraction.FourCycleBound p) (hp : 2 ^ 512 ≤ p)
    (hne : (injLabellings (ZMod p) c.data.G).Nonempty)
    (v : EuclideanSpace ℝ (c.data.cut.Half → ZMod p)) :
    -((cap c : ℝ) * rp p) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp c.data hne v⟫_ℝ := by
  classical
  let : LinearOrder c.data.cut.Half := LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  exact AtMost.tail_criterion_tight c.data (FiniteModel.Adj c.edge c.data.cut)
    (FiniteModel.Adj_contains c.data c.edge (SmallCut.mem_edge c)) hW hMR h4 hp hne
    ((SmallCut.card_vertex c).trans (by norm_num)) (SmallCut.card_half c)
    (SmallCut.cross_pairs c) (SmallCut.degree c)
    (fun j => (SmallCut.half_degree c j).trans (by norm_num))
    (fun j => (SmallCut.cross_degree c j).trans (by norm_num)) (graph_error c hp)
    (rho_bound c) (model_upper c (by omega)) (plus_upper c (by omega)) (deltaE_bound c)
    (step_pos c) (finiteTest c (by omega)) (step_cap c) v

end Sarkozy.SpectralD.SmallMatrices
