module

public import Sarkozy.PartVLaws.UpperGraphs
public import Sarkozy.PartVLaws.TailCounts
public import Sarkozy.Cuts.CutTransport

/-!
# The upper field graphs in the completion laws' coordinates

The graphs of `lem:upper-geometry`, with `FieldTy` objects and an arbitrary layer
type. The reindexing results identify their graph laws exactly with `lamOf`, hence
with the tail's `lam2` and `lam1`. These are equalities of probability laws, with no
count estimates or density losses.
-/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType.TwoCoord

theorem cRel_proper (f : FieldTy) : (cRel f).Proper := by
  cases f
  · exact typeL_proper
  · exact typeF_proper
  · exact typeE_proper

/-- `G_{φ₀φ₁}` on the object types used by the completion laws. -/
def graph (f0 f1 : FieldTy) (Λ : Type) [Fintype Λ] :
    OrientedGraph (f0.Obj × f1.Obj × Λ) :=
  twoLayerGraph (cRel f0) (cRel f1) (cRel_proper f0) (cRel_proper f1) Λ

theorem mem_graph (f0 f1 : FieldTy) {Λ : Type} [Fintype Λ]
    (a b : f0.Obj × f1.Obj × Λ) :
    (a, b) ∈ (graph f0 f1 Λ).E ↔ twoLayerEdge (cRel f0) (cRel f1) a b = true :=
  mem_twoLayerGraph _ _ _ _ _

/-- The identity on field objects, with a chosen reindexing of the layers. -/
def verticesEquiv (f0 f1 : FieldTy) {Λ Λ' : Type} (e : Λ ≃ Λ') :
    f0.Obj × f1.Obj × Λ ≃ (toFType f0).Obj × (toFType f1).Obj × Λ' where
  toFun v := (objCast f0 v.1, objCast f1 v.2.1, e v.2.2)
  invFun v := (objUncast f0 v.1, objUncast f1 v.2.1, e.symm v.2.2)
  left_inv v := by
    rcases v with ⟨a, b, l⟩
    simp only [objUncast_objCast, e.symm_apply_apply]
  right_inv v := by
    rcases v with ⟨a, b, l⟩
    simp only [objCast_objUncast, e.apply_symm_apply]

theorem verticesEquiv_edges (f0 f1 : FieldTy) {Λ Λ' : Type}
    [Fintype Λ] [Fintype Λ'] (e : Λ ≃ Λ') (a b : f0.Obj × f1.Obj × Λ) :
    (a, b) ∈ (graph f0 f1 Λ).E ↔
      (verticesEquiv f0 f1 e a, verticesEquiv f0 f1 e b) ∈
        (fieldGraph (toFType f0) (toFType f1) Λ').E := by
  rw [mem_graph, fieldGraph, mem_twoLayerGraph]
  cases f0 <;> cases f1 <;> rfl

section Laws

variable {F Λ Λ' : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype Λ] [DecidableEq Λ] [Fintype Λ'] [DecidableEq Λ']

/-- Relabelling layers and field objects preserves nonemptiness. -/
theorem nonempty (f0 f1 : FieldTy) (e : Λ ≃ Λ')
    (hne : (injLabellings F (fieldGraph (toFType f0) (toFType f1) Λ')).Nonempty) :
    (injLabellings F (graph f0 f1 Λ)).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  refine ⟨y ∘ verticesEquiv f0 f1 e, ?_⟩
  rw [Cuts.inj_iso _ _ (verticesEquiv f0 f1 e) (verticesEquiv_edges f0 f1 e)]
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hy

/-- The graph law after reindexing is exactly the completion law `lamOf`. -/
theorem lamOf_eq_graphLaw
    (hne : ∀ f0 f1, (injLabellings F (fieldGraph f0 f1 Λ')).Nonempty)
    (e : Λ ≃ Λ') (f0 f1 : FieldTy) :
    lamOf (fun f0 f1 => graphLaw _ (hne f0 f1)) e f0 f1 =
      graphLaw (graph f0 f1 Λ) (nonempty f0 f1 e (hne _ _)) := by
  apply law_eq_of_expect
  intro Ψ
  rw [lamOf, FiniteLaw.expect_map]
  let σ := verticesEquiv f0 f1 e
  have hedge : ∀ a b, (a, b) ∈ (fieldGraph (toFType f0) (toFType f1) Λ').E ↔
      (σ.symm a, σ.symm b) ∈ (graph f0 f1 Λ).E := by
    intro a b
    rw [verticesEquiv_edges f0 f1 e, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (Cuts.graphLaw_iso _ _ σ.symm hedge (hne _ _)
    (nonempty f0 f1 e (hne _ _)) Ψ).symm

end Laws

/-- The two representations of the pair of layers. -/
def twoLayers : ZMod 2 ≃ Fin 2 where
  toFun := layerFin
  invFun := layerUn
  left_inv := layerUn_layerFin
  right_inv := layerFin_layerUn

/-- The two representations of the single layer. -/
def oneLayer : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv l := (Fin.fin_one_eq_zero l).symm

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)

theorem lam2_eq_graphLaw (f0 f1 : FieldTy) :
    lam2 (tailFieldLaws p hne) f0 f1 =
      graphLaw (graph f0 f1 (ZMod 2)) (nonempty f0 f1 twoLayers (hne.two _ _)) :=
  lamOf_eq_graphLaw hne.two twoLayers f0 f1

theorem lam1_eq_graphLaw (f0 f1 : FieldTy) :
    lam1 (tailFieldLaws p hne) f0 f1 =
      graphLaw (graph f0 f1 Unit) (nonempty f0 f1 oneLayer (hne.one _ _)) :=
  lamOf_eq_graphLaw hne.one oneLayer f0 f1

end Sarkozy.PartVLaws.FieldGraphs
