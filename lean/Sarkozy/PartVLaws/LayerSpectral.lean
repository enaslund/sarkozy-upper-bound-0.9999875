module

public import Sarkozy.PartVLaws.FieldGraphs
public import Sarkozy.Spectral.ReflectionOrder

/-!
# Layer spectral bounds give the upper reference's layer caps

`lem:upper-geometry`(c) and the reserved-cut paragraph of
`lem:upper-reference-rp`(i) in `paper/sections/25_upper_reference.tex`.

`layerData` supplies spectral data for every field pair. Its half graph is exactly
the one-layer graph, after the explicit equivalence `layerHalfEquiv`. Thus the
duplicated half law is `Diag_ι(λ⁽¹⁾)`, and a lower bound for the normalized cut
operator implies (V3) with the very same constant. This includes all nonroot
layer cuts, at either prime class.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.PartVLaws.FieldGraphs

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord

theorem mem_layerHalf (f0 f1 : FieldTy) (v : f0.Obj × f1.Obj × ZMod 2) :
    v ∈ (Reserved.fieldCut f0.Obj f1.Obj).half ↔ v.2.2 = 0 := by
  simp only [Reserved.fieldCut, ReflectionCut.prodRight, layerCut,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_singleton]

/-- Spectral data for the layer cut of any two-layer field graph. The deletion
order is an enumeration of the half; the cut operator does not use this order. -/
noncomputable def layerData (f0 f1 : FieldTy) :
    Cuts.SpecData (f0.Obj × f1.Obj × ZMod 2) where
  G := graph f0 f1 (ZMod 2)
  cut := Reserved.fieldCut f0.Obj f1.Obj
  aut a b := by rw [mem_graph, mem_graph]; rfl
  order := by
    classical
    simpa only [Fintype.card_coe] using
      (Fintype.equivFin (Reserved.fieldCut f0.Obj f1.Obj).Half).symm

/-- The plus half of the layer cut is the vertex set of the one-layer graph. -/
def layerHalfEquiv (f0 f1 : FieldTy) :
    (layerData f0 f1).cut.Half ≃ f0.Obj × f1.Obj × Unit where
  toFun v := (v.1.1, v.1.2.1, ())
  invFun v := ⟨(v.1, v.2.1, 0), (mem_layerHalf f0 f1 _).mpr rfl⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext rfl ((mem_layerHalf f0 f1 _).mp v.2).symm)
  right_inv _ := rfl

/-- The layer half has one vertex for each pair of field objects. -/
theorem layerData_n (f0 f1 : FieldTy) :
    (layerData f0 f1).n = Fintype.card f0.Obj * Fintype.card f1.Obj := by
  have h := Fintype.card_congr (layerHalfEquiv f0 f1)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_unit, mul_one,
    Cuts.SpecData.n] using h

/-- **`lem:upper-geometry`(c)**, as a graph isomorphism at the layer cut. -/
theorem layerHalfEquiv_edges (f0 f1 : FieldTy) (a b : (layerData f0 f1).cut.Half) :
    (a, b) ∈ (layerData f0 f1).halfGraph.E ↔
      (layerHalfEquiv f0 f1 a, layerHalfEquiv f0 f1 b) ∈ (graph f0 f1 Unit).E := by
  rw [Cuts.SpecData.mem_halfGraph]
  change (a.1, b.1) ∈ (graph f0 f1 (ZMod 2)).E ↔ _
  rw [mem_graph, mem_graph]
  rfl

section Laws

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  (f0 f1 : FieldTy)
  (hne2 : (injLabellings F (graph f0 f1 (ZMod 2))).Nonempty)
  (hne1 : (injLabellings F (graph f0 f1 Unit)).Nonempty)

/-- The layer half law is precisely the one-layer graph law, with its vertices
reindexed by `layerHalfEquiv`. -/
theorem layerHalfLaw_expect (Ψ : ((layerData f0 f1).cut.Half → F) → ℝ) :
    ((layerData f0 f1).halfLaw hne2).expect Ψ =
      (graphLaw (graph f0 f1 Unit) hne1).expect
        (fun y => Ψ (y ∘ layerHalfEquiv f0 f1)) := by
  let e := layerHalfEquiv f0 f1
  have hedge : ∀ a b, (a, b) ∈ (graph f0 f1 Unit).E ↔
      (e.symm a, e.symm b) ∈ (layerData f0 f1).halfGraph.E := by
    intro a b
    rw [layerHalfEquiv_edges, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Cuts.graphLaw_iso _ _ e.symm hedge hne1
    ((layerData f0 f1).half_nonempty hne2) Ψ

/-- Duplicating the half graph law gives the paper's one-layer diagonal law. -/
theorem layer_diagonalHalf :
    (layerData f0 f1).cut.diagonalHalf ((layerData f0 f1).halfLaw hne2) =
      pushFunctional (lawL (graphLaw (graph f0 f1 Unit) hne1)) Reserved.diagF := by
  refine LinearMap.ext fun Ψ => ?_
  change ((layerData f0 f1).halfLaw hne2).expect
      (fun x => Ψ ((layerData f0 f1).cut.join x x)) = _
  rw [layerHalfLaw_expect f0 f1 hne2 hne1]
  apply FiniteLaw.expect_congr
  intro y
  congr 1
  funext v
  simp only [ReflectionCut.join]
  split <;> rfl

/-- A normalized layer-cut bound gives the inequality of graph laws in (V3). -/
theorem layer_below (a : ℝ)
    (h : ∀ v : EuclideanSpace ℝ ((layerData f0 f1).cut.Half → F),
      -a * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (layerData f0 f1) hne2 v⟫_ℝ) :
    (Reserved.fieldCut f0.Obj f1.Obj).Below
      (-a • pushFunctional (lawL (graphLaw (graph f0 f1 Unit) hne1)) Reserved.diagF)
      (lawL (graphLaw (graph f0 f1 (ZMod 2)) hne2)) := by
  have hb := Spectral.cutOp_below (layerData f0 f1) hne2 a h
  rwa [layer_diagonalHalf f0 f1 hne2 hne1] at hb

end Laws

/-- **The layer-cap bridge for the actual tail laws** (`it:upper-valid-layer`).
Every input is a spectral lower bound on the actual field graph. -/
theorem tail_layerCap (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)
    (f0 f1 : FieldTy) (a : ℝ)
    (h : ∀ v : EuclideanSpace ℝ ((layerData f0 f1).cut.Half → ZMod p),
      -a * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (layerData f0 f1)
        (nonempty f0 f1 twoLayers (hne.two _ _)) v⟫_ℝ) :
    (Reserved.fieldCut f0.Obj f1.Obj).Below
      (-a • pushFunctional (lawL (lam1 (tailFieldLaws p hne) f0 f1)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws p hne) f0 f1)) := by
  rw [lam1_eq_graphLaw, lam2_eq_graphLaw]
  exact layer_below f0 f1 _ _ a h

end Sarkozy.PartVLaws.FieldGraphs
