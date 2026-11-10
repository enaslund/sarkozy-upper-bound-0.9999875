module

public import Sarkozy.PartVLaws.FieldGraphs
public import Sarkozy.Spectral.ReflectionOrder

/-!
# Chamber spectral bounds give the root envelopes of the upper reference

`lem:upper-geometry`(c) and the chamber-cut paragraph of
`lem:upper-reference-rp`(i), `paper/sections/25_upper_reference.tex`.

For every field type and layer set, the half graph of the chamber cut of
`G_{Lφ}` is `G_{Fφ}`. Its half law is therefore exactly the fold law in the
five-type datum. Grouping labels into rows carries the normalized spectral lower
bound to `RootEnv`, with no density comparison and no change of constant.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.PartVLaws.FieldGraphs

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.InfluenceGlue

theorem chamberFlip_zero (u : ZMod 6) :
    (chamberCut 0).flip u = chamberRefl 5 u := by
  revert u
  decide

theorem fold0_flip (u : ZMod 6) : fold 0 ((chamberCut 0).flip u) = fold 0 u := by
  revert u
  decide

theorem fold0_cast_of_half (u : ZMod 6) (hu : u ∈ (chamberCut 0).half) :
    ((fold 0 u).val : ZMod 6) = u := by
  revert u
  decide

theorem cast_mem_chamberHalf (i : Fin 3) : (i.val : ZMod 6) ∈ (chamberCut 0).half := by
  revert i
  decide

variable (f' : FieldTy) (Λ : Type) [Fintype Λ] [DecidableEq Λ]

/-- `G_{Lφ}` with its first object type explicitly reduced to `ZMod 6`. -/
def chamberGraph : OrientedGraph (ZMod 6 × f'.Obj × Λ) :=
  twoLayerGraph typeL (cRel f') typeL_proper (cRel_proper f') Λ

/-- `G_{Fφ}` with its first object type explicitly reduced to `Fin 3`. -/
def foldGraph : OrientedGraph (Fin 3 × f'.Obj × Λ) :=
  twoLayerGraph typeF (cRel f') typeF_proper (cRel_proper f') Λ

omit [DecidableEq Λ] in
theorem mem_chamberGraph (a b : ZMod 6 × f'.Obj × Λ) :
    (a, b) ∈ (chamberGraph f' Λ).E ↔ twoLayerEdge typeL (cRel f') a b = true :=
  mem_twoLayerGraph _ _ _ _ _

omit [DecidableEq Λ] in
theorem mem_foldGraph (a b : Fin 3 × f'.Obj × Λ) :
    (a, b) ∈ (foldGraph f' Λ).E ↔ twoLayerEdge typeF (cRel f') a b = true :=
  mem_twoLayerGraph _ _ _ _ _

/-- Spectral data for the coordinate-`0` chamber cut of `G_{Lφ}` at any layer set. -/
noncomputable def chamberData : Cuts.SpecData (ZMod 6 × f'.Obj × Λ) where
  G := chamberGraph f' Λ
  cut := (chamberCut 0).prodLeft (f'.Obj × Λ)
  aut a b := by
    rw [mem_chamberGraph, mem_chamberGraph]
    change twoLayerEdge typeL (cRel f') a b = true ↔
      twoLayerEdge typeL (cRel f')
        ((chamberCut 0).flip a.1, a.2) ((chamberCut 0).flip b.1, b.2) = true
    have h := typeL_preserves_reflection 5 (Or.inr (Or.inr rfl)) a.1 b.1
    simp only [twoLayerEdge, chamberFlip_zero, h.1, h.2]
  order := by
    classical
    simpa only [Fintype.card_coe] using
      (Fintype.equivFin ((chamberCut 0).prodLeft (f'.Obj × Λ)).Half).symm

theorem mem_chamberHalf (v : ZMod 6 × f'.Obj × Λ) :
    v ∈ (chamberData f' Λ).cut.half ↔ v.1 ∈ (chamberCut 0).half := by
  change v ∈ (chamberCut 0).half ×ˢ Finset.univ ↔ _
  simp only [Finset.mem_product, Finset.mem_univ, and_true]

/-- The plus half of `G_{Lφ}` is the vertex set of `G_{Fφ}`. -/
def chamberHalfEquiv : (chamberData f' Λ).cut.Half ≃ Fin 3 × f'.Obj × Λ where
  toFun v := (fold 0 v.1.1, v.1.2)
  invFun v := ⟨((v.1.val : ZMod 6), v.2),
    (mem_chamberHalf f' Λ _).mpr (cast_mem_chamberHalf v.1)⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext (fold0_cast_of_half v.1.1 ((mem_chamberHalf f' Λ _).mp v.2)) rfl
  right_inv v := by
    refine Prod.ext ?_ rfl
    simpa using fold_half 0 v.1

/-- The chamber half consists of three complete rows. -/
theorem chamberData_n : (chamberData f' Λ).n = 3 * (Fintype.card f'.Obj * Fintype.card Λ) := by
  have h := Fintype.card_congr (chamberHalfEquiv f' Λ)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
    Cuts.SpecData.n] using h

/-- **`lem:upper-geometry`(c)**, as a graph isomorphism at the chamber cut. -/
theorem chamberHalfEquiv_edges (a b : (chamberData f' Λ).cut.Half) :
    (a, b) ∈ (chamberData f' Λ).halfGraph.E ↔
      (chamberHalfEquiv f' Λ a, chamberHalfEquiv f' Λ b) ∈ (foldGraph f' Λ).E := by
  rw [Cuts.SpecData.mem_halfGraph]
  change (a.1, b.1) ∈ (chamberGraph f' Λ).E ↔ _
  rw [mem_chamberGraph, mem_foldGraph]
  rw [← twoLayer_restrict_first]
  simp only [chamberHalfEquiv, Equiv.coe_fn_mk,
    fold0_cast_of_half _ ((mem_chamberHalf f' Λ _).mp a.2),
    fold0_cast_of_half _ ((mem_chamberHalf f' Λ _).mp b.2)]

/-- Group a half configuration into rows indexed by the chamber half. -/
def halfRows {X : Type} (x : (chamberData f' Λ).cut.Half → X) :
    (chamberCut 0).Half → f'.Obj × Λ → X :=
  fun u v => x ⟨(u.1, v), (mem_chamberHalf f' Λ _).mpr u.2⟩

section Laws

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  (hneL : (injLabellings F (chamberGraph f' Λ)).Nonempty)
  (hneF : (injLabellings F (foldGraph f' Λ)).Nonempty)

/-- The chamber half law is exactly the fold graph law. -/
theorem chamberHalfLaw_expect (Ψ : ((chamberData f' Λ).cut.Half → F) → ℝ) :
    ((chamberData f' Λ).halfLaw hneL).expect Ψ =
      (graphLaw (foldGraph f' Λ) hneF).expect
        (fun y => Ψ (y ∘ chamberHalfEquiv f' Λ)) := by
  let e := chamberHalfEquiv f' Λ
  have hedge : ∀ a b, (a, b) ∈ (foldGraph f' Λ).E ↔
      (e.symm a, e.symm b) ∈ (chamberData f' Λ).halfGraph.E := by
    intro a b
    rw [chamberHalfEquiv_edges, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Cuts.graphLaw_iso _ _ e.symm hedge hneF
    ((chamberData f' Λ).half_nonempty hneL) Ψ

variable (D : Datum (f'.Obj × Λ → F))

/-- The root component's reflection form is the chamber cut form on row functions. -/
theorem rootForm_eq_cutForm
    (hL : D.piL = (graphLaw (chamberGraph f' Λ) hneL).map rows0)
    (φ ψ : ((chamberCut 0).Half → f'.Obj × Λ → F) → ℝ) :
    (chamberCut 0).form D.compL φ ψ =
      (chamberData f' Λ).cutForm hneL (φ ∘ halfRows f' Λ) (ψ ∘ halfRows f' Λ) := by
  change D.piL.expect _ = _
  rw [hL, FiniteLaw.expect_map,
    ← (chamberData f' Λ).expect_cut_form hneL (φ ∘ halfRows f' Λ) (ψ ∘ halfRows f' Λ)]
  rfl

/-- The aligned fold component realizes the `L²` inner product for the chamber
half graph law, including all labels inside each row. -/
theorem foldForm_eq_halfLaw
    (hF : D.piF = (graphLaw (foldGraph f' Λ) hneF).map rows0)
    (φ ψ : ((chamberCut 0).Half → f'.Obj × Λ → F) → ℝ) :
    (chamberCut 0).form (D.compF 0) φ ψ =
      ((chamberData f' Λ).halfLaw hneL).expect
        (fun x => φ (halfRows f' Λ x) * ψ (halfRows f' Λ x)) := by
  change (patternLaw (fold 0) D.piF).expect _ = _
  rw [patternLaw, FiniteLaw.expect_map, hF, FiniteLaw.expect_map,
    chamberHalfLaw_expect f' Λ hneL hneF]
  apply FiniteLaw.expect_congr
  intro y
  change φ (fun u v => y (fold 0 u.1, v)) *
    ψ (fun u v => y (fold 0 ((chamberCut 0).flip u.1), v)) = _
  simp only [fold0_flip]
  rfl

/-- **The root-envelope bridge** (`it:upper-valid-root`). The fold normalization
is discharged by the graph isomorphism, for an arbitrary layer set. -/
theorem rootEnv_of_cutOp
    (hL : D.piL = (graphLaw (chamberGraph f' Λ) hneL).map rows0)
    (hF : D.piF = (graphLaw (foldGraph f' Λ) hneF).map rows0)
    (d r : ℝ)
    (h : ∀ v : EuclideanSpace ℝ ((chamberData f' Λ).cut.Half → F),
      -(d * r) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (chamberData f' Λ) hneL v⟫_ℝ) :
    RootEnv D d r := by
  constructor
  · intro φ ψ
    change (chamberCut 0).form D.compL φ ψ -
        -(d * r) * (chamberCut 0).form (D.compF 0) φ ψ =
      (chamberCut 0).form D.compL ψ φ -
        -(d * r) * (chamberCut 0).form (D.compF 0) ψ φ
    simp only [rootForm_eq_cutForm f' Λ hneL D hL,
      foldForm_eq_halfLaw f' Λ hneL hneF D hF]
    rw [(chamberData f' Λ).cutForm_symm hneL (φ ∘ halfRows f' Λ) (ψ ∘ halfRows f' Λ)]
    congr 2
    exact FiniteLaw.expect_congr _ fun x => mul_comm _ _
  · intro φ
    change 0 ≤ (chamberCut 0).form D.compL φ φ -
      -(d * r) * (chamberCut 0).form (D.compF 0) φ φ
    rw [rootForm_eq_cutForm f' Λ hneL D hL, foldForm_eq_halfLaw f' Λ hneL hneF D hF]
    have hφ := h (l2Map ((chamberData f' Λ).halfLaw hneL) (φ ∘ halfRows f' Λ))
    rw [norm_l2Map_sq, (Spectral.cutOp_form (chamberData f' Λ) hneL _ _).1] at hφ
    exact sub_nonneg.mpr (by simpa only [Function.comp_apply, pow_two] using hφ)

end Laws

omit [Fintype Λ] [DecidableEq Λ] in
/-- **The two-layer root-envelope bridge for the actual tail law**, at either
prime class and every field type. The datum hypothesis only supplies the row
datum; no additional comparison of its fold law is assumed. -/
theorem tail_rootEnv_two (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)
    (hRow : RowHyp0 (lam2 (tailFieldLaws p hne)) f') (d r : ℝ)
    (h : ∀ v : EuclideanSpace ℝ ((chamberData f' (ZMod 2)).cut.Half → ZMod p),
      -(d * r) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (chamberData f' (ZMod 2))
        (nonempty .L f' twoLayers (hne.two _ _)) v⟫_ℝ) :
    RootEnv (rowD0 (lam2 (tailFieldLaws p hne)) f' hRow) d r := by
  apply rootEnv_of_cutOp f' (ZMod 2) (nonempty .L f' twoLayers (hne.two _ _))
    (nonempty .F f' twoLayers (hne.two _ _)) _ ?_ ?_ d r h
  · exact (rowDatum0 _ _ hRow).piL.trans
      (congrArg (fun μ => μ.map rows0) (lam2_eq_graphLaw p hne .L f'))
  · exact (rowDatum0 _ _ hRow).piF.trans
      (congrArg (fun μ => μ.map rows0) (lam2_eq_graphLaw p hne .F f'))

omit [Fintype Λ] [DecidableEq Λ] in
/-- **The one-layer root-envelope bridge for the actual tail law.** -/
theorem tail_rootEnv_one (p : ℕ) [Fact p.Prime] (hne : TailNonempty p)
    (hRow : RowHyp0 (lam1 (tailFieldLaws p hne)) f') (d r : ℝ)
    (h : ∀ v : EuclideanSpace ℝ ((chamberData f' Unit).cut.Half → ZMod p),
      -(d * r) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (chamberData f' Unit)
        (nonempty .L f' oneLayer (hne.one _ _)) v⟫_ℝ) :
    RootEnv (rowD0 (lam1 (tailFieldLaws p hne)) f' hRow) d r := by
  apply rootEnv_of_cutOp f' Unit (nonempty .L f' oneLayer (hne.one _ _))
    (nonempty .F f' oneLayer (hne.one _ _)) _ ?_ ?_ d r h
  · exact (rowDatum0 _ _ hRow).piL.trans
      (congrArg (fun μ => μ.map rows0) (lam1_eq_graphLaw p hne .L f'))
  · exact (rowDatum0 _ _ hRow).piF.trans
      (congrArg (fun μ => μ.map rows0) (lam1_eq_graphLaw p hne .F f'))

end Sarkozy.PartVLaws.FieldGraphs
