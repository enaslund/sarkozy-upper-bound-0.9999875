module

public import Sarkozy.BlockAdapter.Layer
public import Sarkozy.PartVLaws.BlockRP

@[expose] public section







open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.FiveType.TwoCoord
  Sarkozy.Cuts Sarkozy.PartVLaws Sarkozy.PartVLaws.FieldGraphs

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-! ## Relabelled block graph laws -/

/-- **A vertex relabelling carries block graph laws to block graph laws.** -/
theorem blockGraphLaw_map_iso {W W' : Type} [Fintype W] [DecidableEq W] [Fintype W']
    [DecidableEq W'] (G : OrientedGraph W) (G' : OrientedGraph W') (σ : W ≃ W')
    (hσ : ∀ u w, (u, w) ∈ G.E ↔ (σ u, σ w) ∈ G'.E)
    (hne' : ∀ i, (injLabellings (ZMod (pr i)) G').Nonempty)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) :
    (blockGraphLaw pr G' hne').map (fun y => y ∘ σ) = blockGraphLaw pr G hne := by
  have hw : ∀ i (y : W' → ZMod (pr i)),
      (graphLaw G (hne i)).weight (precomp σ _ y) = (graphLaw G' (hne' i)).weight y := by
    intro i y
    have h := weight_of_expect_equiv (graphLaw G' (hne' i)) (graphLaw G (hne i))
      (precomp σ.symm (ZMod (pr i)))
      (fun Ψ => Cuts.graphLaw_iso G G' σ hσ (hne i) (hne' i) Ψ)
      (precomp σ _ y)
    have e : precomp σ.symm (ZMod (pr i)) (precomp σ _ y) = y := by
      funext w
      simp [precomp]
    rw [e] at h
    exact h.symm
  apply PartVLaws.law_eq_of_expect
  intro Ψ
  rw [FiniteLaw.expect_map]
  unfold blockGraphLaw
  rw [expect_tensor_eq_sum, expect_tensor_eq_sum]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun i => precomp σ (ZMod (pr i))) _ _ fun z => ?_
  change (∏ i, (graphLaw G' (hne' i)).weight (z i)) * Ψ ((fun v j => z j v) ∘ σ) =
    (∏ i, (graphLaw G (hne i)).weight (precomp σ _ (z i))) * Ψ (fun v j => z j (σ v))
  simp only [hw]
  rfl

variable (hne : UpperNonempty pr)

/-- **The two-layer upper block laws in the completion coordinates are block graph laws** of
`graph f₀ f₁ (ℤ/2)`. -/
theorem lam2_upperBlock (f0 f1 : FieldTy) :
    lam2 (upperBlockFieldLaws pr hne) f0 f1 =
      blockGraphLaw pr (graph f0 f1 (ZMod 2))
        (fun i => nonempty f0 f1 twoLayers (hne.two _ _ i)) :=
  blockGraphLaw_map_iso pr _ _ (verticesEquiv f0 f1 twoLayers)
    (verticesEquiv_edges f0 f1 twoLayers) _ _

/-- The one-layer upper block laws are block graph laws of `graph f₀ f₁ Unit`. -/
theorem lam1_upperBlock (f0 f1 : FieldTy) :
    lam1 (upperBlockFieldLaws pr hne) f0 f1 =
      blockGraphLaw pr (graph f0 f1 Unit)
        (fun i => nonempty f0 f1 oneLayer (hne.one _ _ i)) :=
  blockGraphLaw_map_iso pr _ _ (verticesEquiv f0 f1 oneLayer)
    (verticesEquiv_edges f0 f1 oneLayer) _ _

/-! ## The block forms at `ϑ₀` -/

section Forms

variable (f' : FieldTy) (Λ : Type) [Fintype Λ] [DecidableEq Λ]

/-- The chamber half law is the fold graph law, as a weight identity. -/
theorem chamberHalfLaw_weight {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hneL : (injLabellings F (chamberGraph f' Λ)).Nonempty)
    (hneF : (injLabellings F (FieldGraphs.foldGraph f' Λ)).Nonempty)
    (y : Fin 3 × f'.Obj × Λ → F) :
    ((chamberData f' Λ).halfLaw hneL).weight (precomp (chamberHalfEquiv f' Λ) F y) =
      (graphLaw (FieldGraphs.foldGraph f' Λ) hneF).weight y :=
  weight_of_expect_equiv _ _ (precomp (chamberHalfEquiv f' Λ) F)
    (chamberHalfLaw_expect f' Λ hneL hneF) y

variable (hL : ∀ i, (injLabellings (ZMod (pr i)) (chamberGraph f' Λ)).Nonempty)

/-- **The cut form at `ϑ₀` of the upper root rows is the tensor of the per-prime cut operators.** -/
theorem upperRootForm (φ ψ : ((chamberCut 0).Half → f'.Obj × Λ → BlockLabel pr) → ℝ) :
    (chamberCut 0).form (lawL ((blockGraphLaw pr (chamberGraph f' Λ) hL).map rows0)) φ ψ =
      kernelForm (FiniteLaw.pi fun i => (chamberData f' Λ).halfLaw (hL i))
        (FiniteLaw.pi fun i => (chamberData f' Λ).halfLaw (hL i))
        (fun x y => ∏ i, (chamberData f' Λ).cutK (x i) (y i) / (chamberData f' Λ).cutZ (hL i))
        ((φ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ))
        ((ψ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ)) := by
  change ((blockGraphLaw pr (chamberGraph f' Λ) hL).map rows0).expect _ = _
  rw [FiniteLaw.expect_map]
  exact block_cut_expect pr (chamberData f' Λ) hL (φ ∘ halfRows f' Λ) (ψ ∘ halfRows f' Λ)

/-- **The cut form at `ϑ₀` of `Π_{F₀}` of the upper fold rows is the `L²(⊗ μ_p)` norm.** -/
theorem upperFoldForm
    (hF : ∀ i, (injLabellings (ZMod (pr i)) (FieldGraphs.foldGraph f' Λ)).Nonempty)
    (φ : ((chamberCut 0).Half → f'.Obj × Λ → BlockLabel pr) → ℝ) :
    (chamberCut 0).form (lawL (patternLaw (fold 0)
        ((blockGraphLaw pr (FieldGraphs.foldGraph f' Λ) hF).map rows0))) φ φ =
      (FiniteLaw.pi fun i => (chamberData f' Λ).halfLaw (hL i)).expect
        (fun ξ => ((φ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ)) ξ *
          ((φ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ)) ξ) := by
  rw [pi_expect_equiv (fun i => (chamberData f' Λ).halfLaw (hL i))
    (fun i => graphLaw (FieldGraphs.foldGraph f' Λ) (hF i))
    (fun i => precomp (chamberHalfEquiv f' Λ) _)
    (fun i y => chamberHalfLaw_weight f' Λ (hL i) (hF i) y)]
  change (patternLaw (fold 0) ((blockGraphLaw pr (FieldGraphs.foldGraph f' Λ) hF).map
    rows0)).expect _ = _
  rw [patternLaw, FiniteLaw.expect_map, FiniteLaw.expect_map]
  unfold blockGraphLaw
  rw [expect_tensor_eq_sum]
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl fun z _ => ?_
  congr 1
  simp only [Function.comp_apply, fold0_flip]
  rfl

theorem upperRootEnv_of_cutCaps (D : Datum (f'.Obj × Λ → BlockLabel pr))
    (hF : ∀ i, (injLabellings (ZMod (pr i)) (FieldGraphs.foldGraph f' Λ)).Nonempty)
    (hpiL : D.piL = (blockGraphLaw pr (chamberGraph f' Λ) hL).map rows0)
    (hpiF : D.piF = (blockGraphLaw pr (FieldGraphs.foldGraph f' Λ) hF).map rows0)
    {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (chamberData f' Λ) (hL i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (chamberData f' Λ) (hL i) v⟫_ℝ ≤
      (1 + B / pr i) * ‖v‖ ^ 2) :
    RootEnv D (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ := by
  have hcompL : D.compL = lawL ((blockGraphLaw pr (chamberGraph f' Λ) hL).map rows0) := by
    unfold Datum.compL
    rw [hpiL]
  have hcompF : D.compF 0 = lawL (patternLaw (fold 0)
      ((blockGraphLaw pr (FieldGraphs.foldGraph f' Λ) hF).map rows0)) := by
    unfold Datum.compF
    rw [hpiF]
  constructor
  · intro φ ψ
    change (chamberCut 0).form D.compL φ ψ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) φ ψ =
      (chamberCut 0).form D.compL ψ φ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) ψ φ
    rw [form_symm_of_flip_inv (chamberCut 0) (flip_inv_of_inv6 D.compL_inv6) φ ψ,
      D.compF0_positive.symmetric φ ψ]
  · intro φ
    change 0 ≤ (chamberCut 0).form D.compL φ φ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) φ φ
    rw [hcompL, hcompF, upperRootForm pr f' Λ hL φ φ, upperFoldForm pr f' Λ hL hF φ]
    have h := UpperReference.cut_block_cap (chamberData f' Λ) pr hL hg hB hX hXb hbp hLs hgp
      hlow hup ((φ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ))
    have hn : Recentering.nrm (FiniteLaw.pi fun i => (chamberData f' Λ).halfLaw (hL i))
        ((φ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ)) ^ 2 =
        (FiniteLaw.pi fun i => (chamberData f' Λ).halfLaw (hL i)).expect
          (fun ξ => ((φ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ)) ξ *
            ((φ ∘ halfRows f' Λ) ∘ blockHalfRows pr (chamberData f' Λ)) ξ) := by
      unfold Recentering.nrm Recentering.ip
      exact Real.sq_sqrt (FiniteLaw.expect_nonneg _ fun ξ => mul_self_nonneg _)
    rw [hn] at h
    linarith

end Forms

/-! ## The upper block data -/

/-- **(V1) `root20` at an upper block from per-prime cut caps**: the root envelope of the
coordinate-`0` row datum of the two-layer laws at the field type `f'`. -/
theorem upper_root20_of_cutCaps (f' : FieldTy)
    (hRow : RowHyp0 (lam2 (upperBlockFieldLaws pr hne)) f')
    {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (chamberData f' (ZMod 2))
      (nonempty .L f' twoLayers (hne.two _ _ i)) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (chamberData f' (ZMod 2))
      (nonempty .L f' twoLayers (hne.two _ _ i)) v⟫_ℝ ≤ (1 + B / pr i) * ‖v‖ ^ 2) :
    RootEnv (rowD0 (lam2 (upperBlockFieldLaws pr hne)) f' hRow)
      (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ :=
  upperRootEnv_of_cutCaps pr f' (ZMod 2) (fun i => nonempty .L f' twoLayers (hne.two _ _ i)) _
    (fun i => nonempty .F f' twoLayers (hne.two _ _ i))
    ((rowDatum0 _ _ hRow).piL.trans
      (congrArg (fun μ => μ.map rows0) (lam2_upperBlock pr hne .L f')))
    ((rowDatum0 _ _ hRow).piF.trans
      (congrArg (fun μ => μ.map rows0) (lam2_upperBlock pr hne .F f')))
    hg hB hX hXb hbp hLs hgp hlow hup

/-- **(V1) `root10` at an upper block from per-prime cut caps** (one-layer laws). -/
theorem upper_root10_of_cutCaps (f' : FieldTy)
    (hRow : RowHyp0 (lam1 (upperBlockFieldLaws pr hne)) f')
    {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, Spectral.cutOp (chamberData f' Unit)
      (nonempty .L f' oneLayer (hne.one _ _ i)) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (chamberData f' Unit)
      (nonempty .L f' oneLayer (hne.one _ _ i)) v⟫_ℝ ≤ (1 + B / pr i) * ‖v‖ ^ 2) :
    RootEnv (rowD0 (lam1 (upperBlockFieldLaws pr hne)) f' hRow)
      (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ :=
  upperRootEnv_of_cutCaps pr f' Unit (fun i => nonempty .L f' oneLayer (hne.one _ _ i)) _
    (fun i => nonempty .F f' oneLayer (hne.one _ _ i))
    ((rowDatum0 _ _ hRow).piL.trans
      (congrArg (fun μ => μ.map rows0) (lam1_upperBlock pr hne .L f')))
    ((rowDatum0 _ _ hRow).piF.trans
      (congrArg (fun μ => μ.map rows0) (lam1_upperBlock pr hne .F f')))
    hg hB hX hXb hbp hLs hgp hlow hup

end Sarkozy.BlockAdapter
