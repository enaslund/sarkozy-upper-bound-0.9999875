module

public import Sarkozy.BlockAdapter.Layer

@[expose] public section

/-!
# The block adapter for the upper layer caps (`lem:upper-reference-rp`(ii), (V3))

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`(d), (V3);
`lem:upper-geometry`; `lem:spec:cutkernel`(e); `lem:spec:tensorcomp`(b),(c), `lem:majorant`(c).

The two-coordinate analogue of `Layer.lean`: for objects `O₀ × O₁`, a two-layer graph `G₂` on
`O₀ × O₁ × Fin 2` invariant under the layer swap, its one-layer restriction `G₁` and patterns
`φ₀, φ₁`, the upper component `emit λ₂ (upEmission φ₀ φ₁)` is bounded below at `ι` by
`-d b^{-1/2}` times its diagonal copy, from per-prime cut caps of the layer swap
(**`upLayerCap_of_cutCaps`**).
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts

variable (O₀ O₁ : Type) [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]

/-- The layer swap of `O₀ × O₁ × Fin 2`. -/
def upCut : ReflectionCut (O₀ × O₁ × Fin 2) := (finCut.prodRight O₁).prodRight O₀

/-- A two-coordinate two-layer graph is invariant under the layer swap. -/
def UpSwapInvariant (G : OrientedGraph (O₀ × O₁ × Fin 2)) : Prop :=
  ∀ u w, (u, w) ∈ G.E ↔ ((u.1, u.2.1, 1 - u.2.2), (w.1, w.2.1, 1 - w.2.2)) ∈ G.E

/-- **The spectral data of the reserved cut** of a two-coordinate two-layer graph. -/
noncomputable def upLayerData (G : OrientedGraph (O₀ × O₁ × Fin 2)) (hG : UpSwapInvariant O₀ O₁ G) :
    SpecData (O₀ × O₁ × Fin 2) where
  G := G
  cut := upCut O₀ O₁
  aut u w := hG u w
  order := by
    classical
    simpa only [Fintype.card_coe] using (Fintype.equivFin (upCut O₀ O₁).Half).symm

theorem mem_upHalf (v : O₀ × O₁ × Fin 2) : v ∈ (upCut O₀ O₁).half ↔ v.2.2 = 0 := by
  change v ∈ (Finset.univ : Finset O₀) ×ˢ ((Finset.univ : Finset O₁) ×ˢ ({0} : Finset (Fin 2))) ↔ _
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_singleton, true_and]

section Graph

variable (G₂ : OrientedGraph (O₀ × O₁ × Fin 2)) (hG : UpSwapInvariant O₀ O₁ G₂)
  (G₁ : OrientedGraph (O₀ × O₁ × Fin 1))

/-- The plus half of the layer swap is `O₀ × O₁ × {0}`. -/
def upHalfEquiv : (upLayerData O₀ O₁ G₂ hG).cut.Half ≃ O₀ × O₁ × Fin 1 where
  toFun v := (v.1.1, v.1.2.1, 0)
  invFun v := ⟨(v.1, v.2.1, 0), (mem_upHalf O₀ O₁ _).mpr rfl⟩
  left_inv v := Subtype.ext (Prod.ext rfl (Prod.ext rfl ((mem_upHalf O₀ O₁ _).mp v.2).symm))
  right_inv _ := Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))

/-- `G₁` is the layer-`0` restriction of `G₂`. -/
def UpLayerRestricts : Prop :=
  ∀ (a a' : O₀) (b b' : O₁), ((a, b, 0), (a', b', 0)) ∈ G₂.E ↔ ((a, b, 0), (a', b', 0)) ∈ G₁.E

theorem upHalfEquiv_edges (hres : UpLayerRestricts O₀ O₁ G₂ G₁)
    (x y : (upLayerData O₀ O₁ G₂ hG).cut.Half) :
    (x, y) ∈ (upLayerData O₀ O₁ G₂ hG).halfGraph.E ↔
      (upHalfEquiv O₀ O₁ G₂ hG x, upHalfEquiv O₀ O₁ G₂ hG y) ∈ G₁.E := by
  rw [SpecData.mem_halfGraph]
  obtain ⟨⟨a, b, l⟩, hx⟩ := x
  obtain ⟨⟨a', b', l'⟩, hy⟩ := y
  have hl : l = 0 := (mem_upHalf O₀ O₁ _).mp hx
  have hl' : l' = 0 := (mem_upHalf O₀ O₁ _).mp hy
  subst hl hl'
  exact hres a a' b b'

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem upHalfLaw_expect (hres : UpLayerRestricts O₀ O₁ G₂ G₁)
    (hne₂ : (injLabellings F G₂).Nonempty) (hne₁ : (injLabellings F G₁).Nonempty)
    (Ψ : ((upLayerData O₀ O₁ G₂ hG).cut.Half → F) → ℝ) :
    ((upLayerData O₀ O₁ G₂ hG).halfLaw hne₂).expect Ψ =
      (graphLaw G₁ hne₁).expect (fun y => Ψ (y ∘ upHalfEquiv O₀ O₁ G₂ hG)) := by
  let e := upHalfEquiv O₀ O₁ G₂ hG
  have hedge : ∀ a b, (a, b) ∈ G₁.E ↔
      (e.symm a, e.symm b) ∈ (upLayerData O₀ O₁ G₂ hG).halfGraph.E := by
    intro a b
    rw [upHalfEquiv_edges O₀ O₁ G₂ hG G₁ hres, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Cuts.graphLaw_iso _ _ e.symm hedge hne₁ ((upLayerData O₀ O₁ G₂ hG).half_nonempty hne₂) Ψ

theorem upHalfLaw_weight (hres : UpLayerRestricts O₀ O₁ G₂ G₁)
    (hne₂ : (injLabellings F G₂).Nonempty) (hne₁ : (injLabellings F G₁).Nonempty)
    (y : O₀ × O₁ × Fin 1 → F) :
    ((upLayerData O₀ O₁ G₂ hG).halfLaw hne₂).weight (precomp (upHalfEquiv O₀ O₁ G₂ hG) F y) =
      (graphLaw G₁ hne₁).weight y :=
  weight_of_expect_equiv _ _ (precomp (upHalfEquiv O₀ O₁ G₂ hG) F)
    (upHalfLaw_expect O₀ O₁ G₂ hG G₁ hres hne₂ hne₁) y

end Graph

/-- The slots of the plus half of `ι` read the layer-`0` labels of the objects
`(φ₀(u₀), φ₁(u₁))`. -/
def upSlotRows {X : Type} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁)
    (x : (upCut O₀ O₁).Half → X) : reservedCut.Half → X :=
  fun v => x ⟨(φ₀ v.1.1, φ₁ v.1.2.1, 0), (mem_upHalf O₀ O₁ _).mpr rfl⟩

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The cut form at `ι` of an upper two-layer component** `emit λ (upEmission φ₀ φ₁)`. -/
theorem reservedForm_up_two (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (φ₀ : ZMod 6 → O₀)
    (φ₁ : ZMod 6 → O₁) (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (upEmission φ₀ φ₁)).weight) F G =
      lam.expect (fun y => F (upSlotRows O₀ O₁ φ₀ φ₁ (fun h => y h.1)) *
        G (upSlotRows O₀ O₁ φ₀ φ₁ (fun h => y ((upCut O₀ O₁).flip h.1)))) := by
  change (emit lam (upEmission φ₀ φ₁)).expect _ = _
  rw [expect_emit]
  refine lam.expect_congr fun y => ?_
  have h1 : (fun v : reservedCut.Half => (y ∘ upEmission φ₀ φ₁) v.1) =
      upSlotRows O₀ O₁ φ₀ φ₁ (fun h => y h.1) := by
    funext v
    have hv := reserved_half_layer v
    simp only [Function.comp_apply, upEmission, upSlotRows, hv]
    rfl
  have h2 : (fun v : reservedCut.Half => (y ∘ upEmission φ₀ φ₁) (reservedCut.flip v.1)) =
      upSlotRows O₀ O₁ φ₀ φ₁ (fun h => y ((upCut O₀ O₁).flip h.1)) := by
    funext v
    have hv := reserved_half_layer v
    obtain ⟨⟨u₀, u₁, l⟩, hmem⟩ := v
    change l = 0 at hv
    subst hv
    change y (φ₀ u₀, φ₁ u₁, layerFin (layerCut.flip 0)) = y (φ₀ u₀, φ₁ u₁, finCut.flip 0)
    rw [layerFin_flip_zero]
  rw [h1, h2]

/-- **The cut form at `ι` of an upper diagonal copy**: the mean of `Φ²`. -/
theorem reservedForm_up_diag (lam : FiniteLaw (O₀ × O₁ × Fin 1 → X)) (φ₀ : ZMod 6 → O₀)
    (φ₁ : ZMod 6 → O₁) (F : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (upDiagEmission φ₀ φ₁)).weight) F F =
      lam.expect (fun y => F (fun v => y (φ₀ v.1.1, φ₁ v.1.2.1, 0)) *
        F (fun v => y (φ₀ v.1.1, φ₁ v.1.2.1, 0))) := by
  change (emit lam (upDiagEmission φ₀ φ₁)).expect _ = _
  rw [expect_emit]
  rfl

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (G₂ : OrientedGraph (O₀ × O₁ × Fin 2)) (hG : UpSwapInvariant O₀ O₁ G₂)
  (G₁ : OrientedGraph (O₀ × O₁ × Fin 1))

/-- **The upper layer cap from per-prime cut caps** (`lem:upper-reference-rp`(ii), (V3), at a
block): for the block laws `λ_𝔅(G₂)`, `λ_𝔅(G₁)` and patterns `φ₀, φ₁`,
`Π_φ ⪰_ι -g e^{BL/(X log X)} b^{-1/2} Diag_ι(Π⁽¹⁾_φ)` from the per-prime bounds
`-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` of the layer swap of `G₂`. -/
theorem upLayerCap_of_cutCaps (hres : UpLayerRestricts O₀ O₁ G₂ G₁)
    (hL : ∀ i, (injLabellings (ZMod (pr i)) G₂).Nonempty)
    (h₁ : ∀ i, (injLabellings (ZMod (pr i)) G₁).Nonempty) (φ₀ : ZMod 6 → O₀)
    (φ₁ : ZMod 6 → O₁) {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (upLayerData O₀ O₁ G₂ hG) (hL i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (upLayerData O₀ O₁ G₂ hG) (hL i) v⟫_ℝ ≤
      (1 + B / pr i) * ‖v‖ ^ 2) :
    reservedCut.Below
      (-(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) •
        signedIntegral (emit (blockGraphLaw pr G₁ h₁) (upDiagEmission φ₀ φ₁)).weight)
      (signedIntegral (emit (blockGraphLaw pr G₂ hL) (upEmission φ₀ φ₁)).weight) := by
  set D := upLayerData O₀ O₁ G₂ hG
  set μ := FiniteLaw.pi fun i => D.halfLaw (hL i)
  set K := fun x y : (∀ i, D.cut.Half → ZMod (pr i)) =>
    ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i)
  have htwo : ∀ F G : (reservedCut.Half → BlockLabel pr) → ℝ,
      reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
        (upEmission φ₀ φ₁)).weight) F G =
        kernelForm μ μ K ((F ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D)
          ((G ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D) := by
    intro F G
    rw [reservedForm_up_two]
    exact block_cut_expect pr D hL (F ∘ upSlotRows O₀ O₁ φ₀ φ₁) (G ∘ upSlotRows O₀ O₁ φ₀ φ₁)
  have hdiagPos := emit_positive (blockGraphLaw pr G₁ h₁) (upDiagEmission φ₀ φ₁) reservedCut
    (upDiagEmission_reserved φ₀ φ₁)
  have hK : ∀ x y, K y x = K x y := by
    intro x y
    simp only [K]
    exact Finset.prod_congr rfl fun i _ => by rw [D.cutK_symm]
  constructor
  · intro F G
    change reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (upEmission φ₀ φ₁)).weight) F G -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (upDiagEmission φ₀ φ₁)).weight) F G =
      reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (upEmission φ₀ φ₁)).weight) G F -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (upDiagEmission φ₀ φ₁)).weight) G F
    rw [htwo, htwo, kernelForm_symm μ K hK, hdiagPos.symmetric F G]
  · intro F
    change 0 ≤ reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (upEmission φ₀ φ₁)).weight) F F -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (upDiagEmission φ₀ φ₁)).weight) F F
    have hdiag : reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
        (upDiagEmission φ₀ φ₁)).weight) F F =
        μ.expect (fun ξ => ((F ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D) ξ *
          ((F ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D) ξ) := by
      rw [reservedForm_up_diag, pi_expect_equiv (fun i => D.halfLaw (hL i))
        (fun i => graphLaw G₁ (h₁ i)) (fun i => precomp (upHalfEquiv O₀ O₁ G₂ hG) _)
        (fun i y => upHalfLaw_weight O₀ O₁ G₂ hG G₁ hres (hL i) (h₁ i) y)]
      unfold blockGraphLaw
      rw [expect_tensor_eq_sum]
      rfl
    rw [htwo, hdiag]
    have h := UpperReference.cut_block_cap D pr hL hg hB hX hXb hbp hLs hgp hlow hup
      ((F ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D)
    have hn : Recentering.nrm μ ((F ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D) ^ 2 =
        μ.expect (fun ξ => ((F ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D) ξ *
          ((F ∘ upSlotRows O₀ O₁ φ₀ φ₁) ∘ blockHalfRows pr D) ξ) := by
      unfold Recentering.nrm Recentering.ip
      exact Real.sq_sqrt (μ.expect_nonneg fun ξ => mul_self_nonneg _)
    rw [hn] at h
    linarith

end Block

end Sarkozy.BlockAdapter
