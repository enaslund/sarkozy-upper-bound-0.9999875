module

public import Sarkozy.PartV.RootAffine
public import Sarkozy.PartV.ChamberCut

@[expose] public section

/-!
# The middle reference is invariant under the layer swap (`lem:front12:reference`(iii))

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(iii) ("invariant under the layer
swap"); `paper/sections/20b_positive_roots.tex`, `lem:positive-root-properties`(b) (the layer swap
fixes each score). The slot layer swap `(u₀, u₁, ℓ) ↦ (u₀, u₁, 1 - ℓ)` acts on the two-layer
components through the swap of the two layers of each object, which is an automorphism of
`G_{L,2}`, `G_{F,2}` and `G_{E,2}` and fixes the scores of the positive roots; the one-layer
diagonal copies are fixed by it (`middleTilde_layerSwap`, and the block corollaries for the three
roots).
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-- The layer swap of the slots. -/
def slotSwap (v : Slot) : Slot := (v.1, v.2.1, 1 - v.2.2)

theorem layerFin_swap (ℓ : Layer) : layerFin (1 - ℓ) = Equiv.swap 0 1 (layerFin ℓ) := by
  revert ℓ
  decide

theorem midEmission_slotSwap {O : Type*} (φ : ZMod 6 → O) (v : Slot) :
    midEmission φ (slotSwap v) = layerSwapMap O (midEmission φ v) := by
  simp only [midEmission, slotSwap, layerSwapMap, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id_eq, layerFin_swap]

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The middle law is invariant under the layer swap**, when every two-layer field law is
invariant under the swap of the layers of each object. -/
theorem middleTilde_layerSwap (F : MiddleFieldLaws X) (W : MiddleWeights) (r : ℝ)
    (hF : ∀ (f : FType) (H : (f.Obj × Fin 2 → X) → ℝ),
      (F.two f).expect (fun y => H (y ∘ layerSwapMap f.Obj)) = (F.two f).expect H)
    (H : (Slot → X) → ℝ) :
    middleTilde F W r (fun z => H (z ∘ slotSwap)) = middleTilde F W r H := by
  unfold middleTilde tildeMeasure
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  congr 1
  rcases i with ⟨b, t, φ⟩
  rw [← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral]
  cases b
  · simp only [midComponent, expect_emit]
    rfl
  · simp only [midComponent, expect_emit]
    have h := hF t.field (fun y => H (y ∘ midEmission (t.pat φ)))
    have he : ∀ y : t.field.Obj × Fin 2 → X,
        (y ∘ midEmission (t.pat φ)) ∘ slotSwap = (y ∘ layerSwapMap t.field.Obj) ∘
          midEmission (t.pat φ) := by
      intro y
      funext v
      simp only [Function.comp_apply, midEmission_slotSwap]
    simp only [he]
    exact h

/-- Expectation invariance from weight invariance under a relabelling. -/
theorem expect_comp_of_weight {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y]
    (μ : FiniteLaw (W → Y)) (π : W ≃ W) (h : ∀ y, μ.weight (y ∘ π) = μ.weight y)
    (H : (W → Y) → ℝ) : μ.expect (fun y => H (y ∘ π)) = μ.expect H := by
  unfold FiniteLaw.expect
  calc ∑ y, μ.weight y * H (y ∘ π) = ∑ y, μ.weight (relabelEquiv π y) * H (relabelEquiv π y) :=
        sum_congr rfl fun y _ => by
          change _ = μ.weight (y ∘ π) * H (y ∘ π)
          rw [h y]
    _ = ∑ y, μ.weight y * H y := Fintype.sum_equiv (relabelEquiv π) _ _ fun _ => rfl

/-- The layer swap fixes each base pair. -/
theorem basePair_layerSwap (j : Fin 3) :
    (basePair j).image (layerSwapMap (ZMod 6)) = basePair j := by
  revert j
  decide

section Prime

variable (p : ℕ) [Fact p.Prime]

theorem rootTrace_layerSwap (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) :
    rootTrace p j (x ∘ layerSwapMap (ZMod 6)) = rootTrace p j x := by
  unfold rootTrace
  refine sum_congr rfl fun z _ => ?_
  congr 1
  conv_rhs => rw [← basePair_layerSwap j]
  rw [prod_image]
  · rfl
  · intro a _ b _ hab
    exact (layerSwapMap (ZMod 6)).injective hab

/-- **The individual-square root is invariant under the layer swap.** -/
theorem individualRoot_weight_layerSwap (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (x : ZMod 6 × Fin 2 → ZMod p) :
    (individualRoot p u hne).weight (x ∘ layerSwapMap (ZMod 6)) =
      (individualRoot p u hne).weight x := by
  change (graphLaw _ hne).weight (x ∘ layerSwapMap (ZMod 6)) *
      individualWeight p u (x ∘ layerSwapMap (ZMod 6)) / _ =
    (graphLaw _ hne).weight x * individualWeight p u x / _
  have hmem : x ∘ layerSwapMap (ZMod 6) ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) ↔
      x ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) :=
    mem_injLabellings_comp_iff _ _ recordGraph_layerSwap x
  have hlam : (graphLaw (recordGraph (Fin 2)) hne).weight (x ∘ layerSwapMap (ZMod 6)) =
      (graphLaw (recordGraph (Fin 2)) hne).weight x := by
    simp only [graphLaw, hmem]
  rw [hlam]
  unfold individualWeight rootScore
  simp only [rootTrace_layerSwap]

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The field laws of the middle block law are invariant under the layer swap, given the root. -/
theorem middleBlockFieldLaws_layerSwap (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
    (hroot : ∀ H : (ZMod 6 × Fin 2 → BlockLabel pr) → ℝ,
      root.expect (fun y => H (y ∘ layerSwapMap (ZMod 6))) = root.expect H) :
    ∀ (f : FType) (H : (f.Obj × Fin 2 → BlockLabel pr) → ℝ),
      ((middleBlockFieldLaws pr hne root).two f).expect (fun y => H (y ∘ layerSwapMap f.Obj)) =
        ((middleBlockFieldLaws pr hne root).two f).expect H
  | .L, H => hroot H
  | .F, H => blockGraphLaw_expect_auto pr (foldGraph (Fin 2)) hne.F2 _ foldGraph_layerSwap H
  | .E, H => blockGraphLaw_expect_auto pr (matchGraph (Fin 2)) hne.E2 _
      (matchGraph_auto (Fin 2) _) H

/-- **Layer-swap invariance of the middle block law, uniform root.** -/
theorem middleBlockReference_uniform_layerSwap (hne : MiddleNonempty pr) (W : MiddleWeights)
    {r : ℝ} (hr : 0 ≤ r) (H : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (uniformRoot pr hne) W hr).expect (fun z => H (z ∘ slotSwap)) =
      (middleBlockReference pr hne (uniformRoot pr hne) W hr).expect H := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.expect_eq_signedIntegral]
  unfold middleBlockReference
  rw [middleReference_eq, LinearMap.smul_apply, LinearMap.smul_apply, middleTilde_layerSwap]
  exact middleBlockFieldLaws_layerSwap pr hne _
    (fun H' => blockGraphLaw_expect_auto pr (recordGraph (Fin 2)) hne.L2 _ recordGraph_layerSwap H')

/-- **Layer-swap invariance of the middle block law, individual-square root.** -/
theorem middleBlockReference_individual_layerSwap (hne : MiddleNonempty pr) (u : ℚ)
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (H : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr).expect
        (fun z => H (z ∘ slotSwap)) =
      (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr).expect H := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.expect_eq_signedIntegral]
  unfold middleBlockReference
  rw [middleReference_eq, LinearMap.smul_apply, LinearMap.smul_apply, middleTilde_layerSwap]
  refine middleBlockFieldLaws_layerSwap pr hne _ (fun H' => ?_)
  refine expect_comp_of_weight _ (layerSwapMap (ZMod 6)) (fun y => ?_) H'
  unfold individualBlockRoot
  rw [tensor_weight, tensor_weight]
  exact prod_congr rfl fun i _ =>
    individualRoot_weight_layerSwap (pr i) u (hne.L2 i) (fun v => y v i)

end Block

end Sarkozy.PartV
