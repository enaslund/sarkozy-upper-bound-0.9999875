module

public import Sarkozy.PartV.CoherentDictionary
public import Sarkozy.PartV.RootAffine

/-!
# Layer invariance of the coherent root

The exact dictionary supplies the layer-swap symmetry of
`lem:imp:coherent39-law`, both at a prime and on a block.
-/

@[expose] public section

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings CoherentDictionary

section Prime

variable (p : ℕ) [Fact p.Prime]

theorem coherentScore_relabel (D : Dictionary) (e : Vertex ≃ Vertex)
    (hD : (D.map fun sc => (sc.1.image e, sc.2)).Perm D) (x : Vertex → ZMod p) :
    coherentScore p D (x ∘ e) = coherentScore p D x := by
  have ht (sc : Support × ℚ) :
      coherentTerm p (x ∘ e) sc = coherentTerm p x (sc.1.image e, sc.2) := by
    unfold coherentTerm
    congr 2
    apply sum_congr rfl
    intro s _
    rw [prod_image]
    · rfl
    · exact e.injective.injOn
  have h1 : (D.map fun sc => (sc.2 : ℝ) *
      ((∑ s : ZMod p, ∏ i ∈ sc.1, (quadraticChar (ZMod p) (s - (x ∘ e) i) : ℝ)) / p)) =
      (D.map fun sc => (sc.1.image e, sc.2)).map (coherentTerm p x) := by
    rw [List.map_map]
    exact List.map_congr_left fun sc _ => ht sc
  unfold coherentScore
  rw [h1]
  congr 1
  exact (hD.map (coherentTerm p x)).sum_eq

theorem coherentScore39_layerSwap (x : Vertex → ZMod p) :
    coherentScore p dictionary39 (x ∘ layerSwapMap (ZMod 6)) =
      coherentScore p dictionary39 x :=
  coherentScore_relabel p dictionary39 _ dictionary39_layerSwap x

theorem coherentRoot39_weight_layerSwap (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (x : Vertex → ZMod p) :
    (coherentRoot p dictionary39 u hη hne).weight (x ∘ layerSwapMap (ZMod 6)) =
      (coherentRoot p dictionary39 u hη hne).weight x := by
  change (graphLaw _ hne).weight (x ∘ layerSwapMap (ZMod 6)) *
      coherentWeight p dictionary39 u η (x ∘ layerSwapMap (ZMod 6)) / _ =
    (graphLaw _ hne).weight x * coherentWeight p dictionary39 u η x / _
  have hmem : x ∘ layerSwapMap (ZMod 6) ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) ↔
      x ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) :=
    mem_injLabellings_comp_iff _ _ recordGraph_layerSwap x
  have hlam : (graphLaw (recordGraph (Fin 2)) hne).weight (x ∘ layerSwapMap (ZMod 6)) =
      (graphLaw (recordGraph (Fin 2)) hne).weight x := by
    simp only [graphLaw, hmem]
  rw [hlam]
  unfold coherentWeight
  rw [coherentScore39_layerSwap]

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

theorem coherentBlockRoot39_layerSwap (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (H : (Vertex → BlockLabel pr) → ℝ) :
    (coherentBlockRoot pr dictionary39 u hη hne).expect
        (fun y => H (y ∘ layerSwapMap (ZMod 6))) =
      (coherentBlockRoot pr dictionary39 u hη hne).expect H := by
  refine expect_comp_of_weight _ (layerSwapMap (ZMod 6)) (fun y => ?_) H
  unfold coherentBlockRoot
  rw [tensor_weight, tensor_weight]
  exact prod_congr rfl fun i _ =>
    coherentRoot39_weight_layerSwap (pr i) u hη (hne i) (fun v => y v i)

theorem middleBlockReference_coherent39_layerSwap (hne : MiddleNonempty pr)
    (u : ℚ) {η : ℚ} (hη : 0 < η) (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r)
    (H : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (coherentBlockRoot pr dictionary39 u hη hne.L2) W hr).expect
        (fun z => H (z ∘ slotSwap)) =
      (middleBlockReference pr hne (coherentBlockRoot pr dictionary39 u hη hne.L2) W hr).expect H := by
  rw [FiniteLaw.expect_eq_signedIntegral, FiniteLaw.expect_eq_signedIntegral]
  unfold middleBlockReference
  rw [middleReference_eq, LinearMap.smul_apply, LinearMap.smul_apply, middleTilde_layerSwap]
  exact middleBlockFieldLaws_layerSwap pr hne _
    (coherentBlockRoot39_layerSwap pr u hη hne.L2)

end Block

end Sarkozy.PartV
