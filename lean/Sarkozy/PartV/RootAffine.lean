module

public import Sarkozy.PartV.PositiveRoot

@[expose] public section

/-!
# The positive roots and the square-affine maps ((R3) on every piece)

`paper/sections/20b_positive_roots.tex`, `lem:positive-root-properties`(b): every map
`z ↦ αz + β` with `χ(α) = 1` fixes each score (substitute `z = αz' + β`; the product of the four
factors gains `α⁴`, and `χ(α⁴) = 1`), hence the weight and the root; likewise the coherent score
(`lem:imp:coherent39-law`, every degree). Consequently (R3) of `hyp:record:reference` holds for
the middle block law on every piece: `middleBlockReference_uniform_affine`,
`middleBlockReference_individual_affine`, `middleBlockReference_coherent_affine`.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- A product of linear factors under a square-affine substitution. -/
theorem quadraticChar_prod_affine {ι : Type*} (S : Finset ι) (x : ι → ZMod p) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β z : ZMod p) :
    quadraticChar (ZMod p) (∏ v ∈ S, ((α * z + β) - (α * x v + β))) =
      quadraticChar (ZMod p) (∏ v ∈ S, (z - x v)) := by
  have h : ∏ v ∈ S, ((α * z + β) - (α * x v + β)) = α ^ S.card * ∏ v ∈ S, (z - x v) := by
    rw [← prod_const, ← prod_mul_distrib]
    refine prod_congr rfl fun v _ => ?_
    ring
  rw [h, map_mul, map_pow, hα, one_pow, one_mul]

/-- **The scores are invariant under the square-affine maps**
(`lem:positive-root-properties`(b)). -/
theorem rootTrace_affine (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) :
    rootTrace p j (fun v => α * x v + β) = rootTrace p j x := by
  unfold rootTrace
  have hα0 := ne_zero_of_quadraticChar_eq_one hα
  rw [← Fintype.sum_equiv (affineMap α hα0 β) (fun z => quadraticChar (ZMod p)
    (∏ v ∈ basePair j, ((α * z + β) - (α * x v + β)))) _ (fun _ => rfl)]
  refine sum_congr rfl fun z _ => ?_
  exact quadraticChar_prod_affine p _ x hα β z

theorem individualWeight_affine (u : ℚ) (x : ZMod 6 × Fin 2 → ZMod p) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) :
    individualWeight p u (fun v => α * x v + β) = individualWeight p u x := by
  unfold individualWeight rootScore
  simp only [rootTrace_affine p _ x hα β]

theorem graphLaw_weight_affine' {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) {α : ZMod p} (hα : quadraticChar (ZMod p) α = 1)
    (β : ZMod p) (y : W → ZMod p) :
    (graphLaw G hne).weight (fun w => α * y w + β) = (graphLaw G hne).weight y := by
  have hmem : (fun w => α * y w + β) ∈ injLabellings (ZMod p) G ↔
      y ∈ injLabellings (ZMod p) G := by
    rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
    exact feasible_affine_iff G hα β y
  simp only [graphLaw, hmem]

/-- **The individual-square root is invariant under the square-affine maps.** -/
theorem individualRoot_weight_affine (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) (x : ZMod 6 × Fin 2 → ZMod p) :
    (individualRoot p u hne).weight (fun v => α * x v + β) = (individualRoot p u hne).weight x := by
  change (graphLaw _ hne).weight (fun v => α * x v + β) *
      individualWeight p u (fun v => α * x v + β) / _ =
    (graphLaw _ hne).weight x * individualWeight p u x / _
  rw [graphLaw_weight_affine' p _ hne hα β, individualWeight_affine p u x hα β]

/-- The coherent score is invariant under the square-affine maps. -/
theorem coherentScore_affine (D : Dictionary) (x : ZMod 6 × Fin 2 → ZMod p) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) :
    coherentScore p D (fun v => α * x v + β) = coherentScore p D x := by
  unfold coherentScore
  congr 2
  refine List.map_congr_left fun Sc _ => ?_
  congr 2
  have hα0 := ne_zero_of_quadraticChar_eq_one hα
  rw [← Fintype.sum_equiv (affineMap α hα0 β) (fun s => ∏ i ∈ Sc.1,
    (quadraticChar (ZMod p) ((α * s + β) - (α * x i + β)) : ℝ)) _ (fun _ => rfl)]
  refine sum_congr rfl fun s _ => ?_
  refine prod_congr rfl fun i _ => ?_
  have : (α * s + β) - (α * x i + β) = α * (s - x i) := by ring
  rw [this, map_mul, hα, one_mul]

/-- **The coherent root is invariant under the square-affine maps.** -/
theorem coherentRoot_weight_affine (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) {α : ZMod p}
    (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) (x : ZMod 6 × Fin 2 → ZMod p) :
    (coherentRoot p D u hη hne).weight (fun v => α * x v + β) =
      (coherentRoot p D u hη hne).weight x := by
  change (graphLaw _ hne).weight (fun v => α * x v + β) *
      coherentWeight p D u η (fun v => α * x v + β) / _ =
    (graphLaw _ hne).weight x * coherentWeight p D u η x / _
  rw [graphLaw_weight_affine' p _ hne hα β]
  unfold coherentWeight
  rw [coherentScore_affine p D x hα β]

end Prime

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

theorem individualBlockRoot_affine (u : ℚ)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (α β : BlockLabel pr) (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (H : (ZMod 6 × Fin 2 → BlockLabel pr) → ℝ) :
    (individualBlockRoot pr u hne).expect (fun z => H (fun w i => α i * z w i + β i)) =
      (individualBlockRoot pr u hne).expect H := by
  unfold individualBlockRoot
  exact expect_tensor_comp (fun i => individualRoot (pr i) u (hne i))
    (fun i => Equiv.piCongrRight fun _ => affineMap (α i) (ne_zero_of_quadraticChar_eq_one (hα i))
      (β i))
    (fun i y => individualRoot_weight_affine (pr i) u (hne i) (hα i) (β i) y) H

theorem coherentBlockRoot_affine (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (α β : BlockLabel pr) (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (H : (ZMod 6 × Fin 2 → BlockLabel pr) → ℝ) :
    (coherentBlockRoot pr D u hη hne).expect (fun z => H (fun w i => α i * z w i + β i)) =
      (coherentBlockRoot pr D u hη hne).expect H := by
  unfold coherentBlockRoot
  exact expect_tensor_comp (fun i => coherentRoot (pr i) D u hη (hne i))
    (fun i => Equiv.piCongrRight fun _ => affineMap (α i) (ne_zero_of_quadraticChar_eq_one (hα i))
      (β i))
    (fun i y => coherentRoot_weight_affine (pr i) D u hη (hne i) (hα i) (β i) y) H

/-- **(R3) for the middle block law with the individual-square root.** -/
theorem middleBlockReference_individual_affine (hne : MiddleNonempty pr) (u : ℚ)
    (α β : BlockLabel pr) (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (H : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr).expect
        (fun z => H (fun v i => α i * z v i + β i)) =
      (middleBlockReference pr hne (individualBlockRoot pr u hne.L2) W hr).expect H :=
  middleBlockReference_affine pr hne _ α β hα (individualBlockRoot_affine pr u hne.L2 α β hα) W hr H

/-- **(R3) for the middle block law with the coherent root.** -/
theorem middleBlockReference_coherent_affine (hne : MiddleNonempty pr) (D : Dictionary) (u : ℚ)
    {η : ℚ} (hη : 0 < η) (α β : BlockLabel pr) (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (H : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (coherentBlockRoot pr D u hη hne.L2) W hr).expect
        (fun z => H (fun v i => α i * z v i + β i)) =
      (middleBlockReference pr hne (coherentBlockRoot pr D u hη hne.L2) W hr).expect H :=
  middleBlockReference_affine pr hne _ α β hα (coherentBlockRoot_affine pr D u hη hne.L2 α β hα)
    W hr H

/-- **(R3) for the uniform root**, recorded for symmetry. -/
theorem middleBlockReference_uniform_affine (hne : MiddleNonempty pr)
    (α β : BlockLabel pr) (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (H : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne (uniformRoot pr hne) W hr).expect
        (fun z => H (fun v i => α i * z v i + β i)) =
      (middleBlockReference pr hne (uniformRoot pr hne) W hr).expect H :=
  middleBlockReference_affine pr hne _ α β hα
    (fun H' => blockGraphLaw_expect_affine pr _ hne.L2 α β hα H') W hr H

end Block

end Sarkozy.PartV
