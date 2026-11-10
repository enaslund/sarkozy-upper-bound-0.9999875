module

public import Sarkozy.PartV.CoherentChamberCollision

/-! The coherent chamber collision price as a Schur-norm bound on the half graph law. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.Cuts Sarkozy.Recentering

theorem chamber_reflection_left : ∀ i,
    g6Vert 5 (chamberVertices true i) = chamberVertices false i := by
  change ∀ i, act 5 (chamberVertices true i) = chamberVertices false i
  decide +kernel

theorem chamber_reflection_right : ∀ i,
    g6Vert 5 (chamberVertices false i) = chamberVertices true i := by
  change ∀ i, act 5 (chamberVertices false i) = chamberVertices true i
  decide +kernel

variable {p : ℕ}

noncomputable def chamberConfiguration (x y : Fin 6 → ZMod p) : Vertex → ZMod p :=
  joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)

theorem chamberConfiguration_swap (x y : Fin 6 → ZMod p) :
    chamberConfiguration y x = chamberConfiguration x y ∘ g6Vert 5 := by
  funext v
  rcases chamberVertices_cover v with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp only [Function.comp_apply, chamber_reflection_left, chamberConfiguration,
      join_chamber_left, join_chamber_right]
  · simp only [Function.comp_apply, chamber_reflection_right, chamberConfiguration,
      join_chamber_left, join_chamber_right]

/-- The explicit unnormalized collision price `C_w`, including exceptional matchings. -/
noncomputable def chamberCollisionPrice (p : ℕ) (u η : ℚ) : ℝ :=
  ((η : ℝ) + (1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p)) ^ 2) *
      L20Cap.Dbal (Real.sqrt p)⁻¹ (p : ℝ)⁻¹ +
    ((η : ℝ) + (1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p)) ^ 2) *
      (144 * 65536 * L20Cap.chamberCubeDensity p / (p : ℝ) ^ 3)

variable [Fact p.Prime]

noncomputable def weightedChamberCollision (u η : ℚ) (x y : Fin 6 → ZMod p) : ℝ :=
  collisionKernelColl L20Cap.D20Z x y *
    coherentWeight p dictionary39 u η (chamberConfiguration x y)

theorem weightedChamberCollision_nonneg (u η : ℚ) (hη : 0 ≤ η)
    (x y : Fin 6 → ZMod p) : 0 ≤ weightedChamberCollision u η x y := by
  have hη' : (0 : ℝ) ≤ η := by exact_mod_cast hη
  have hK : 0 ≤ collisionKernelColl L20Cap.D20Z x y := by
    rw [collisionKernelColl_eq]
    exact add_nonneg (collisionKernel1_nonneg _ _ _) (collisionKernel2_nonneg _ _ _)
  exact mul_nonneg hK (add_nonneg hη' (sq_nonneg _))

theorem weightedChamberCollision_symm (u η : ℚ) (x y : Fin 6 → ZMod p) :
    weightedChamberCollision u η x y = weightedChamberCollision u η y x := by
  have hK : collisionKernelColl L20Cap.D20Z y x = collisionKernelColl L20Cap.D20Z x y := by
    unfold collisionKernelColl
    rw [collisionCommon_symm y x, collisionKernel_symm L20Cap.D20Z L20Cap.D20Z_antisymm y x]
  have hW : coherentWeight p dictionary39 u η (chamberConfiguration y x) =
      coherentWeight p dictionary39 u η (chamberConfiguration x y) := by
    unfold coherentWeight
    rw [chamberConfiguration_swap,
      coherentScore_g6 p dictionary39 dictionary39_invariant 5]
  simp only [weightedChamberCollision, hK, hW]

open Classical in
theorem weightedChamberCollision_indicator (u η : ℚ) (x y : Fin 6 → ZMod p)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    (if Collision false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y) then
      rawCrossKernel false (chamberConfiguration x y) *
        coherentWeight p dictionary39 u η (chamberConfiguration x y) else 0) =
      weightedChamberCollision u η x y := by
  unfold weightedChamberCollision
  rw [← chamber_collision_indicator x y hx hy]
  split_ifs <;> simp only [chamberConfiguration, zero_mul]

open Classical in
theorem weightedChamberCollision_expect (u η : ℚ) (x : Fin 6 → ZMod p)
    (hx : Function.Injective x) (hne6 : (injLabellings (ZMod p) L20Cap.G6).Nonempty) :
    (graphLaw L20Cap.G6 hne6).expect (fun y =>
      if Collision false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y) then
        rawCrossKernel false (chamberConfiguration x y) *
          coherentWeight p dictionary39 u η (chamberConfiguration x y) else 0) =
      (graphLaw L20Cap.G6 hne6).expect (weightedChamberCollision u η x) := by
  rw [coverRow_expect_graphLaw, coverRow_expect_graphLaw]
  apply congrArg (fun s : ℝ => s / (injLabellings (ZMod p) L20Cap.G6).card)
  refine sum_congr rfl fun y hy => ?_
  have hyF := (mem_injLabellings_iff_feasible L20Cap.G6 y).mp hy
  exact weightedChamberCollision_indicator u η x y hx
    (fun i j h => hyF.1 i (mem_univ _) j (mem_univ _) h)

theorem weightedChamberCollision_transport (u η : ℚ) (x : Fin 6 → ZMod p)
    (hx : Function.Injective x) (hne6 : (injLabellings (ZMod p) L20Cap.G6).Nonempty)
    (hne : (injLabellings (ZMod p) (inducedHalfGraph false false)).Nonempty) :
    CubePins.mass (fun b => (graphLaw (inducedHalfGraph false false) hne).weight b *
      rawCrossKernel false (joinHalves false (chamberLabelsEquiv true x) b) *
      coherentWeight p dictionary39 u η (joinHalves false (chamberLabelsEquiv true x) b))
      (Collision false (chamberLabelsEquiv true x)) =
      (graphLaw L20Cap.G6 hne6).expect (weightedChamberCollision u η x) := by
  classical
  let Ψ : (Half false false → ZMod p) → ℝ := fun b =>
    if Collision false (chamberLabelsEquiv true x) b then
      rawCrossKernel false (joinHalves false (chamberLabelsEquiv true x) b) *
        coherentWeight p dictionary39 u η (joinHalves false (chamberLabelsEquiv true x) b)
    else 0
  have hm : CubePins.mass (fun b =>
      (graphLaw (inducedHalfGraph false false) hne).weight b *
        rawCrossKernel false (joinHalves false (chamberLabelsEquiv true x) b) *
        coherentWeight p dictionary39 u η (joinHalves false (chamberLabelsEquiv true x) b))
      (Collision false (chamberLabelsEquiv true x)) =
      (graphLaw (inducedHalfGraph false false) hne).expect Ψ := by
    unfold CubePins.mass FiniteLaw.expect Ψ
    rw [sum_filter]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> simp only [mul_zero, mul_assoc]
  rw [hm, graphLaw_iso L20Cap.G6 (inducedHalfGraph false false)
    (chamberEquiv false) (chamberEquiv_edges false) hne6 hne Ψ]
  exact weightedChamberCollision_expect u η x hx hne6

theorem weightedChamberCollision_row (hW : WeilBound (ZMod p))
    (h3 : p % 4 = 3) (h64 : 64 ≤ p) (u η : ℚ) (hη : 0 ≤ η)
    (hne6 : (injLabellings (ZMod p) L20Cap.G6).Nonempty)
    (x : Fin 6 → ZMod p) (hx : x ∈ injLabellings (ZMod p) L20Cap.G6) :
    (graphLaw L20Cap.G6 hne6).expect (weightedChamberCollision u η x) ≤
      chamberCollisionPrice p u η := by
  have hxF := (mem_injLabellings_iff_feasible L20Cap.G6 x).mp hx
  have hxinj : Function.Injective x := fun i j h =>
    hxF.1 i (mem_univ _) j (mem_univ _) h
  have hne := chamber_half_nonempty h3 (by omega : 7 < p) false
  rw [← weightedChamberCollision_transport u η x hxinj hne6 hne]
  exact chamber_collision_weight_balanced hW h3 h64 (chamberLabelsEquiv true x)
    ((chamberLabelsEquiv_mem true x).mp hx) hne u η hη

/-- The unnormalized coherent collision operator has form norm at most `C_w`. -/
theorem weightedChamberCollision_schur (hW : WeilBound (ZMod p))
    (h3 : p % 4 = 3) (h64 : 64 ≤ p) (u η : ℚ) (hη : 0 ≤ η)
    (hne6 : (injLabellings (ZMod p) L20Cap.G6).Nonempty) (f : (Fin 6 → ZMod p) → ℝ) :
    |kernelForm (graphLaw L20Cap.G6 hne6) (graphLaw L20Cap.G6 hne6)
        (weightedChamberCollision u η) f f| ≤
      chamberCollisionPrice p u η * nrm (graphLaw L20Cap.G6 hne6) f ^ 2 := by
  apply L20Cap.schur_test _ _ (weightedChamberCollision_nonneg u η hη)
    (weightedChamberCollision_symm u η) _ f
  intro x hx
  have hmem : x ∈ injLabellings (ZMod p) L20Cap.G6 := by
    by_contra h
    simp only [graphLaw, h, ↓reduceIte, lt_self_iff_false] at hx
  exact weightedChamberCollision_row hW h3 h64 u η hη hne6 x hmem

end Sarkozy.PartV.CoherentDictionary
