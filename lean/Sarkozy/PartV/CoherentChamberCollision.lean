module

public import Sarkozy.PartV.CoherentChamberKernel

/-!
# The coherent chamber collision estimate with the ordinary mass bound supplied

The row is an admissible labelling of the actual chamber half graph. The proof
uses the balanced L20 collision estimate and the exact exceptional matching mass.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

open Classical in
theorem chamber_collision_indicator (x y : Fin 6 → ZMod p)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    (if Collision false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y) then
      rawCrossKernel false
        (joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)) else 0) =
      collisionKernelColl L20Cap.D20Z x y := by
  classical
  simp only [collisionKernelColl, chamber_raw_kernel, chamber_collision_iff x y hx hy]

open Classical in
theorem chamber_collision_expect (x : Fin 6 → ZMod p) (hx : Function.Injective x)
    (hne6 : (injLabellings (ZMod p) L20Cap.G6).Nonempty) :
    (graphLaw L20Cap.G6 hne6).expect (fun y =>
      if Collision false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y) then
        rawCrossKernel false
          (joinHalves false (chamberLabelsEquiv true x) (chamberLabelsEquiv false y)) else 0) =
      (graphLaw L20Cap.G6 hne6).expect (collisionKernelColl L20Cap.D20Z x) := by
  classical
  rw [coverRow_expect_graphLaw, coverRow_expect_graphLaw]
  apply congrArg (fun s : ℝ => s / (injLabellings (ZMod p) L20Cap.G6).card)
  refine sum_congr rfl fun y hy => ?_
  have hyF := (mem_injLabellings_iff_feasible L20Cap.G6 y).mp hy
  exact chamber_collision_indicator x y hx
    (fun i j h => hyF.1 i (mem_univ _) j (mem_univ _) h)

theorem chamber_collision_mass_transport (x : Fin 6 → ZMod p) (hx : Function.Injective x)
    (hne6 : (injLabellings (ZMod p) L20Cap.G6).Nonempty)
    (hne : (injLabellings (ZMod p) (inducedHalfGraph false false)).Nonempty) :
    CubePins.mass (fun b =>
      (graphLaw (inducedHalfGraph false false) hne).weight b *
        rawCrossKernel false (joinHalves false (chamberLabelsEquiv true x) b))
      (Collision false (chamberLabelsEquiv true x)) =
      (graphLaw L20Cap.G6 hne6).expect (collisionKernelColl L20Cap.D20Z x) := by
  classical
  let Ψ : (Half false false → ZMod p) → ℝ := fun b =>
    if Collision false (chamberLabelsEquiv true x) b then
      rawCrossKernel false (joinHalves false (chamberLabelsEquiv true x) b) else 0
  have hm : CubePins.mass (fun b =>
      (graphLaw (inducedHalfGraph false false) hne).weight b *
        rawCrossKernel false (joinHalves false (chamberLabelsEquiv true x) b))
      (Collision false (chamberLabelsEquiv true x)) =
      (graphLaw (inducedHalfGraph false false) hne).expect Ψ := by
    unfold CubePins.mass FiniteLaw.expect Ψ
    rw [sum_filter]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [hm, Cuts.graphLaw_iso L20Cap.G6 (inducedHalfGraph false false)
    (chamberEquiv false) (chamberEquiv_edges false) hne6 hne Ψ]
  exact chamber_collision_expect x hx hne6

/-- The ordinary collision mass of the actual chamber kernel is at most `D_bal`. -/
theorem chamber_collision_mass_balanced (hW : WeilBound (ZMod p))
    (h3 : p % 4 = 3) (h64 : 64 ≤ p)
    (a : Half false true → ZMod p)
    (ha : a ∈ injLabellings (ZMod p) (inducedHalfGraph false true))
    (hne : (injLabellings (ZMod p) (inducedHalfGraph false false)).Nonempty) :
    CubePins.mass (fun b => (graphLaw (inducedHalfGraph false false) hne).weight b *
      rawCrossKernel false (joinHalves false a b)) (Collision false a) ≤
        L20Cap.Dbal (Real.sqrt p)⁻¹ (p : ℝ)⁻¹ := by
  classical
  obtain ⟨x, rfl⟩ := (chamberLabelsEquiv (p := p) true).surjective a
  have hx := (chamberLabelsEquiv_mem true x).mpr ha
  have hxF := (mem_injLabellings_iff_feasible L20Cap.G6 x).mp hx
  have hxinj : Function.Injective x := fun i j h =>
    hxF.1 i (mem_univ _) j (mem_univ _) h
  have hne6 : (injLabellings (ZMod p) L20Cap.G6).Nonempty := ⟨x, hx⟩
  rw [chamber_collision_mass_transport x hxinj hne6 hne]
  have hm1 : quadraticChar (ZMod p) (-1) = -1 :=
    collision_chi_neg_one (by simpa only [ZMod.card] using h3)
  simpa only [ZMod.card] using
    L20Cap.balanced_collision_row hW hm1 (by simpa only [ZMod.card] using h64) hne6 x hx

/-- The weighted chamber collision price, with both ordinary and exceptional
mass estimates proved for the graph law. -/
theorem chamber_collision_weight_balanced (hW : WeilBound (ZMod p))
    (h3 : p % 4 = 3) (h64 : 64 ≤ p)
    (a : Half false true → ZMod p)
    (ha : a ∈ injLabellings (ZMod p) (inducedHalfGraph false true))
    (hne : (injLabellings (ZMod p) (inducedHalfGraph false false)).Nonempty)
    (u η : ℚ) (hη : 0 ≤ η) :
    CubePins.mass (fun b => (graphLaw (inducedHalfGraph false false) hne).weight b *
      rawCrossKernel false (joinHalves false a b) *
      coherentWeight p dictionary39 u η (joinHalves false a b)) (Collision false a) ≤
        ((η : ℝ) + (1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p)) ^ 2) *
          L20Cap.Dbal (Real.sqrt p)⁻¹ (p : ℝ)⁻¹ +
        ((η : ℝ) + (1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p)) ^ 2) *
          (144 * 65536 * L20Cap.chamberCubeDensity p / (p : ℝ) ^ 3) := by
  have haF := (mem_injLabellings_iff_feasible (inducedHalfGraph false true) a).mp ha
  have hainj : Function.Injective a := fun v w h =>
    haF.1 v (mem_univ _) w (mem_univ _) h
  exact chamber_collision_weight_mass_graph hW h3 (by omega) a hainj hne u η hη _
    (chamber_collision_mass_balanced hW h3 h64 a ha hne)

end Sarkozy.PartV.CoherentDictionary
