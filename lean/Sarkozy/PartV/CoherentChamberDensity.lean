module

public import Sarkozy.L20Cap.HalfCount
public import Sarkozy.PartV.CoherentCollisionWeight
public import Sarkozy.Cuts.CutTransport

/-! The old chamber half has the paper's explicit cube density `D₆ = 16/(θh)`. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings

def inducedHalfGraph (isLayer side : Bool) : OrientedGraph (Half isLayer side) where
  E := univ.filter fun e => (e.1.val, e.2.val) ∈ (recordGraph (Fin 2)).E
  loopless v h := (recordGraph (Fin 2)).loopless v.val (mem_filter.mp h).2
  oriented v w hvw hwv := (recordGraph (Fin 2)).oriented v.val w.val
    (mem_filter.mp hvw).2 (mem_filter.mp hwv).2

def chamberVertices (side : Bool) : Fin 6 → Vertex :=
  if side then ![(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]
  else ![(5, 0), (5, 1), (4, 0), (4, 1), (3, 0), (3, 1)]

theorem chamberVertices_side (side : Bool) (i : Fin 6) :
    cutSide false (chamberVertices side i) = side := by
  cases side <;> fin_cases i <;> decide +kernel

def chamberIndex (side : Bool) (i : Fin 6) : Half false side :=
  ⟨chamberVertices side i, chamberVertices_side side i⟩

theorem chamberIndex_bijective (side : Bool) : Function.Bijective (chamberIndex side) := by
  cases side <;> decide +kernel

noncomputable def chamberEquiv (side : Bool) : Fin 6 ≃ Half false side :=
  Equiv.ofBijective (chamberIndex side) (chamberIndex_bijective side)

theorem chamberEquiv_edges (side : Bool) : ∀ i j,
    (i, j) ∈ L20Cap.G6.E ↔ (chamberEquiv side i, chamberEquiv side j) ∈
      (inducedHalfGraph false side).E := by
  cases side <;> decide +kernel

variable {p : ℕ} [Fact p.Prime]

noncomputable def chamberLabelsEquiv (side : Bool) :
    (Fin 6 → ZMod p) ≃ (Half false side → ZMod p) where
  toFun x v := x ((chamberEquiv side).symm v)
  invFun y i := y (chamberEquiv side i)
  left_inv x := by funext i; simp
  right_inv y := by funext v; simp

theorem chamberLabelsEquiv_mem (side : Bool) (x : Fin 6 → ZMod p) :
    x ∈ injLabellings (ZMod p) L20Cap.G6 ↔
      chamberLabelsEquiv side x ∈ injLabellings (ZMod p) (inducedHalfGraph false side) :=
  Cuts.inj_iso _ _ (chamberEquiv side) (chamberEquiv_edges side) x

theorem chamber_half_card (side : Bool) :
    (injLabellings (ZMod p) (inducedHalfGraph false side)).card =
      (injLabellings (ZMod p) L20Cap.G6).card := by
  have h := Fintype.card_congr ((chamberLabelsEquiv (p := p) side).subtypeEquiv
    (chamberLabelsEquiv_mem side))
  simpa only [Fintype.card_coe] using h.symm

theorem chamber_half_nonempty (h3 : p % 4 = 3) (h7 : 7 < p) (side : Bool) :
    (injLabellings (ZMod p) (inducedHalfGraph false side)).Nonempty := by
  obtain ⟨y⟩ := Variance.WeightedMoment.weightedMoment_halfConf_nonempty p h3 h7
  let x := (L20Cap.halfConfEquiv (p := p)).symm y
  exact ⟨chamberLabelsEquiv side x.val, (chamberLabelsEquiv_mem side x.val).mp x.property⟩

theorem chamber_half_density (h3 : p % 4 = 3) (h7 : 7 < p) (side : Bool)
    (hne : (injLabellings (ZMod p) (inducedHalfGraph false side)).Nonempty)
    (x : Half false side → ZMod p) :
    (graphLaw (inducedHalfGraph false side) hne).weight x ≤
      L20Cap.chamberCubeDensity p / (p : ℝ) ^ 6 := by
  classical
  obtain ⟨y, hy⟩ := hne
  have hy' : (chamberLabelsEquiv side).symm y ∈ injLabellings (ZMod p) L20Cap.G6 := by
    rw [chamberLabelsEquiv_mem, Equiv.apply_symm_apply]
    exact hy
  have h := L20Cap.G6_density h3 h7 ⟨_, hy'⟩ ((chamberLabelsEquiv side).symm y)
  simp only [graphLaw, ite_eq_left hy'] at h
  change (if x ∈ injLabellings (ZMod p) (inducedHalfGraph false side) then
    1 / ((injLabellings (ZMod p) (inducedHalfGraph false side)).card : ℝ) else 0) ≤ _
  rw [chamber_half_card]
  split_ifs
  · exact h
  · exact div_nonneg (L20Cap.chamberCubeDensity_pos h7).le (by positivity)

/-- The exceptional chamber mass with the actual graph law and its density supplied. -/
theorem chamber_exceptional_mass_graph (h3 : p % 4 = 3) (h7 : 7 < p)
    (a : Half false true → ZMod p) (ha : Function.Injective a)
    (hne : (injLabellings (ZMod p) (inducedHalfGraph false false)).Nonempty) :
    CubePins.mass (fun b => (graphLaw (inducedHalfGraph false false) hne).weight b *
      rawCrossKernel false (joinHalves false a b)) (Exceptional false a) ≤
        144 * 65536 * L20Cap.chamberCubeDensity p / (p : ℝ) ^ 3 :=
  chamber_exceptional_mass a ha _ _ (L20Cap.chamberCubeDensity_pos h7).le
    (chamber_half_density h3 h7 false hne)

theorem chamber_collision_weight_mass_graph (hW : WeilBound (ZMod p))
    (h3 : p % 4 = 3) (h7 : 7 < p)
    (a : Half false true → ZMod p) (ha : Function.Injective a)
    (hne : (injLabellings (ZMod p) (inducedHalfGraph false false)).Nonempty)
    (u η : ℚ) (hη : 0 ≤ η) (D : ℝ)
    (hD : CubePins.mass (fun b => (graphLaw (inducedHalfGraph false false) hne).weight b *
      rawCrossKernel false (joinHalves false a b)) (Collision false a) ≤ D) :
    CubePins.mass (fun b => (graphLaw (inducedHalfGraph false false) hne).weight b *
      rawCrossKernel false (joinHalves false a b) *
      coherentWeight p dictionary39 u η (joinHalves false a b)) (Collision false a) ≤
        ((η : ℝ) + (1 + |(u : ℝ)| * (14 + 1 / Real.sqrt p)) ^ 2) * D +
        ((η : ℝ) + (1 + |(u : ℝ)| * ((13 / 5 : ℝ) * Real.sqrt p)) ^ 2) *
          (144 * 65536 * L20Cap.chamberCubeDensity p / (p : ℝ) ^ 3) :=
  raw_collision_weight_mass hW false a ha _ u η hη D _
    (L20Cap.chamberCubeDensity_pos h7).le (chamber_half_density h3 h7 false hne) hD

end Sarkozy.PartV.CoherentDictionary
