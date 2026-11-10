module

public import Sarkozy.PartV.ChamberCut
public import Sarkozy.FiveType.PolarizationTensor

/-!
# The paired `E` bridge: the polarization orders (`lem:record:paired-e-bridge`(a),
`lem:record:paired-e-joint`(a))

`paper/sections/22_variance.tex`, Section 22.4. The two-layer laws of a middle block form a
five-type datum on the label pairs of one object (V1's `PartV.fieldDatum`, from the `E` law, the
`F` law and the root), whose components at `ϑ₀` are the records `Π_{F_j,𝔅}` (`compF j`),
`Π_{E_s,𝔅}` (`compE s`) and the merges `G_{e,𝔅} = compG 0 0`, `G_{o,𝔅} = compG 1 1`. The rows
of `lem:front12:reference`(i), `‖T^ξ_F - 𝒥‖ ≤ f₂ r`, `‖T^ξ_E - 𝒥‖ ≤ h₂ r` (V1's `RowBounds`, a
hypothesis there and here), give the bridge with `ε_𝔅 = (f₂ + h₂) r_𝔅`:

* `paired_e_bridge_a`: **`lem:record:paired-e-bridge`(a)**, for the datum:
  `Π_{F_1} + Π_{F_2} ⪯_{ϑ₀} Π_{E_0} + Π_{E_1} + ε_𝔅 (G_e + G_o)`; this is
  `lem:tr:polarization`(a) (C1's `FiveType.Datum.polarization_a`).
* `paired_e_bridge_a_slots`: the same order on the slot array, read through the first
  coordinate (V1's `pushL_firstCut_positive`), at the first-coordinate chamber cut `ϑ₀`.
* `paired_e_joint_a`: **`lem:record:paired-e-joint`(a)**, both orders, for a finite set of
  blocks: `⊗(Π_{E_0} + ε G_e) + ⊗(Π_{E_1} + ε G_o) ⪰_{ϑ₀} ⊗Π_{F_1} + ⊗Π_{F_2}` and
  `⊗(Π_{E_0} + Π_{E_1} + ε G) ⪰_{ϑ₀} ⊗Π_{F_1} + ⊗Π_{F_2}`; this is `lem:tr:polarization`(c)
  (`FiveType.polarization_c_first`, `polarization_c_second`).

**Not formalized:** `lem:record:paired-e-bridge`(b) (the centred norm `3/(b - 3)` of the matching
records at `ι`), which needs the actual half marginal of the matching record as a tensor product
of disjoint-triple operators (`TraceMixing/DisjointTripleOrdered` has the one-prime operator);
and the grouping that identifies these block tensor products with the selected factor of
`Matching.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.PartV Sarkozy.FiveType

namespace Sarkozy.Variance

section Bridge

variable {X : Type} [Fintype X] [DecidableEq X] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- **`lem:record:paired-e-bridge`(a)** for the two-layer five-type datum `D` of a middle block
with the rows (i): `Π_{F_1} + Π_{F_2} ⪯_{ϑ₀} Π_{E_0} + Π_{E_1} + ε_𝔅(G_e + G_o)`, with
`ε_𝔅 = (f₂ + h₂) r`. -/
theorem paired_e_bridge_a (D : Datum (Λ → X)) {f h r : ℝ} (hrows : RowBounds D f h r) :
    (chamberCut 0).Below D.QF (D.QE ((f + h) * r)) :=
  D.polarization_a (eF := f * r) (eE := h * r) (fun b hb => (hrows b hb).1)
    (fun b hb => (hrows b hb).2) (le_of_eq (by ring))

/-- **`lem:record:paired-e-bridge`(a) on the slot array**: the order of `paired_e_bridge_a`,
read on the slots through the first coordinate by a reading map `κ` (V1's `toSlot₂` is the
two-layer one), holds at the first-coordinate chamber cut `ϑ₀`. -/
theorem paired_e_bridge_a_slots (D : Datum (Λ → X)) {f h r : ℝ} (hrows : RowBounds D f h r)
    (κ : (Λ → X) → Chamber × Layer → X) :
    (firstChamberCut 0).Below
      (pushL D.QF (fun (Ψ : Chamber → Λ → X) (v : Slot) => κ (Ψ v.1) v.2))
      (pushL (D.QE ((f + h) * r)) (fun (Ψ : Chamber → Λ → X) (v : Slot) => κ (Ψ v.1) v.2)) := by
  have hpos := pushL_firstCut_positive κ _ 0 (paired_e_bridge_a D hrows)
  unfold ReflectionCut.Below
  have e : pushL (D.QE ((f + h) * r)) (fun (Ψ : Chamber → Λ → X) (v : Slot) => κ (Ψ v.1) v.2) -
      pushL D.QF (fun (Ψ : Chamber → Λ → X) (v : Slot) => κ (Ψ v.1) v.2) =
      pushL (D.QE ((f + h) * r) - D.QF)
        (fun (Ψ : Chamber → Λ → X) (v : Slot) => κ (Ψ v.1) v.2) := by
    apply LinearMap.ext
    intro g
    rfl
  rw [e]
  exact hpos

end Bridge

section Joint

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, Fintype (X j)]
  [∀ j, DecidableEq (X j)]

/-- **`lem:record:paired-e-joint`(a)**, both orders, for the five-type data `D j` of the blocks
of a finite set, with row bounds `e_F, e_E` and `ε_𝔅 ≥ e_F + e_E`:
`⊗Π_{F_1} + ⊗Π_{F_2} ⪯_{ϑ₀} ⊗(Π_{E_0} + ε G_e) + ⊗(Π_{E_1} + ε G_o)`, and (for a nonempty set
of blocks) `⊗Π_{F_1} + ⊗Π_{F_2} ⪯_{ϑ₀} ⊗(Π_{E_0} + Π_{E_1} + ε(G_e + G_o))`. -/
theorem paired_e_joint_a [Nonempty J] (D : ∀ j, Datum (X j)) (eF eE ε : J → ℝ)
    (hF : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TF b) (eF j))
    (hE : ∀ j b, (D j).nu.weight b ≠ 0 → NormBound ((D j).nub b) ((D j).TE b) (eE j))
    (hε : ∀ j, eF j + eE j ≤ ε j) :
    (chamberCut 0).Below
        (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2))
        (tensorLaw (fun j => (D j).QE0 (ε j)) + tensorLaw (fun j => (D j).QE1 (ε j))) ∧
      (chamberCut 0).Below
        (tensorLaw (fun j => (D j).compF 1) + tensorLaw (fun j => (D j).compF 2))
        (tensorLaw (fun j => (D j).QE (ε j))) :=
  ⟨(polarization_c_first D eF eE ε hF hE hε).1, polarization_c_second D eF eE ε hF hE hε⟩

end Joint

end Sarkozy.Variance
