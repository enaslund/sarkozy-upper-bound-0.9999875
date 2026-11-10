module

public import Sarkozy.PartV.Components
public import Sarkozy.Labellings.Layer12

@[expose] public section

/-!
# The query images of the middle records (`cert:record:middle-geometry`)

`paper/sections/21_middle_records.tex`, `cert:record:middle-geometry`.

The six queries of `𝓔_6` are `(0, j, 0) → (2, rot j, 1)` (`querySource j`, `queryTarget j` of
`Slots.lean`). A middle record placed by a pattern `φ` reads the slot `(u₀, u₁, ℓ)` as the object
`φ(u₀)` at the layer `ℓ` (V1's `midEmission`), so every query projects onto the same pair of
(object, layer) labels, `(φ(0), 0) → (φ(2), 1)` (`queryImage`, `queryImage_eq`). With the paper's
labels `x_i = (i, 0)` and `y_i = (i, 1)` (`x_i = i`, `y_i = 3 + i`), the certificate's facts are
checked by `decide` (`middle_geometry`):

* two-layer records: `F_0` reads `x_0 → y_2`, which is an edge of `G_{F,2}`, so `F_0` accepts;
  `F_1` needs exactly `x_1 → y_0`, `F_2` exactly `x_2 → y_1`, and `E_0`, `E_1` exactly `x_0 → y_1`,
  none of which is an edge of their graphs;
* one-layer records (`Diag_ι`, `midDiagEmission`): `E_0` and `E_1` need exactly `0 → 1`;
* at the chamber cut `ϑ_1` for `E_0` and `ϑ_2` for `E_1`, the label `2` lies on both sides of the
  cut, the label `1` on the plus side only and `0` on the other side only.

These are statements about the patterns and the emissions; the records themselves are V3's
(`Sarkozy.PartVRecords.Frame`), which place exactly these patterns.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.PartV

/-- **The image of the query `j` under the middle record of the pattern `φ`**: the pair of
(object, layer) labels it reads. -/
def queryImage {O : Type*} (φ : ZMod 6 → O) (j : Chamber) : (O × Fin 2) × (O × Fin 2) :=
  (midEmission φ (querySource j), midEmission φ (queryTarget j))

/-- The image under the one-layer diagonal copy `Diag_ι`. -/
def queryImage₁ {O : Type*} (φ : ZMod 6 → O) (j : Chamber) : (O × Fin 1) × (O × Fin 1) :=
  (midDiagEmission φ (querySource j), midDiagEmission φ (queryTarget j))

/-- **Every query projects onto `(φ(0), 0) → (φ(2), 1)`**, whatever `j`. -/
theorem queryImage_eq {O : Type*} (φ : ZMod 6 → O) (j : Chamber) :
    queryImage φ j = ((φ 0, 0), (φ 2, 1)) := rfl

/-- The one-layer image is `(φ(0), 0) → (φ(2), 0)`. -/
theorem queryImage₁_eq {O : Type*} (φ : ZMod 6 → O) (j : Chamber) :
    queryImage₁ φ j = ((φ 0, 0), (φ 2, 0)) := rfl

/-- The labels of a pattern on the plus half of a chamber cut. -/
def plusLabels (φ : ZMod 6 → Fin 3) (i : ZMod 6) : Finset (Fin 3) := (chamberCut i).half.image φ

/-- The labels of a pattern on the other half of a chamber cut. -/
def minusLabels (φ : ZMod 6 → Fin 3) (i : ZMod 6) : Finset (Fin 3) :=
  ((chamberCut i).half)ᶜ.image φ

/-- **`cert:record:middle-geometry`.** With `x_i = (i, 0)`, `y_i = (i, 1)`:
(1) the six queries read `x_0 → y_2` in `F_0`, an edge of `G_{F,2}` (so `F_0` accepts), and need
exactly `x_1 → y_0` in `F_1`, `x_2 → y_1` in `F_2`, `x_0 → y_1` in `E_0` and in `E_1`, none of them
an edge of `G_{F,2}` or `G_{E,2}`; (2) in the one-layer `E_0`, `E_1` they need exactly `0 → 1`;
(3) at `ϑ_1` for `E_0` and at `ϑ_2` for `E_1` the label `2` is on both sides, `1` on the plus side
only and `0` on the other side only. -/
theorem middle_geometry :
    (∀ j, queryImage (fold 0) j = ((0, 0), (2, 1)) ∧
      queryImage (fold 0) j ∈ (foldGraph (Fin 2)).E) ∧
    (∀ j, queryImage (fold 1) j = ((1, 0), (0, 1)) ∧
      queryImage (fold 1) j ∉ (foldGraph (Fin 2)).E) ∧
    (∀ j, queryImage (fold 2) j = ((2, 0), (1, 1)) ∧
      queryImage (fold 2) j ∉ (foldGraph (Fin 2)).E) ∧
    (∀ s : Fin 2, ∀ j, queryImage (matching s) j = ((0, 0), (1, 1)) ∧
      queryImage (matching s) j ∉ (matchGraph (Fin 2)).E) ∧
    (∀ s : Fin 2, ∀ j, queryImage₁ (matching s) j = ((0, 0), (1, 0))) ∧
    (plusLabels (matching 0) 1 = {1, 2} ∧ minusLabels (matching 0) 1 = {0, 2}) ∧
    (plusLabels (matching 1) 2 = {1, 2} ∧ minusLabels (matching 1) 2 = {0, 2}) := by
  refine ⟨fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩, fun s j => ⟨?_, ?_⟩,
    fun s j => ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [queryImage_eq]; decide
  · rw [queryImage_eq, mem_foldGraph]; decide
  · rw [queryImage_eq]; decide
  · rw [queryImage_eq, mem_foldGraph]; decide
  · rw [queryImage_eq]; decide
  · rw [queryImage_eq, mem_foldGraph]; decide
  · rw [queryImage_eq]; revert s; decide
  · simp [matchGraph]
  · rw [queryImage₁_eq]; revert s; decide
  · unfold plusLabels chamberCut; decide
  · unfold minusLabels chamberCut; decide
  · unfold plusLabels chamberCut; decide
  · unfold minusLabels chamberCut; decide

end Sarkozy.PartVLaws
