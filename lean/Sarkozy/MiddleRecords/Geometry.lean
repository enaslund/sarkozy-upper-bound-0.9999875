module

public import Sarkozy.PartV.Components
public import Sarkozy.MiddleRecords.Mirror

/-!
# Query images of the two-layer middle records (`cert:record:middle-geometry`)

`paper/sections/21_middle_records.tex`, `cert:record:middle-geometry`, for the two-layer fold
and matching records. A two-layer record of pattern `φ` reads the slot `(u₀, u₁, ℓ)` as the
object `φ(u₀)` in layer `ℓ` (V1's `midEmission`), and the query `j` of `𝓔₆` is the slot pair
`(0, j, 0) → (2, rot j, 1)` (`querySource`, `queryTarget`). With the labels `x_i = (i, 0)` and
`y_i = (i, 1)`, every query reads (`fold_query`, `matching_query`, by `decide` over the six
chambers):
* in `F₀`: `x₀ → y₂`, the reference cross edge `𝖠` (so `F₀` accepts);
* in `F₁`: `x₁ → y₀`, the channel `𝖢` (`F1_query_is_C`);
* in `F₂`: `x₂ → y₁`, the reflected channel `𝖢^ς = χ(y₁ - x₂)`;
* in `E₀` and `E₁`: `x₀ → y₁`, the channel `𝖣` (`E_query_is_D`).

These are the frozen geometry record's claims for the two-layer records. V3's
`Sarkozy.PartVRecords.mergeEmission_query` and `midDiag_queryTarget`/`midDiag_querySource` check
the merges and the one-layer `E_s` (`0 → 1`). **Not checked here:** the sides of the chamber
cuts `ϑ₁`, `ϑ₂` for the one-layer `E₀`, `E₁`.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Sarkozy.Labellings Sarkozy.PartV

/-- The query image of a two-layer record of pattern `φ`. -/
def queryImage {O : Type*} (φ : ZMod 6 → O) (j : Chamber) : (O × Fin 2) × (O × Fin 2) :=
  (midEmission φ (querySource j), midEmission φ (queryTarget j))

/-- **The fold records**: every query of `𝓔₆` reads `x₀ → y₂` in `F₀`, `x₁ → y₀` in `F₁` and
`x₂ → y₁` in `F₂`. -/
theorem fold_query (j : Chamber) :
    queryImage (fold 0) j = ((0, 0), (2, 1)) ∧ queryImage (fold 1) j = ((1, 0), (0, 1)) ∧
      queryImage (fold 2) j = ((2, 0), (1, 1)) := by
  revert j
  decide

/-- **The matching records**: every query of `𝓔₆` reads `x₀ → y₁` in `E₀` and in `E₁`. -/
theorem matching_query (j : Chamber) :
    queryImage (matching 0) j = ((0, 0), (1, 1)) ∧
      queryImage (matching 1) j = ((0, 0), (1, 1)) := by
  revert j
  decide

/-- The label `(o, ℓ)` of a two-layer record as a channel label (`x_o` for `ℓ = 0`, `y_o` for
`ℓ = 1`). -/
def toLbl (z : Fin 3 × Fin 2) : Lbl := (decide (z.2 = 1), z.1)

/-- **`F₀` accepts**: its query image is the edge of the reference cross channel `𝖠`. -/
theorem F0_query_is_A (j : Chamber) :
    (toLbl (queryImage (fold 0) j).1, toLbl (queryImage (fold 0) j).2) = Chan.A.edge := by
  revert j
  decide

/-- **`F₁` needs the cross edge `x₁ → y₀`**, the channel `𝖢`. -/
theorem F1_query_is_C (j : Chamber) :
    (toLbl (queryImage (fold 1) j).1, toLbl (queryImage (fold 1) j).2) = Chan.C.edge := by
  revert j
  decide

/-- **`E₀`, `E₁` need the cross edge `x₀ → y₁`**, the channel `𝖣`. -/
theorem E_query_is_D (s : Fin 2) (j : Chamber) :
    (toLbl (queryImage (matching s) j).1, toLbl (queryImage (matching s) j).2) = Chan.D.edge := by
  revert s j
  decide

end Sarkozy.MiddleRecords
