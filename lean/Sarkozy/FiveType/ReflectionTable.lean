module

public import Sarkozy.Labellings.Patterns

/-!
# The table of reflections (`tab:reflection`)

Source: `paper/sections/17_completion_repair.tex`, `tab:reflection`, used in
`lem:record:fold-identification`(e).

Precomposition with the generators of `𝒢₆`: for each generator `α`, the images
`(F_0 ∘ α, F_1 ∘ α, F_2 ∘ α)` of the folds and the permutations `ψ_{s,α}` with
`E_s ∘ α = ψ_{s,α} ∘ E_s`:

| `α` | `(F_0∘α, F_1∘α, F_2∘α)` | `ψ_{0,α}` | `ψ_{1,α}` |
|---|---|---|---|
| `ϑ_1 : u ↦ 1 - u` | `(F_1, F_0, F_2)` | `(0 1)` | `(1 2)` |
| `ϑ_2 : u ↦ 3 - u` | `(F_2, F_1, F_0)` | `(0 2)` | `(0 1)` |
| `ϑ_0 : u ↦ 5 - u` | `(F_0, F_2, F_1)` | `(1 2)` | `(0 2)` |
| `u ↦ u + 2` | `(F_2, F_0, F_1)` | `(0 1 2)` | `(0 1 2)` |

Each row is checked by `decide` over `ℤ/6ℤ`. The cycle `(0 1 2)` (`0 ↦ 1 ↦ 2 ↦ 0`) is
`finRotate 3`. This completes the generator statements of `Labellings/Patterns.lean`
(`fold_refl1/3/5`, `fold_translation`, `matching_generators`) with the explicit permutations.
-/

@[expose] public section

namespace Sarkozy.FiveType

open Sarkozy.Labellings

/-- **`tab:reflection`, row `ϑ_1 : u ↦ 1 - u`.** -/
theorem tab_reflection_one (u : ZMod 6) :
    (fold 0 (chamberRefl 1 u) = fold 1 u ∧ fold 1 (chamberRefl 1 u) = fold 0 u ∧
      fold 2 (chamberRefl 1 u) = fold 2 u) ∧
    matching 0 (chamberRefl 1 u) = Equiv.swap (0 : Fin 3) 1 (matching 0 u) ∧
    matching 1 (chamberRefl 1 u) = Equiv.swap (1 : Fin 3) 2 (matching 1 u) := by
  revert u
  decide

/-- **`tab:reflection`, row `ϑ_2 : u ↦ 3 - u`.** -/
theorem tab_reflection_three (u : ZMod 6) :
    (fold 0 (chamberRefl 3 u) = fold 2 u ∧ fold 1 (chamberRefl 3 u) = fold 1 u ∧
      fold 2 (chamberRefl 3 u) = fold 0 u) ∧
    matching 0 (chamberRefl 3 u) = Equiv.swap (0 : Fin 3) 2 (matching 0 u) ∧
    matching 1 (chamberRefl 3 u) = Equiv.swap (0 : Fin 3) 1 (matching 1 u) := by
  revert u
  decide

/-- **`tab:reflection`, row `ϑ_0 : u ↦ 5 - u`.** -/
theorem tab_reflection_five (u : ZMod 6) :
    (fold 0 (chamberRefl 5 u) = fold 0 u ∧ fold 1 (chamberRefl 5 u) = fold 2 u ∧
      fold 2 (chamberRefl 5 u) = fold 1 u) ∧
    matching 0 (chamberRefl 5 u) = Equiv.swap (1 : Fin 3) 2 (matching 0 u) ∧
    matching 1 (chamberRefl 5 u) = Equiv.swap (0 : Fin 3) 2 (matching 1 u) := by
  revert u
  decide

/-- **`tab:reflection`, row `u ↦ u + 2`**; `(0 1 2)` is `finRotate 3`. -/
theorem tab_reflection_translation (u : ZMod 6) :
    (fold 0 (u + 2) = fold 2 u ∧ fold 1 (u + 2) = fold 0 u ∧ fold 2 (u + 2) = fold 1 u) ∧
    matching 0 (u + 2) = finRotate 3 (matching 0 u) ∧
    matching 1 (u + 2) = finRotate 3 (matching 1 u) := by
  revert u
  decide

end Sarkozy.FiveType
