module

public import Sarkozy.Extraction.CollisionSignedIncident
public import Sarkozy.L20Cap.RectGraph
public import Sarkozy.L20Cap.Collisions

/-!
# The surviving pins and elimination orders for the balanced L20 collision bound

The sixteen core/private pins have incompatible signed constraints. For the
twenty remaining pins the merged-neighbour price is one. The elimination orders
give degrees `3,3,4,4,4` for a core pin and `2,3,3,4,4` for a private pin.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy.Extraction

def balancedCore : Finset (Fin 6) := {0, 1, 4, 5}

def balancedPair : Finset (Fin 6) := {2, 3}

theorem balanced_univ : (univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := by
  decide +kernel

theorem balanced_signs : ∀ i j, D20Z i j = 0 ∨ D20Z i j = 1 ∨ D20Z i j = -1 := by
  decide +kernel

/-- Exactly core/core and private/private pins survive. -/
theorem balanced_gamma : ∀ i j,
    collisionGamma G6 D20Z i j ↔ (i ∈ balancedPair ↔ j ∈ balancedPair) := by
  decide +kernel

theorem balanced_mg : ∀ i j, collisionGamma G6 D20Z i j → rowsMg G6 D20Z j i = 0 := by
  decide +kernel

theorem balanced_degree : ∀ i, rowsDeg0 G6 i = ![2, 2, 0, 0, 2, 2] i := by
  decide +kernel

theorem balanced_total_degree : ∀ i, rowsDeg0 G6 i + collisionR D20Z i = 4 := by
  decide +kernel

theorem balanced_delta : collisionDeltaPlus G6 = 2 := by
  decide +kernel

theorem balanced_neighbours : ∀ i, rowsN D20Z i =
    if i ∈ balancedPair then balancedCore else balancedPair := by
  decide +kernel

/-- Ranks of the five unpinned vertices, with the pinned vertex put last. -/
def balancedOrd (i _j : Fin 6) : Fin 6 → ℕ :=
  ![![5, 2, 3, 4, 0, 1], ![2, 5, 3, 4, 0, 1], ![0, 2, 5, 4, 1, 3],
    ![0, 2, 4, 5, 1, 3], ![0, 1, 3, 4, 5, 2], ![0, 1, 3, 4, 2, 5]] i

theorem balancedOrd_spec : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i →
    balancedOrd i j ℓ = balancedOrd i j ℓ' → ℓ = ℓ' := by
  decide +kernel

def balancedT (i : Fin 6) : Fin 6 → ℕ :=
  ![![0, 4, 4, 4, 3, 3], ![4, 0, 4, 4, 3, 3], ![2, 3, 0, 4, 3, 4],
    ![2, 3, 4, 0, 3, 4], ![3, 3, 4, 4, 0, 4], ![3, 3, 4, 4, 4, 0]] i

theorem balancedT_eq : ∀ i j ℓ, collisionGamma G6 D20Z i j → ℓ ≠ i →
    collisionT G6 D20Z balancedOrd i j ℓ = balancedT i ℓ := by
  decide +kernel

/-- The five count-error factors for any surviving pin. -/
theorem balanced_product (f : ℕ → ℝ) (i j : Fin 6)
    (h : collisionGamma G6 D20Z i j) :
    (∏ ℓ ∈ univ.erase i, f (collisionT G6 D20Z balancedOrd i j ℓ)) =
      if i ∈ balancedPair then f 2 * f 3 ^ 2 * f 4 ^ 2 else f 3 ^ 2 * f 4 ^ 3 := by
  have ht : (∏ ℓ ∈ univ.erase i, f (collisionT G6 D20Z balancedOrd i j ℓ)) =
      ∏ ℓ ∈ univ.erase i, f (balancedT i ℓ) :=
    prod_congr rfl fun ℓ hℓ => congrArg f (balancedT_eq i j ℓ h (mem_erase.mp hℓ).1)
  have he : ∀ v : Fin 6, univ.erase v =
      ![{1, 2, 3, 4, 5}, {0, 2, 3, 4, 5}, {0, 1, 3, 4, 5},
        {0, 1, 2, 4, 5}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}] v := by
    decide +kernel
  rw [ht, he]
  fin_cases i <;> norm_num [balancedT, balancedPair] <;> ring

end Sarkozy.L20Cap
