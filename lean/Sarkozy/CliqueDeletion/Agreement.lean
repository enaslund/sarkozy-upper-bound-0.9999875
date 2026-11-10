module

public import Sarkozy.CliqueDeletion.Paper

@[expose] public section

/-!
# Agreement with the paper's exception below `2¹⁶` (`lem:frontier:iidlocal`(iv))

`paper/sections/19_prefix.tex`, `lem:frontier:iidlocal`(iv): the exception `λ^ex_p` of the
six-label law is "supported on labellings `z` with `z_{ιv} = z_v` for all `v` (fixed samplewise
by `ι`)". Hence, for `p < 2¹⁶`, where V1's prefix law is the six-label law of `def:clique-law`:

* `prefixLaw_flip_support`: every labelling of positive weight is fixed by `ι`;
* `prefixLaw_symQueryEq_iff`: on the support, the `ι`-closed event `symQueryEq 𝓔₆` deleted by
  `cliqueDeletion` is the paper's event `queryEq 𝓔₆`;
* **`prefixLaw_restrict_eq`**: the deleted measures agree, `1_{symQueryEq} μ_p = 1_{queryEq} μ_p`,
  so for `p < 2¹⁶` the deletion of `cliqueDeletion` is exactly the paper's `λ^ex_p`.

For `p ≥ 2¹⁶` (the independent-draw law of `thm:density:iid-prefix`) the two events differ, and
`cliqueDeletion` deletes the `ι`-closure (see `Paper.lean`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.CliqueDeletion

open Sarkozy.PartV Sarkozy.PartVLaws Sarkozy.TheoremC

variable (p : ℕ) [Fact p.Prime]

/-- **Below `2¹⁶` every labelling of the support is fixed by `ι`** (`lem:frontier:iidlocal`(iv)). -/
theorem prefixLaw_flip_support (hp : p < 2 ^ 16) {z : Slot → ZMod (p ^ (2 * digitPairs))}
    (hz : (prefixLaw p).weight z ≠ 0) (v : Slot) : z (reservedCut.flip v) = z v := by
  have hnot : ¬ 2 ^ 16 ≤ p := by omega
  unfold prefixLaw at hz
  simp only [hnot, ↓reduceIte] at hz
  unfold cliqueLaw affineChamberLaw chamberIidLaw at hz
  obtain ⟨q, _, rfl⟩ := exists_of_map_weight_ne_zero _ _ hz
  simp only [Function.comp_apply, firstChamber_flip]

/-- **On the support, below `2¹⁶`, the `ι`-closed event is the paper's event.** -/
theorem prefixLaw_symQueryEq_iff (hp : p < 2 ^ 16) {z : Slot → ZMod (p ^ (2 * digitPairs))}
    (hz : (prefixLaw p).weight z ≠ 0) :
    symQueryEq MainAnchor.paperQueries z ↔ queryEq MainAnchor.paperQueries z := by
  unfold symQueryEq queryEq
  simp only [prefixLaw_flip_support p hp hz, or_self]

/-- **Below `2¹⁶` the deleted measure of `cliqueDeletion` is the paper's exception `λ^ex_p`**
(`lem:frontier:iidlocal`(iv), `lem:frontier:iidenergy`(ii)). -/
theorem prefixLaw_restrict_eq (hp : p < 2 ^ 16) (z : Slot → ZMod (p ^ (2 * digitPairs))) :
    restrictW (prefixLaw p) (symQueryEq MainAnchor.paperQueries) z =
      restrictW (prefixLaw p) (queryEq MainAnchor.paperQueries) z := by
  unfold restrictW
  by_cases hz : (prefixLaw p).weight z = 0
  · simp only [hz, ite_self]
  · simp only [prefixLaw_symQueryEq_iff p hp hz]

end Sarkozy.CliqueDeletion
