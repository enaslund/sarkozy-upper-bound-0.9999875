module

public import Sarkozy.EnvelopeSteps.PaperAveraging
public import Sarkozy.EnvelopeSteps.Multiplicative

@[expose] public section

/-!
# The placements of the middle records and `lem:reflection-averaging`(a) at the placements

`paper/sections/23_envelopes.tex`, `subsec:reflection-averaging`: "placing, at every `𝔅 ∈ X`, by
the map `ω(𝔅) : ℤ/6ℤ → {0, 1, 2}` … the slot `(u₀, u₁, ℓ)` receives the layer-`ℓ` label of the
object `ω(𝔅)(u₀)`", and `lem:reflection-averaging`(a).

At the reserved cut `ι` the plus half is the layer `0`, so a half labelling is the layer-`0`
labelling of the 36 slots `(u₀, u₁, 0)`, and an object triple `x : Fin 3 → Y` is placed by a
pattern `pat : ℤ/6ℤ → {0, 1, 2}` as `v ↦ x(pat(u₀))` (`midPlace`).

* **`midPlace_slotR`**: if `pat'(h − u) = β(pat(u))`, then `R_h` maps the placement by `pat'` to
  the placement by `pat` of the triple with its names permuted by `β`;
* **`midPlace_fold`** (`(F₀, F₁, F₂) ∘ R_h` of `tab:reflection`, W2's `fold_reflection_table`) and
  **`midPlace_matching`** (`E_s ∘ R_h = ψ_{h,s} ∘ E_s`, W2's `matching_reflection_table`): the two
  cases of (a) at the placements;
* **`prodPlace_slotR`**: the same over a block set, with the product placement;
* so the placement identity `ha` of `step4_averaging` holds for the product of the middle
  placements whenever it holds at every block (`ha_of_blocks`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

open Sarkozy.Labellings Sarkozy.Envelopes

/-- **The placement of an object triple by a pattern** at the reserved cut: the slot
`(u₀, u₁, 0)` receives the label of the object `pat(u₀)`. -/
def midPlace {Y : Type*} (pat : ZMod 6 → Fin 3) (x : Fin 3 → Y) : reservedCut.Half → Y :=
  fun v => x (pat v.1.1)

/-- **`R_h` moves the placements**: if `pat'(h − u) = β(pat(u))` for all `u`, then
`φ_{pat'}(x) ∘ R_h = φ_{pat}(x ∘ β)`. -/
theorem midPlace_slotR {Y : Type*} (h : ZMod 6) (pat pat' : ZMod 6 → Fin 3)
    (β : Equiv.Perm (Fin 3)) (hpat : ∀ u, pat' (h - u) = β (pat u)) (x : Fin 3 → Y) :
    (fun v => midPlace pat' x (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) =
      midPlace pat (fun o => x (β o)) := by
  funext v
  change x (pat' (h - v.1.1)) = x (β (pat v.1.1))
  rw [hpat]

/-- **`lem:reflection-averaging`(a) for the folds at the placements**: `F_j ∘ R_h = F_k` gives
`φ_{F_k}(x) ∘ R_h = φ_{F_j}(x)`. -/
theorem midPlace_fold {Y : Type*} (h : ZMod 6) (j k : Fin 3)
    (hjk : ∀ u, Labellings.fold k (chamberRefl h u) = Labellings.fold j u) (x : Fin 3 → Y) :
    (fun v => midPlace (Labellings.fold k) x
      (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) = midPlace (Labellings.fold j) x :=
  midPlace_slotR h (Labellings.fold j) (Labellings.fold k) (Equiv.refl _) (fun u => hjk u) x

/-- **`lem:reflection-averaging`(a) for the matchings at the placements**:
`E_s ∘ R_h = ψ_{h,s} ∘ E_s` gives `φ_{E_s}(x) ∘ R_h = φ_{E_s}(x ∘ ψ_{h,s})`. -/
theorem midPlace_matching {Y : Type*} (h : ZMod 6) (hh : h = 1 ∨ h = 3 ∨ h = 5) (s : Fin 2)
    (x : Fin 3 → Y) :
    (fun v => midPlace (matching s) x (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) =
      midPlace (matching s) (fun o => x (psiRefl h s o)) :=
  midPlace_slotR h (matching s) (matching s) (psiRefl h s)
    (fun u => matching_reflection_table h hh s u) x

/-- The fold rows of `tab:reflection` in the form of `midPlace_fold`: `R_5` exchanges `F₁` and
`F₂`. -/
theorem fold_R5_12 (u : ZMod 6) : Labellings.fold 2 (chamberRefl 5 u) = Labellings.fold 1 u :=
  (fold_reflection_table u).2.2.2.2

theorem fold_R5_21 (u : ZMod 6) : Labellings.fold 1 (chamberRefl 5 u) = Labellings.fold 2 u :=
  (fold_reflection_table u).2.2.2.1

variable {S : Type*} {Y : S → Type*}

/-- **The product placement and `R_h`**: if at every block `φ̄_j(x_j) ∘ R_h = φ_j(ψ_j x_j)`, then
the same holds for the product placement with `ψ = ∏_j ψ_j`. -/
theorem prodPlace_slotR (h : ZMod 6) (φ φbar : ∀ j, (Fin 3 → Y j) → (reservedCut.Half → Y j))
    (ψ : ∀ j, (Fin 3 → Y j) ≃ (Fin 3 → Y j))
    (ha : ∀ j x, (fun v => φbar j x (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) =
      φ j (ψ j x)) (x : ∀ j, Fin 3 → Y j) :
    (fun v => prodPlace reservedCut φbar x (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) =
      prodPlace reservedCut φ (Equiv.piCongrRight ψ x) := by
  funext v j
  change φbar j (x j) (halfPerm reservedCut (slotREquiv h) (slotR_half h) v) = φ j (ψ j (x j)) v
  rw [← ha j (x j)]

/-- **The placement identity of `step4_averaging` from the blocks** (`lem:reflection-averaging`(a)
at the placements): for record assignments whose placements are products of block placements
satisfying the identity at every block. -/
theorem ha_of_blocks {Ω : Type*} (h : ZMod 6) (bar : Ω → Ω)
    (φ : Ω → ∀ j, (Fin 3 → Y j) → (reservedCut.Half → Y j))
    (ψ : Ω → ∀ j, (Fin 3 → Y j) ≃ (Fin 3 → Y j))
    (ha : ∀ ω j x, (fun v => φ (bar ω) j x
      (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) = φ ω j (ψ ω j x)) :
    ∀ ω x, (fun v => prodPlace reservedCut (φ (bar ω)) x
      (halfPerm reservedCut (slotREquiv h) (slotR_half h) v)) =
      prodPlace reservedCut (φ ω) (Equiv.piCongrRight (ψ ω) x) :=
  fun ω x => prodPlace_slotR h (φ ω) (φ (bar ω)) (ψ ω) (ha ω) x

end Sarkozy.EnvelopeSteps
