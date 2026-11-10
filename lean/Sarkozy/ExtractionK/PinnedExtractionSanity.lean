module

public import Sarkozy.ExtractionK.PinnedExtraction
public import Sarkozy.ExtractionK.Sanity

@[expose] public section

/-!
# Non-vacuity of the hypotheses of `pinned_extraction` (`prop:pinned-extraction`)

A concrete instance of every hypothesis of `pinned_extraction` except the literature input
`WeilBound (ZMod 5)` (Weil's theorem, `thm:weil`(a)), which stays a hypothesis: `F = 𝔽₅`, `n = 2`
coordinates, no fixed labels and no pins (`𝓜 = ∅`, `ϖ = 0`, so `e^pin_0 = 4/5 < 1`), the cross
signs `ς₀₁ = 1`, `ς₁₀ = -1` and the class, witness (`k = 1`), cover and kernel constant
`c_ker = 1` of `Sanity.lean` (`sanitySgn`, `sanityEx`, `sanityP`, `sanityW`, `sanity_ker`),
`Δ_pin = 1`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

local instance peFactFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- No pins. -/
def pePinNone : Fin 2 → ZMod 5 → ℤ := fun _ _ => 0

theorem pe_sanity_pinCount (j : Fin 2) : pinCount pePinNone j = 0 := by
  simp [pinCount, pinRoots, pePinNone]

theorem pe_sanity_ePin : ePin (Fintype.card (ZMod 5)) 2 (∅ : Finset (ZMod 5)).card 0 < 1 := by
  rw [ZMod.card, card_empty]
  unfold ePin
  have h5 : (Real.sqrt ((5 : ℕ) : ℝ))⁻¹ ^ 2 = 1 / 5 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h5]
  norm_num

/-- **Non-vacuity of `prop:pinned-extraction`** (`pinned_extraction`): for the instance of the
module docstring every hypothesis except Weil's theorem is discharged, and the conclusion holds
for all `f`, `h`. -/
theorem pe_sanity_pinned_extraction (hW : WeilBound (ZMod 5)) (f h : (Fin 2 → ZMod 5) → ℝ) :
    |(∑ x ∈ pinLab ∅ pePinNone, ∑ y ∈ pinLab ∅ pePinNone,
        f x * (∑ S ∈ cls sanityEx sanityP ∅, ∏ e ∈ S, chiPair sanitySgn e x y) * h y) /
        ((pinLab ∅ pePinNone).card : ℝ) ^ 2| ≤
      1 * (Real.sqrt (Fintype.card (ZMod 5)))⁻¹ ^ 1 *
        Real.sqrt (2 ^ (((sanityEx \ (sanityP ∪ ∅)).filter (fun e => e.1 ∈ witV sanityW)).card +
          ((sanityEx \ (sanityP ∪ ∅)).filter (fun e => e.2 ∈ witW sanityW)).card)) *
        2 ^ (1 * 0) * peLambda0 (Fintype.card (ZMod 5)) 2 (∅ : Finset (ZMod 5)).card 0 1 *
        Real.exp (peGamma (Fintype.card (ZMod 5)) 2 (∅ : Finset (ZMod 5)).card 1 * 2 ^ 0 *
          peOc (sanityEx \ (sanityP ∪ ∅)) (witV sanityW) (witW sanityW) {1} ∅) *
        Real.sqrt ((∑ x ∈ pinLab ∅ pePinNone, f x ^ 2) / (pinLab ∅ pePinNone).card) *
        Real.sqrt ((∑ x ∈ pinLab ∅ pePinNone, h x ^ 2) / (pinLab ∅ pePinNone).card) :=
  pinned_extraction hW ∅ pePinNone (fun _ _ => Or.inl rfl) (fun _ _ h => absurd rfl h) 0
    (fun j => (pe_sanity_pinCount j).le) pe_sanity_ePin sanitySgn (by decide) (Δ := 1)
    (by decide) (by decide) sanityEx sanityP ∅ (by decide) ⟨by decide, by decide, by decide⟩
    sanityW sanity_witness {1} ∅ sanity_cover zero_le_one sanity_ker f h

end Sarkozy.ExtractionK
