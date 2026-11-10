module

public import Sarkozy.PartV.DictionaryCollection

/-!
# Exact collection of the coherent auxiliary-diagonal terms

At either cut the one-sided symmetric differences collect to thirty pairs.
Their absolute coefficient mass is `8/25`. Singleton terms cancel before
applying trace estimates, as required in `imp:local:finite-coherent-layer`.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset
open scoped symmDiff

def diagonalRaw : Dictionary :=
  (dictionary39.product dictionary39).map fun st =>
    (st.1.1 ∆ st.2.1, st.1.2 * st.2.2)

def cutSide (isLayer : Bool) (v : Vertex) : Bool :=
  if isLayer then decide (v.2 = 0) else decide (v.1.val < 3)

def OneSided (isLayer : Bool) (S : Support) : Prop :=
  S.Nonempty ∧ ((∀ v ∈ S, cutSide isLayer v = true) ∨ (∀ v ∈ S, cutSide isLayer v = false))

instance (isLayer : Bool) (S : Support) : Decidable (OneSided isLayer S) := by
  unfold OneSided
  infer_instance

def oneSidedRaw (isLayer : Bool) : Dictionary :=
  diagonalRaw.filter fun sc => decide (OneSided isLayer sc.1)

def collectedOneSided (isLayer : Bool) : Finset Support :=
  (supports (oneSidedRaw isLayer)).filter fun S => coefficientAt (oneSidedRaw isLayer) S ≠ 0

theorem diagonal_constant : coefficientAt diagonalRaw ∅ = 13 / 75 := by decide +kernel

theorem oneSided_count (isLayer : Bool) : (collectedOneSided isLayer).card = 30 := by
  cases isLayer <;> decide +kernel

theorem oneSided_pairs_raw (isLayer : Bool) : ∀ sc ∈ oneSidedRaw isLayer,
    coefficientAt (oneSidedRaw isLayer) sc.1 = 0 ∨ sc.1.card = 2 := by
  cases isLayer <;> decide +kernel

theorem oneSided_pairs (isLayer : Bool) (S : Support) (hS : S ∈ collectedOneSided isLayer) :
    S.card = 2 := by
  obtain ⟨hs, hn⟩ := mem_filter.mp hS
  simp only [supports, List.mem_toFinset, List.mem_map] at hs
  obtain ⟨sc, hsc, rfl⟩ := hs
  exact (oneSided_pairs_raw isLayer sc hsc).resolve_left hn

theorem oneSided_absolute_mass (isLayer : Bool) :
    (∑ S ∈ collectedOneSided isLayer, |coefficientAt (oneSidedRaw isLayer) S|) = 8 / 25 := by
  cases isLayer <;> decide +kernel

theorem oneSided_signed_mass (isLayer : Bool) :
    (∑ S ∈ collectedOneSided isLayer, coefficientAt (oneSidedRaw isLayer) S) =
      if isLayer then -8 / 75 else 8 / 45 := by
  cases isLayer <;> decide +kernel

end Sarkozy.PartV.CoherentDictionary
