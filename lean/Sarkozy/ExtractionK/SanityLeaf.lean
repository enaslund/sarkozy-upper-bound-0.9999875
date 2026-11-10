module

public import Sarkozy.ExtractionK.Sanity
public import Sarkozy.ExtractionK.Leaf

@[expose] public section

/-!
# Non-vacuity of `LeafRecordData.Valid` (`cor:extraction-leaf`(b))

The record of the sanity instance of `Sanity.lean` (`𝔽₅`, `U⁺ = Fin 2`, the class
`𝒞({(0,1)}, ∅)` of `E_× = {(0,1), (1,0)}`, witness `w₀ = (0,1)`, cover `C_x = {1}`, `C_z = ∅`, both
orders with `1` before `0`) satisfies every condition of `LeafRecordData.Valid`
(`sanity_leafRecord_valid`), the witness digraph having one vertex.
-/

open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-- The record of the sanity instance. -/
def sanityRecord : LeafRecordData (Fin 2) where
  k := 1
  w := sanityW
  Cx := {1}
  Cz := ∅
  ordX := sanityOrd
  ordZ := sanityOrd

theorem sanity_leafRecord_valid : sanityRecord.Valid sanityEx (sanityP, ∅) where
  witness := sanity_witness
  cover := sanity_cover
  injX := by decide
  injZ := by decide
  segX0 := by decide
  segZ0 := by decide
  segX1 := by decide
  segZ1 := by decide
  twoCycles i := by
    show (twoCycleComponent (witnessIdx sanityP sanityW) i).card ≤ 2
    have h : (twoCycleComponent (witnessIdx sanityP sanityW) i).card ≤ (univ : Finset (Fin 1)).card :=
      card_le_card (subset_univ _)
    simp only [card_univ, Fintype.card_fin] at h
    omega

end Sarkozy.ExtractionK
