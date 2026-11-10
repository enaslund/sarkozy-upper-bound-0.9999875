module

public import Sarkozy.PartV.CoherentPinTrace
public import Sarkozy.PartV.DictionaryCollection

/-!
# The twenty coherent-score collections at a single collision

The pins are precisely the sixteen core/core and four private/private pairs
in `imp:env:coherent-single-pin`. All coefficients are collected directly
from the physical dictionary, including the deleted-evaluation error.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

def pinVertices : Fin 20 → Vertex × Vertex :=
  ![((0, 0), (3, 0)), ((0, 0), (3, 1)), ((0, 0), (5, 0)), ((0, 0), (5, 1)),
    ((0, 1), (3, 0)), ((0, 1), (3, 1)), ((0, 1), (5, 0)), ((0, 1), (5, 1)),
    ((2, 0), (3, 0)), ((2, 0), (3, 1)), ((2, 0), (5, 0)), ((2, 0), (5, 1)),
    ((2, 1), (3, 0)), ((2, 1), (3, 1)), ((2, 1), (5, 0)), ((2, 1), (5, 1)),
    ((1, 0), (4, 0)), ((1, 0), (4, 1)), ((1, 1), (4, 0)), ((1, 1), (4, 1))]

def pinClass (i : Fin 20) : Fin 3 :=
  if ((pinVertices i).1.1 = 0 ∧ (pinVertices i).2.1 = 5) ∨
      ((pinVertices i).1.1 = 2 ∧ (pinVertices i).2.1 = 3) then 0
  else if (pinVertices i).1.2 = (pinVertices i).2.2 then 1 else 2

def pinRaw (i : Fin 20) : Dictionary :=
  dictionary39.map fun sc =>
    (pinSupport (pinVertices i).1 (pinVertices i).2 sc.1, sc.2)

def holeMass (i : Fin 20) : ℚ :=
  (dictionary39.map fun sc =>
    if pinHole (pinVertices i).1 (pinVertices i).2 sc.1 then |sc.2| else 0).sum

def pinLeading : Fin 3 → ℚ := ![64 / 5, 10, 26 / 3]
def pinTail : Fin 3 → ℚ := ![8 / 5, 11 / 5, 31 / 15]

theorem pin_complete :
    univ.image pinVertices = core.product (core.image reflect) ∪
      privateCore.product (privateCore.image reflect) := by
  decide +kernel

theorem pin_distinct : ∀ i : Fin 20, (pinVertices i).1 ≠ (pinVertices i).2 := by
  decide +kernel

theorem pin_support_cases : ∀ i : Fin 20, ∀ sc ∈ dictionary39,
    4 ≤ (pinSupport (pinVertices i).1 (pinVertices i).2 sc.1).card ∧
      (pinVertices i).2 ∉ pinSupport (pinVertices i).1 (pinVertices i).2 sc.1 := by
  decide +kernel

theorem pin_supports (i : Fin 20) (S : Support) (hS : S ∈ supports (pinRaw i)) :
    4 ≤ S.card ∧ (pinVertices i).2 ∉ S := by
  simp only [supports, pinRaw, List.mem_toFinset, List.map_map, List.mem_map,
    Function.comp_def] at hS
  obtain ⟨sc, hsc, rfl⟩ := hS
  exact pin_support_cases i sc hsc

theorem pin_collection_00 :
    leadingMass (pinRaw 0) = pinLeading (pinClass 0) ∧
      evenMass (pinRaw 0) + holeMass 0 = pinTail (pinClass 0) := by decide +kernel

theorem pin_collection_01 :
    leadingMass (pinRaw 1) = pinLeading (pinClass 1) ∧
      evenMass (pinRaw 1) + holeMass 1 = pinTail (pinClass 1) := by decide +kernel

theorem pin_collection_02 :
    leadingMass (pinRaw 2) = pinLeading (pinClass 2) ∧
      evenMass (pinRaw 2) + holeMass 2 = pinTail (pinClass 2) := by decide +kernel

theorem pin_collection_03 :
    leadingMass (pinRaw 3) = pinLeading (pinClass 3) ∧
      evenMass (pinRaw 3) + holeMass 3 = pinTail (pinClass 3) := by decide +kernel

theorem pin_collection_04 :
    leadingMass (pinRaw 4) = pinLeading (pinClass 4) ∧
      evenMass (pinRaw 4) + holeMass 4 = pinTail (pinClass 4) := by decide +kernel

theorem pin_collection_05 :
    leadingMass (pinRaw 5) = pinLeading (pinClass 5) ∧
      evenMass (pinRaw 5) + holeMass 5 = pinTail (pinClass 5) := by decide +kernel

theorem pin_collection_06 :
    leadingMass (pinRaw 6) = pinLeading (pinClass 6) ∧
      evenMass (pinRaw 6) + holeMass 6 = pinTail (pinClass 6) := by decide +kernel

theorem pin_collection_07 :
    leadingMass (pinRaw 7) = pinLeading (pinClass 7) ∧
      evenMass (pinRaw 7) + holeMass 7 = pinTail (pinClass 7) := by decide +kernel

theorem pin_collection_08 :
    leadingMass (pinRaw 8) = pinLeading (pinClass 8) ∧
      evenMass (pinRaw 8) + holeMass 8 = pinTail (pinClass 8) := by decide +kernel

theorem pin_collection_09 :
    leadingMass (pinRaw 9) = pinLeading (pinClass 9) ∧
      evenMass (pinRaw 9) + holeMass 9 = pinTail (pinClass 9) := by decide +kernel

theorem pin_collection_10 :
    leadingMass (pinRaw 10) = pinLeading (pinClass 10) ∧
      evenMass (pinRaw 10) + holeMass 10 = pinTail (pinClass 10) := by decide +kernel

theorem pin_collection_11 :
    leadingMass (pinRaw 11) = pinLeading (pinClass 11) ∧
      evenMass (pinRaw 11) + holeMass 11 = pinTail (pinClass 11) := by decide +kernel

theorem pin_collection_12 :
    leadingMass (pinRaw 12) = pinLeading (pinClass 12) ∧
      evenMass (pinRaw 12) + holeMass 12 = pinTail (pinClass 12) := by decide +kernel

theorem pin_collection_13 :
    leadingMass (pinRaw 13) = pinLeading (pinClass 13) ∧
      evenMass (pinRaw 13) + holeMass 13 = pinTail (pinClass 13) := by decide +kernel

theorem pin_collection_14 :
    leadingMass (pinRaw 14) = pinLeading (pinClass 14) ∧
      evenMass (pinRaw 14) + holeMass 14 = pinTail (pinClass 14) := by decide +kernel

theorem pin_collection_15 :
    leadingMass (pinRaw 15) = pinLeading (pinClass 15) ∧
      evenMass (pinRaw 15) + holeMass 15 = pinTail (pinClass 15) := by decide +kernel

theorem pin_collection_16 :
    leadingMass (pinRaw 16) = pinLeading (pinClass 16) ∧
      evenMass (pinRaw 16) + holeMass 16 = pinTail (pinClass 16) := by decide +kernel

theorem pin_collection_17 :
    leadingMass (pinRaw 17) = pinLeading (pinClass 17) ∧
      evenMass (pinRaw 17) + holeMass 17 = pinTail (pinClass 17) := by decide +kernel

theorem pin_collection_18 :
    leadingMass (pinRaw 18) = pinLeading (pinClass 18) ∧
      evenMass (pinRaw 18) + holeMass 18 = pinTail (pinClass 18) := by decide +kernel

theorem pin_collection_19 :
    leadingMass (pinRaw 19) = pinLeading (pinClass 19) ∧
      evenMass (pinRaw 19) + holeMass 19 = pinTail (pinClass 19) := by decide +kernel

theorem pin_collections (i : Fin 20) :
    leadingMass (pinRaw i) = pinLeading (pinClass i) ∧
      evenMass (pinRaw i) + holeMass i = pinTail (pinClass i) := by
  fin_cases i
  · exact pin_collection_00
  · exact pin_collection_01
  · exact pin_collection_02
  · exact pin_collection_03
  · exact pin_collection_04
  · exact pin_collection_05
  · exact pin_collection_06
  · exact pin_collection_07
  · exact pin_collection_08
  · exact pin_collection_09
  · exact pin_collection_10
  · exact pin_collection_11
  · exact pin_collection_12
  · exact pin_collection_13
  · exact pin_collection_14
  · exact pin_collection_15
  · exact pin_collection_16
  · exact pin_collection_17
  · exact pin_collection_18
  · exact pin_collection_19

theorem pin_class_counts :
    (univ.filter fun i : Fin 20 => pinClass i = 0).card = 8 ∧
      (univ.filter fun i : Fin 20 => pinClass i = 1).card = 6 ∧
      (univ.filter fun i : Fin 20 => pinClass i = 2).card = 6 := by
  decide +kernel

theorem pin_private_classes :
    pinClass 16 = 1 ∧ pinClass 17 = 2 ∧ pinClass 18 = 2 ∧ pinClass 19 = 1 := by
  decide +kernel

end Sarkozy.PartV.CoherentDictionary
