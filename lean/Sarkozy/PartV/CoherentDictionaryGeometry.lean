module

public import Sarkozy.PartV.CoherentDictionary

/-!
# The 1,521 crossed coherent-support cases

The chamber and layer alternatives used for Cauchy--Schwarz in
`imp:local:filtered-coherent`, checked against the exact physical dictionary.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

def GoodPair {α : Type*} [DecidableEq α] (s t : Finset α) : Prop :=
  s.Nonempty ∧ t.Nonempty ∧ 2 ≤ (s ∪ t).card

instance {α : Type*} [DecidableEq α] (s t : Finset α) : Decidable (GoodPair s t) := by
  unfold GoodPair
  infer_instance

def ChamberCore (s t : Support) : Prop :=
  GoodPair (s ∩ core) (t ∩ core) ∧
    GoodPair (s ∩ core.image reflect) (t ∩ core.image reflect)

def ChamberPrivate (s t : Support) : Prop :=
  GoodPair (s ∩ privateCore) (t ∩ privateCore) ∧
    GoodPair (s ∩ privateCore.image reflect) (t ∩ privateCore.image reflect)

instance (s t : Support) : Decidable (ChamberCore s t) := by
  unfold ChamberCore
  infer_instance

instance (s t : Support) : Decidable (ChamberPrivate s t) := by
  unfold ChamberPrivate
  infer_instance

def layer (s : Support) (l : Fin 2) : Finset (ZMod 6) :=
  (s.filter fun v => v.2 = l).image Prod.fst

def evenTriangle : Finset (ZMod 6) := {0, 2, 4}
def oddTriangle : Finset (ZMod 6) := {1, 3, 5}

def LayerPair (s t : Support) (l l' : Fin 2) : Prop :=
  GoodPair (layer s l ∩ evenTriangle) (layer t l ∩ evenTriangle) ∧
    GoodPair (layer s l' ∩ oddTriangle) (layer t l' ∩ oddTriangle)

instance (s t : Support) (l l' : Fin 2) : Decidable (LayerPair s t l l') := by
  unfold LayerPair
  infer_instance

theorem dictionary39_chamber_cases : ∀ sc ∈ dictionary39, ∀ tc ∈ dictionary39,
    ChamberCore sc.1 tc.1 ∨ ChamberPrivate sc.1 tc.1 := by
  decide +kernel

theorem dictionary39_layer_cases : ∀ sc ∈ dictionary39, ∀ tc ∈ dictionary39,
    LayerPair sc.1 tc.1 0 1 ∨ LayerPair sc.1 tc.1 1 0 := by
  decide +kernel

theorem dictionary39_triangle_sizes : ∀ sc ∈ dictionary39, ∀ l : Fin 2,
    1 ≤ (layer sc.1 l ∩ evenTriangle).card ∧ (layer sc.1 l ∩ evenTriangle).card ≤ 2 ∧
      1 ≤ (layer sc.1 l ∩ oddTriangle).card ∧ (layer sc.1 l ∩ oddTriangle).card ≤ 2 ∧
      3 ≤ (layer sc.1 l).card := by
  decide +kernel

theorem dictionary39_case_counts :
    ((dictionary39.product dictionary39).filter
      (fun st => decide (ChamberCore st.1.1 st.2.1))).length = 1493 ∧
      ((dictionary39.product dictionary39).filter
        (fun st => decide (¬ChamberCore st.1.1 st.2.1))).length = 28 ∧
      ((dictionary39.product dictionary39).filter
        (fun st => decide (LayerPair st.1.1 st.2.1 0 1))).length = 1437 ∧
      ((dictionary39.product dictionary39).filter
        (fun st => decide (¬LayerPair st.1.1 st.2.1 0 1))).length = 84 := by
  decide +kernel

end Sarkozy.PartV.CoherentDictionary
