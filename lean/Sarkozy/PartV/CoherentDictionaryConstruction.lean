module

public import Sarkozy.PartV.CoherentRP
public import Sarkozy.PartV.LayerSwap

/-!
# Constructing the signed coherent dictionary

Equations `eq:merge-local-I-19`--`eq:merge-local-I-21`: the five supports
on each four-label core, their signed products averaged over the six chamber
symmetries, collection of equal supports, and the two successive filters.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.FiveType Sarkozy.Labellings

abbrev Vertex := ZMod 6 × Fin 2
abbrev Support := Finset Vertex

def core : Support := {(0, 0), (0, 1), (2, 0), (2, 1)}

def coreSupports : List Support :=
  [{(0, 0), (0, 1), (2, 0)}, {(0, 0), (0, 1), (2, 1)},
    {(0, 0), (2, 0), (2, 1)}, {(0, 1), (2, 0), (2, 1)}, core]

theorem coreSupports_eq :
    coreSupports.toFinset = core.powerset.filter (fun s => s.card = 3 ∨ s.card = 4) := by
  decide +kernel

def reflect (v : Vertex) : Vertex := (5 - v.1, v.2)

def act (k : Fin 6) (v : Vertex) : Vertex := (g6 k v.1, v.2)

def negative : Support := {(0, 0), (0, 1), (5, 0), (5, 1)}

/-- Twenty-five signed products, each averaged over six symmetries with weight `1/30`. -/
def raw : Dictionary :=
  (List.finRange 6).flatMap fun k => coreSupports.flatMap fun a => coreSupports.map fun b =>
    let s := a ∪ b.image reflect
    (s.image (act k), (-1 : ℚ) ^ (s ∩ negative).card / 30)

/-- Collect equal physical supports, retaining their exact signed coefficient. -/
def collected : Dictionary :=
  (raw.map Prod.fst).eraseDups.map fun s =>
    (s, ((raw.filter fun sc => sc.1 = s).map Prod.snd).sum)

def privateCore : Support := {(1, 0), (1, 1)}

def GoodCut (s : Support) : Prop :=
  (2 ≤ (s ∩ core).card ∧ 2 ≤ (s ∩ core.image reflect).card) ∨
    (2 ≤ (s ∩ privateCore).card ∧ 2 ≤ (s ∩ privateCore.image reflect).card)

instance (s : Support) : Decidable (GoodCut s) := by
  unfold GoodCut
  infer_instance

def GoodChambers (s : Support) : Prop := ∀ k : Fin 6, GoodCut (s.image (act k))

instance (s : Support) : Decidable (GoodChambers s) := by
  unfold GoodChambers
  infer_instance

def generated51 : Dictionary := collected.filter fun sc => decide (GoodChambers sc.1)

def GoodLayers (s : Support) : Prop :=
  3 ≤ (s.filter (fun v => v.2 = 0)).card ∧ 3 ≤ (s.filter (fun v => v.2 = 1)).card

instance (s : Support) : Decidable (GoodLayers s) := by
  unfold GoodLayers
  infer_instance

def generated39 : Dictionary := generated51.filter fun sc => decide (GoodLayers sc.1)

end Sarkozy.PartV.CoherentDictionary
