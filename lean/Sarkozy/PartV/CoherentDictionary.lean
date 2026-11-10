module

public import Sarkozy.PartV.CoherentDictionaryConstruction



@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Sarkozy.Labellings

def dictionary39 : Dictionary :=
  [
    ({(0, 0), (0, 1), (1, 0), (1, 1), (3, 0), (3, 1), (4, 0)}, -1 / 15),
    ({(0, 0), (0, 1), (1, 0), (1, 1), (3, 0), (3, 1), (4, 0), (4, 1)}, 1 / 15),
    ({(0, 0), (0, 1), (1, 0), (1, 1), (3, 0), (3, 1), (4, 1)}, -1 / 15),
    ({(0, 0), (0, 1), (1, 0), (1, 1), (3, 0), (4, 0), (4, 1)}, -1 / 15),
    ({(0, 0), (0, 1), (1, 0), (1, 1), (3, 1), (4, 0), (4, 1)}, -1 / 15),
    ({(0, 0), (0, 1), (1, 0), (3, 0), (3, 1), (4, 0), (4, 1)}, 1 / 15),
    ({(0, 0), (0, 1), (1, 0), (3, 0), (3, 1), (4, 1)}, -1 / 15),
    ({(0, 0), (0, 1), (1, 1), (3, 0), (3, 1), (4, 0)}, -1 / 15),
    ({(0, 0), (0, 1), (1, 1), (3, 0), (3, 1), (4, 0), (4, 1)}, 1 / 15),
    ({(0, 0), (0, 1), (2, 0), (2, 1), (3, 0), (3, 1), (5, 0)}, -1 / 15),
    ({(0, 0), (0, 1), (2, 0), (2, 1), (3, 0), (3, 1), (5, 0), (5, 1)}, 1 / 15),
    ({(0, 0), (0, 1), (2, 0), (2, 1), (3, 0), (3, 1), (5, 1)}, -1 / 15),
    ({(0, 0), (0, 1), (2, 0), (2, 1), (3, 0), (5, 0), (5, 1)}, 1 / 15),
    ({(0, 0), (0, 1), (2, 0), (2, 1), (3, 1), (5, 0), (5, 1)}, 1 / 15),
    ({(0, 0), (0, 1), (2, 0), (3, 0), (3, 1), (5, 0), (5, 1)}, 1 / 15),
    ({(0, 0), (0, 1), (2, 0), (3, 0), (3, 1), (5, 1)}, -1 / 15),
    ({(0, 0), (0, 1), (2, 1), (3, 0), (3, 1), (5, 0)}, -1 / 15),
    ({(0, 0), (0, 1), (2, 1), (3, 0), (3, 1), (5, 0), (5, 1)}, 1 / 15),
    ({(0, 0), (1, 0), (1, 1), (3, 0), (3, 1), (4, 0), (4, 1)}, 1 / 15),
    ({(0, 0), (1, 0), (1, 1), (3, 1), (4, 0), (4, 1)}, -1 / 15),
    ({(0, 0), (2, 0), (2, 1), (3, 0), (3, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(0, 0), (2, 0), (2, 1), (3, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(0, 1), (1, 0), (1, 1), (3, 0), (3, 1), (4, 0), (4, 1)}, 1 / 15),
    ({(0, 1), (1, 0), (1, 1), (3, 0), (4, 0), (4, 1)}, -1 / 15),
    ({(0, 1), (2, 0), (2, 1), (3, 0), (3, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(0, 1), (2, 0), (2, 1), (3, 0), (5, 0), (5, 1)}, -1 / 15),
    ({(1, 0), (1, 1), (2, 0), (2, 1), (4, 0), (4, 1), (5, 0)}, 1 / 15),
    ({(1, 0), (1, 1), (2, 0), (2, 1), (4, 0), (4, 1), (5, 0), (5, 1)}, 1 / 15),
    ({(1, 0), (1, 1), (2, 0), (2, 1), (4, 0), (4, 1), (5, 1)}, 1 / 15),
    ({(1, 0), (1, 1), (2, 0), (2, 1), (4, 0), (5, 0), (5, 1)}, 1 / 15),
    ({(1, 0), (1, 1), (2, 0), (2, 1), (4, 1), (5, 0), (5, 1)}, 1 / 15),
    ({(1, 0), (1, 1), (2, 0), (4, 0), (4, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(1, 0), (1, 1), (2, 0), (4, 0), (4, 1), (5, 1)}, -1 / 15),
    ({(1, 0), (1, 1), (2, 1), (4, 0), (4, 1), (5, 0)}, -1 / 15),
    ({(1, 0), (1, 1), (2, 1), (4, 0), (4, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(1, 0), (2, 0), (2, 1), (4, 0), (4, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(1, 0), (2, 0), (2, 1), (4, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(1, 1), (2, 0), (2, 1), (4, 0), (4, 1), (5, 0), (5, 1)}, -1 / 15),
    ({(1, 1), (2, 0), (2, 1), (4, 0), (5, 0), (5, 1)}, -1 / 15)]

theorem generated39_perm : generated39.Perm dictionary39 := by decide +kernel

theorem collected_length : collected.length = 75 := by decide +kernel

theorem generated51_length : generated51.length = 51 := by decide +kernel

theorem dictionary39_length : dictionary39.length = 39 := by decide +kernel

theorem dictionary39_invariant : dictionary39.Invariant := by
  change ∀ k : Fin 6, (dictionary39.map fun sc =>
    (sc.1.image (act k), sc.2)).Perm dictionary39
  decide +kernel

theorem dictionary39_layerSwap :
    (dictionary39.map fun sc =>
      (sc.1.image (layerSwapMap (ZMod 6)), sc.2)).Perm dictionary39 := by
  decide +kernel

theorem dictionary39_degrees :
    (dictionary39.filter fun sc => sc.1.card = 6).length = 12 ∧
      (dictionary39.filter fun sc => sc.1.card = 7).length = 24 ∧
      (dictionary39.filter fun sc => sc.1.card = 8).length = 3 := by
  decide +kernel

theorem dictionary39_squares :
    (dictionary39.map fun sc => sc.2 ^ 2).sum = (13 : ℚ) / 75 := by decide +kernel

theorem dictionary39_abs_sum :
    (dictionary39.map fun sc => |sc.2|).sum = (13 : ℚ) / 5 := by decide +kernel

theorem dictionary39_nodup : (dictionary39.map Prod.fst).Nodup := by decide +kernel

def evenCoeff (k : ℕ) : ℚ := (1 + (-1) ^ k) / 2

def leadingCoeff (k : ℕ) : ℚ := k - 1 - evenCoeff k

theorem dictionary39_graded_sums :
    (dictionary39.map fun sc => |sc.2| * leadingCoeff sc.1.card).sum = 14 ∧
      (dictionary39.map fun sc => |sc.2| * evenCoeff sc.1.card).sum = 1 := by
  decide +kernel

theorem dictionary39_supports : ∀ sc ∈ dictionary39,
    (sc.1.card = 6 ∨ sc.1.card = 7 ∨ sc.1.card = 8) ∧
      GoodChambers sc.1 ∧ GoodLayers sc.1 := by
  decide +kernel

end Sarkozy.PartV.CoherentDictionary
