module

public import Sarkozy.PartVLaws.FieldGraphs
public import Sarkozy.JointRows.StarGramCount

/-!
# The ten nontrivial conditional rows of the tail

All degrees and common-support counts below are computed on the actual
two-layer edge relation. The first object is the row, with row 1 pinned
and rows 0 and 2 free. The matching rows at E are edgeless and handled
separately by `TailCorr.MatchingE`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.PartVLaws.FieldGraphs

open Finset Sarkozy.Labellings Sarkozy.JointRows.StarOps

inductive RowCase
  | FL1 | FL2 | FF1 | FF2 | FE1 | FE2 | EL1 | EL2 | EF1 | EF2
  deriving DecidableEq

namespace RowCase

def Index : RowCase → Type
  | .FL1 | .EL1 => ZMod 6 × Fin 1
  | .FL2 | .EL2 => ZMod 6 × Fin 2
  | .FF1 | .FE1 | .EF1 => Fin 3 × Fin 1
  | .FF2 | .FE2 | .EF2 => Fin 3 × Fin 2

instance (c : RowCase) : Fintype c.Index := by cases c <;> unfold Index <;> infer_instance
instance (c : RowCase) : DecidableEq c.Index := by
  cases c <;> unfold Index <;> infer_instance

def edge : (c : RowCase) → (Fin 3 × c.Index) → (Fin 3 × c.Index) → Bool
  | .FL1 | .FL2 => twoLayerEdge typeF typeL
  | .FF1 | .FF2 => twoLayerEdge typeF typeF
  | .FE1 | .FE2 => twoLayerEdge typeF typeE
  | .EL1 | .EL2 => twoLayerEdge typeE typeL
  | .EF1 | .EF2 => twoLayerEdge typeE typeF

def crossSign (c : RowCase) (i j : c.Index) : ℤ :=
  if c.edge (0, i) (2, j) then 1 else if c.edge (2, j) (0, i) then -1 else 0

def pinSign (c : RowCase) (i j : c.Index) : ℤ :=
  if c.edge (1, j) (0, i) then 1 else if c.edge (0, i) (1, j) then -1 else 0

def rowNeighbours (c : RowCase) (i : c.Index) : Finset c.Index :=
  univ.filter fun j => c.crossSign i j ≠ 0

def colNeighbours (c : RowCase) (j : c.Index) : Finset c.Index :=
  univ.filter fun i => c.crossSign i j ≠ 0

def pins : RowCase → ℕ
  | .FL1 | .EL1 => 2
  | .FL2 | .EL2 => 4
  | .FF1 | .EF1 => 1
  | .FF2 | .EF2 => 2
  | .FE1 | .FE2 => 0

def degree : RowCase → ℕ
  | .FL1 => 3
  | .FL2 => 6
  | .FF1 | .FE1 | .EL1 | .EF2 => 2
  | .FF2 | .FE2 | .EL2 => 4
  | .EF1 => 1

def gram : RowCase → ℕ
  | .FL1 => 6
  | .FL2 => 162
  | .FF1 | .FE1 | .EL1 => 1
  | .FF2 | .FE2 | .EL2 => 26
  | .EF1 => 0
  | .EF2 => 2

def cap : RowCase → ℕ
  | .FL1 => 18
  | .FL2 => 258
  | .FF1 => 5
  | .FF2 => 30
  | .FE1 | .EF1 => 3
  | .FE2 => 8
  | .EL1 => 10
  | .EL2 => 120
  | .EF2 => 11

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem card_index (c : RowCase) : Fintype.card c.Index ≤ 12 := by
  cases c <;> decide +kernel

theorem pins_le (c : RowCase) : c.pins ≤ 4 := by cases c <;> decide +kernel

theorem crossSign_cases (c : RowCase) (i j : c.Index) :
    c.crossSign i j = 0 ∨ c.crossSign i j = 1 ∨ c.crossSign i j = -1 := by
  unfold crossSign
  split_ifs <;> norm_num

theorem pinSign_cases (c : RowCase) (i j : c.Index) :
    c.pinSign i j = 0 ∨ c.pinSign i j = 1 ∨ c.pinSign i j = -1 := by
  unfold pinSign
  split_ifs <;> norm_num

theorem no_internal_edges (c : RowCase) (a : Fin 3) (i j : c.Index) :
    c.edge (a, i) (a, j) = false := by
  revert a i j
  cases c <;> decide +kernel

theorem pins_agree (c : RowCase) (i j : c.Index) :
    c.edge (0, i) (1, j) = c.edge (2, i) (1, j) ∧
      c.edge (1, j) (0, i) = c.edge (1, j) (2, i) := by
  revert i j
  cases c <;> decide +kernel

theorem pin_degree (c : RowCase) (i : c.Index) :
    (univ.filter fun j => c.pinSign i j ≠ 0).card ≤ c.pins := by
  revert i
  cases c <;> decide +kernel

theorem row_degree (c : RowCase) (i : c.Index) : (c.rowNeighbours i).card ≤ c.degree := by
  revert i
  cases c <;> decide +kernel

theorem col_degree (c : RowCase) (j : c.Index) : (c.colNeighbours j).card ≤ c.degree := by
  revert j
  cases c <;> decide +kernel

theorem row_gram (c : RowCase) (i : c.Index) :
    ∑ i', commonSupports c.rowNeighbours i i' ≤ c.gram := by
  revert i
  cases c <;> decide +kernel

theorem col_gram (c : RowCase) (j : c.Index) :
    ∑ j', commonSupports c.colNeighbours j j' ≤ c.gram := by
  revert j
  cases c <;> decide +kernel

end RowCase

end Sarkozy.PartVLaws.FieldGraphs
