module

public import Sarkozy.Variance.WeightedIdentityCertificate.Data

/-! The 400 terms before graph relabeling. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Sarkozy.Variance.CharacterGraph

def starGraph (a : Fin 5) (v : Fin 6) : Graph :=
  match a with
  | 0 => [(0, v), (3, v), (1, v)]
  | 1 => [(0, v), (3, v), (4, v)]
  | 2 => [(0, v), (1, v), (4, v)]
  | 3 => [(3, v), (1, v), (4, v)]
  | _ => [(0, v), (3, v), (1, v), (4, v)]

def starSign (a : Fin 5) : ℝ :=
  match a with
  | 0 => 1
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | _ => 1

def halfGraph (h : Fin 16) : Graph :=
  match h with
  | 0 => []
  | 1 => [(0, 1)]
  | 2 => [(0, 4)]
  | 3 => [(0, 1), (0, 4)]
  | 4 => [(3, 1)]
  | 5 => [(0, 1), (3, 1)]
  | 6 => [(0, 4), (3, 1)]
  | 7 => [(0, 1), (0, 4), (3, 1)]
  | 8 => [(3, 4)]
  | 9 => [(0, 1), (3, 4)]
  | 10 => [(0, 4), (3, 4)]
  | 11 => [(0, 1), (0, 4), (3, 4)]
  | 12 => [(3, 1), (3, 4)]
  | 13 => [(0, 1), (3, 1), (3, 4)]
  | 14 => [(0, 4), (3, 1), (3, 4)]
  | _ => [(0, 1), (0, 4), (3, 1), (3, 4)]

def termGraph (a b : Fin 5) (h : Fin 16) : Graph :=
  starGraph a 2 ++ starGraph b 5 ++ halfGraph h

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

noncomputable def termValue (a b : Fin 5) (h : Fin 16) : ℝ :=
  starSign a * starSign b * moment F (termGraph a b h)

end Sarkozy.Variance.WeightedIdentityCertificate
