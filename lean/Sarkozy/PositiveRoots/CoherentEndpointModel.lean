module

public import Sarkozy.PositiveRoots.CoherentMeanModel

/-!
# The coherent chamber and layer matrices at `t = 12/5`

The entries come from the directed graph and the physical dictionary. The
listed active coordinates have dimensions 28 and 27 over the complex numbers.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentEndpoint

open Finset Sarkozy.PartV.CoherentDictionary Sarkozy.Labellings

inductive Cut where
  | chamber | layer
  deriving DecidableEq

def size : Cut → ℕ
  | .chamber => 28
  | .layer => 27

instance (c : Cut) : NeZero (size c) := ⟨by cases c <;> decide⟩

def active : Cut → List ℕ
  | .chamber => [1, 2, 3, 4, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18,
      19, 28, 32, 33, 34, 35, 44, 48, 49, 50, 51, 52, 56, 60]
  | .layer => [1, 2, 4, 5, 8, 10, 11, 13, 16, 17, 19, 20, 22, 25,
      26, 27, 32, 34, 37, 38, 40, 41, 44, 45, 50, 52, 54]

def index (c : Cut) (i : Fin (size c)) : Fin 64 :=
  ⟨(active c).getD i.val 0 % 64, Nat.mod_lt _ (by decide)⟩

def layerVertex (i : Fin 6) : Vertex := ((i.val : ℕ), 0)

def layerReflect (v : Vertex) : Vertex := (v.1, 1 - v.2)

def layerSign (i j : Fin 6) : ℤ :=
  (if (layerVertex i, layerReflect (layerVertex j)) ∈ (recordGraph (Fin 2)).E then 1 else 0) -
    (if (layerReflect (layerVertex j), layerVertex i) ∈ (recordGraph (Fin 2)).E then 1 else 0)

def sign (c : Cut) : Fin 6 → Fin 6 → ℤ :=
  match c with
  | .chamber => CoherentMatrix.sign
  | .layer => layerSign

def starReal (c : Cut) (i j : Fin 64) : ℤ :=
  (if 2 ≤ (CoherentMatrix.support i).card ∧ (CoherentMatrix.support j).card = 1 then
    ∑ b ∈ CoherentMatrix.support j, ∏ a ∈ CoherentMatrix.support i, sign c a b else 0) +
  (if (CoherentMatrix.support i).card = 1 ∧ 2 ≤ (CoherentMatrix.support j).card then
    ∑ a ∈ CoherentMatrix.support i, ∏ b ∈ CoherentMatrix.support j, sign c b a else 0)

def starImag (c : Cut) (i j : Fin 64) : ℤ :=
  if (CoherentMatrix.support i).card = 1 ∧ (CoherentMatrix.support j).card = 1 then
    ∑ a ∈ CoherentMatrix.support i, ∑ b ∈ CoherentMatrix.support j, sign c a b else 0

def numerator (c : Cut) : Fin 64 → Fin 64 → ℤ :=
  match c with
  | .chamber => CoherentMatrix.coefficientNumerator
  | .layer => CoherentMean.layerNumerator

def denominator : Cut → ℤ
  | .chamber => 5021000
  | .layer => 502100

def dictionaryScale : Cut → ℤ
  | .chamber => 800000
  | .layer => 80000

def diagonal : Cut → ℤ
  | .chamber => 27178673
  | .layer => 1099599

def cap : Cut → ℚ
  | .chamber => 5413 / 1000
  | .layer => 219 / 100

def modelReal (c : Cut) (i j : Fin (size c)) : ℤ :=
  denominator c * starReal c (index c i) (index c j) +
    dictionaryScale c * numerator c (index c i) (index c j) +
    if i = j then diagonal c else 0

def modelImag (c : Cut) (i j : Fin (size c)) : ℤ :=
  denominator c * starImag c (index c i) (index c j)

noncomputable def fullLeading (c : Cut) (i j : Fin 64) : ℂ :=
  Sarkozy.SpectralD.gaussian (starReal c i j) (starImag c i j) +
    (800 / 5021 : ℂ) * numerator c i j

noncomputable def leading (c : Cut) (i j : Fin (size c)) : ℂ :=
  fullLeading c (index c i) (index c j)

theorem index_injective (c : Cut) : Function.Injective (index c) := by
  cases c <;> decide +kernel

end Sarkozy.PositiveRoots.CoherentEndpoint
