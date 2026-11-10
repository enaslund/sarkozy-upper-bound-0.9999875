module

public import Sarkozy.PartV.CoherentDictionaryGeometry

/-!
# Exact support counts for the coherent covariance estimate

These are the six ordered-pair counts in `imp:env:coherent-full-covariance`.
The less expensive private factorization is used whenever it is valid.
The operator factorizations and diagonal estimates are separate.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

def coreProductCost (s t : Support) : ℕ :=
  16 * (if s ∩ core = t ∩ core then 2 else 1) *
    (if s ∩ core.image reflect = t ∩ core.image reflect then 2 else 1)

def privateProductCost (s t : Support) : ℕ :=
  (if s ∩ privateCore = t ∩ privateCore then 2 else 1) *
    (if s ∩ privateCore.image reflect = t ∩ privateCore.image reflect then 2 else 1)

def covarianceCase (s t : Support) : Bool × ℕ :=
  if ChamberPrivate s t then (true, privateProductCost s t) else (false, coreProductCost s t)

def covarianceCases : List (Bool × ℕ) :=
  (dictionary39.product dictionary39).map fun st => covarianceCase st.1.1 st.2.1

theorem covarianceCase_valid (sc tc : Support × ℚ)
    (hs : sc ∈ dictionary39) (ht : tc ∈ dictionary39) :
    if (covarianceCase sc.1 tc.1).1 then ChamberPrivate sc.1 tc.1
      else ChamberCore sc.1 tc.1 := by
  by_cases h : ChamberPrivate sc.1 tc.1
  · simp [covarianceCase, h]
  · simpa [covarianceCase, h] using
      (dictionary39_chamber_cases sc hs tc ht).resolve_right h

theorem covariance_core16 : covarianceCases.count (false, 16) = 804 := by decide +kernel
theorem covariance_core32 : covarianceCases.count (false, 32) = 56 := by decide +kernel
theorem covariance_core64 : covarianceCases.count (false, 64) = 41 := by decide +kernel
theorem covariance_private1 : covarianceCases.count (true, 1) = 184 := by decide +kernel
theorem covariance_private2 : covarianceCases.count (true, 2) = 240 := by decide +kernel
theorem covariance_private4 : covarianceCases.count (true, 4) = 196 := by decide +kernel

theorem covariance_cost_totals :
    (covarianceCases.map fun c => if c.1 then 0 else c.2).sum = 17280 ∧
      (covarianceCases.map fun c => if c.1 then c.2 else 0).sum = 1448 := by
  decide +kernel

theorem coherent_pure_mixed_counts :
    (dictionary39.filter fun sc => sc.1 ∩ privateCore = ∅).length = 13 ∧
      (dictionary39.filter fun sc => sc.1 ∩ privateCore ≠ ∅).length = 26 := by
  decide +kernel

/-- The `12 · 3! + 3 · 4! = 144` matching budget is computed from actual degrees. -/
theorem coherent_even_matching_budget :
    (dictionary39.map fun sc =>
      if sc.1.card % 2 = 0 then (sc.1.card / 2).factorial else 0).sum = 144 := by
  decide +kernel

end Sarkozy.PartV.CoherentDictionary
