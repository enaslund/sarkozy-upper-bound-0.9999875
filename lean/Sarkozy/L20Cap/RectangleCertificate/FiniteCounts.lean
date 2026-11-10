module

public import Sarkozy.L20Cap.RectangleCertificate.Data
public import Sarkozy.F3Kernel.Components

/-! Computable versions of the rectangle record counts. -/

@[expose] public section

namespace Sarkozy.L20Cap.RectangleCertificate

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

def neighborCount (A : Finset (Fin 6)) (v : Fin 6) : ℕ :=
  (A.filter fun u => (u, v) ∈ G6.E ∨ (v, u) ∈ G6.E).card

theorem neighborCount_eq (A : Finset (Fin 6)) (v : Fin 6) :
    neighborCount A v = nbrCount G6 A v := rfl

def earlierCount (ord : Fin 6 → ℕ) (v : Fin 6) : ℕ :=
  neighborCount (univ.filter fun u => ord u < ord v) v

theorem earlierCount_eq (ord : Fin 6 → ℕ) (v : Fin 6) :
    earlierCount ord v = ordT G6 ord v := rfl

def finiteExponent (c : ClassDatum) (R : LeafRecordData (Fin 6)) : ℕ :=
  ((Ex8 \ (c.1 ∪ c.2)).filter fun e => e.1 ∈ witV R.w).card +
  ((Ex8 \ (c.1 ∪ c.2)).filter fun e => e.2 ∈ witW R.w).card +
  ∑ v ∈ witV R.w, earlierCount R.ordX v + ∑ v ∈ witW R.w, earlierCount R.ordZ v

theorem finiteExponent_eq (c : ClassDatum) (R : LeafRecordData (Fin 6)) :
    finiteExponent c R = recordExp G6 (Ex8 \ (c.1 ∪ c.2)) (witV R.w) (witW R.w)
      R.ordX R.ordZ := rfl

theorem two_pattern_count (a : ℕ) (ha : a = 0 ∨ a = 2 ∨ a = 4 ∨ a = 6) :
    twoCycleCount (F3Kernel.Components.rectangle 2 a) = if a = 6 then 1 else 0 := by
  rcases ha with rfl | rfl | rfl | rfl
  all_goals
    rw [← F3Kernel.Components.count_eq
      (show F3Kernel.Components.ReachTransitive _ _ from by
        unfold F3Kernel.Components.ReachTransitive
        decide +kernel)]
    decide +kernel

def smallCounts (c : ClassDatum) (R : LeafRecordData (Fin 6)) : Prop :=
  (∀ u ∈ univ \ (witV R.w ∪ R.Cx),
    earlierCount R.ordX u + (intH (Ex8 \ (c.1 ∪ c.2)) u).card ≤ 2) ∧
  (∀ b ∈ R.Cz,
    neighborCount (coverRowEarlier R.Cz R.ordZ b) b +
      (coverRowH ((Ex8 \ (c.1 ∪ c.2)).filter fun e => e.2 ∈ R.Cz) b).card ≤ 2) ∧
  (∀ u ∈ univ \ (witW R.w ∪ R.Cz),
    earlierCount R.ordZ u + (intH ((Ex8 \ (c.1 ∪ c.2)).image Prod.swap) u).card ≤ 2) ∧
  (∀ b ∈ R.Cx,
    neighborCount (coverRowEarlier R.Cx R.ordX b) b +
      (coverRowH (((Ex8 \ (c.1 ∪ c.2)).image Prod.swap).filter fun e => e.2 ∈ R.Cx) b).card ≤ 2) ∧
  (univ \ (witV R.w ∪ R.Cx)).card + R.Cz.card +
    (univ \ (witW R.w ∪ R.Cz)).card + R.Cx.card = 8

end Sarkozy.L20Cap.RectangleCertificate
