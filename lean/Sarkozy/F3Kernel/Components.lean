module

public import Sarkozy.F3Kernel.Split
public import Sarkozy.Extraction.KernelTwoCycles

/-!
# Semantic validation of the witness-component tables

The checker looks up the number of two-vertex strongly connected components in a packed
table. Here finite reachability computations are related to `Relation.ReflTransGen`, so
the table's component-size and component-count claims can be used by the extraction theorem.
-/

@[expose] public section

namespace Sarkozy.F3Kernel.Components

open Finset Sarkozy.Extraction

/-- The witness rectangle represented by an off-diagonal pattern, with its diagonal restored. -/
def rectangle (k p : ℕ) : Finset (Fin k × Fin k) :=
  univ.filter fun e => e.1 = e.2 ∨ bit p (k * e.1.val + e.2.val) = true

/-- One finite reachability update through a specified vertex. -/
def through {k : ℕ} (r : Fin k → Fin k → Bool) (v i j : Fin k) : Bool :=
  r i j || (r i v && r v j)

/-- Materialize intermediate matrices so kernel reduction shares their entries. -/
def cache {k : ℕ} (r : Fin k → Fin k → Bool) : Fin k → Fin k → Bool :=
  let rows := Vector.ofFn fun i => Vector.ofFn (r i)
  fun i j => (rows.get i).get j

@[simp] theorem cache_apply {k : ℕ} (r : Fin k → Fin k → Bool) (i j : Fin k) :
    cache r i j = r i j := by
  simp [cache, Vector.get, Vector.ofFn]
  rfl

/-- Floyd--Warshall updates. Soundness holds for every list of intermediate vertices. -/
def close {k : ℕ} (r : Fin k → Fin k → Bool) : List (Fin k) → Fin k → Fin k → Bool
  | [], i, j => r i j
  | v :: vs, i, j => close (cache (through r v)) vs i j

theorem close_contains {k : ℕ} (r : Fin k → Fin k → Bool) (vs : List (Fin k))
    {i j : Fin k} (h : r i j = true) : close r vs i j = true := by
  induction vs generalizing r with
  | nil => exact h
  | cons v vs ih =>
      apply ih
      simp only [cache_apply, through, h, Bool.true_or]

theorem close_sound {k : ℕ} (r : Fin k → Fin k → Bool) (vs : List (Fin k))
    (R : Fin k → Fin k → Prop)
    (hr : ∀ i j, r i j = true → Relation.ReflTransGen R i j)
    {i j : Fin k} (h : close r vs i j = true) : Relation.ReflTransGen R i j := by
  induction vs generalizing r with
  | nil => exact hr _ _ h
  | cons v vs ih =>
      apply ih (cache (through r v)) _ h
      intro a b hab
      simp only [cache_apply, through, Bool.or_eq_true, Bool.and_eq_true] at hab
      rcases hab with hab | hab
      · exact hr _ _ hab
      · obtain ⟨hav, hvb⟩ := hab
        exact (hr _ _ hav).trans (hr _ _ hvb)

/-- The computed reachability relation, with reflexivity built into its initial matrix. -/
def reach (k p : ℕ) : Fin k → Fin k → Bool :=
  close (fun i j => decide (i = j) || bit p (k * i.val + j.val)) (List.finRange k)

theorem reach_refl (k p : ℕ) (i : Fin k) : reach k p i i = true := by
  apply close_contains
  simp

theorem arc_reach {k p : ℕ} {i j : Fin k} (h : WitnessArc (rectangle k p) i j) :
    reach k p i j = true := by
  apply close_contains
  obtain ⟨hij, hne⟩ := h
  simpa only [rectangle, mem_filter, mem_univ, true_and, hne, false_or,
    decide_false, Bool.false_or] using hij

theorem reach_sound {k p : ℕ} {i j : Fin k} (h : reach k p i j = true) :
    Relation.ReflTransGen (WitnessArc (rectangle k p)) i j := by
  apply close_sound _ _ _ ?_ h
  intro a b hab
  by_cases he : a = b
  · subst b
    exact .refl
  · apply Relation.ReflTransGen.single
    refine ⟨?_, he⟩
    simpa only [rectangle, mem_filter, mem_univ, true_and, he, false_or,
      decide_false, Bool.false_or] using hab

def ReachTransitive (k p : ℕ) : Prop :=
  ∀ i j l : Fin k, reach k p i j = true → reach k p j l = true → reach k p i l = true

theorem reach_complete {k p : ℕ}
    (ht : ReachTransitive k p) {i j : Fin k}
    (h : Relation.ReflTransGen (WitnessArc (rectangle k p)) i j) :
    reach k p i j = true := by
  induction h with
  | refl => exact reach_refl _ _ _
  | tail _ hab ih => exact ht _ _ _ ih (arc_reach hab)

def component (k p : ℕ) (i : Fin k) : Finset (Fin k) :=
  univ.filter fun j => reach k p i j && reach k p j i

def count (k p : ℕ) : ℕ :=
  ((univ.image (component k p)).filter fun C => C.card = 2).card

theorem component_eq {k p : ℕ} (ht : ReachTransitive k p)
    (i : Fin k) : component k p i = twoCycleComponent (rectangle k p) i := by
  ext j
  simp only [component, mem_filter, mem_univ, true_and, Bool.and_eq_true,
    mem_twoCycleComponent, twoCycleMutual]
  exact and_congr ⟨reach_sound, reach_complete ht⟩ ⟨reach_sound, reach_complete ht⟩

theorem count_eq {k p : ℕ} (ht : ReachTransitive k p) :
    count k p = twoCycleCount (rectangle k p) := by
  have he : component k p = twoCycleComponent (rectangle k p) := funext (component_eq ht)
  simp only [count, twoCycleCount, he]

/-- A table entry, decoded exactly as in `leafCheck`. -/
def entry (tbl p : ℕ) : ℕ := Nat.land (Nat.shiftRight tbl (2 * p)) 3

/-- `rectPat` stores only off-diagonal bits. -/
def DiagZero (k p : ℕ) : Prop := ∀ i : Fin k, bit p (k * i.val + i.val) = false

instance (k p : ℕ) : Decidable (DiagZero k p) := inferInstanceAs (Decidable (∀ _, _))

/-- A successful table entry certifies transitivity as well as component sizes and count.
This makes the semantic proof independent of any unproved completeness claim for Warshall. -/
def ValidEntry (tbl k p : ℕ) : Prop :=
  entry tbl p ≠ 0 →
    (∀ i j l : Fin k, reach k p i j = true → reach k p j l = true → reach k p i l = true) ∧
    (∀ i : Fin k, (component k p i).card ≤ 2) ∧
    entry tbl p = 1 + count k p

instance (tbl k p : ℕ) : Decidable (ValidEntry tbl k p) :=
  inferInstanceAs (Decidable (_ → _ ∧ _ ∧ _))

theorem entry_sound {tbl k p : ℕ} (hv : ValidEntry tbl k p) (h : entry tbl p ≠ 0) :
    (∀ i, (twoCycleComponent (rectangle k p) i).card ≤ 2) ∧
      entry tbl p = 1 + twoCycleCount (rectangle k p) := by
  obtain ⟨ht, hc, hn⟩ := hv h
  simpa only [component_eq ht, count_eq ht] using And.intro hc hn

end Sarkozy.F3Kernel.Components
