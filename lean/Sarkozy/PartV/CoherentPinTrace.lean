module

public import Sarkozy.PartV.CoherentDictionaryBounds
public import Sarkozy.L20Cap.Mellin

/-!
# Exact character-trace identities at a single collision

If `x a = x b`, two occurrences of that label cancel except at the deleted
evaluation point. The remaining support omits `b`, so Weil applies whenever
the labels away from `b` are injective.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings Sarkozy.L20Cap

def pinSupport (a b : Vertex) (S : Support) : Support :=
  if b ∈ S then if a ∈ S then (S.erase a).erase b else insert a (S.erase b) else S

def pinHole (a b : Vertex) (S : Support) : Bool := decide (a ∈ S ∧ b ∈ S)

variable {p : ℕ} [Fact p.Prime]

noncomputable def evaluation (S : Support) (x : Vertex → ZMod p) (z : ZMod p) : ℝ :=
  ∏ v ∈ S, chi (z - x v)

theorem evaluation_pin (a b : Vertex) (hab : a ≠ b) (S : Support)
    (x : Vertex → ZMod p) (hx : x b = x a) (z : ZMod p) :
    evaluation S x z = evaluation (pinSupport a b S) x z -
      (if pinHole a b S ∧ z = x a then evaluation (pinSupport a b S) x z else 0) := by
  by_cases hb : b ∈ S
  · by_cases ha : a ∈ S
    · have hb' : b ∈ S.erase a := mem_erase.mpr ⟨Ne.symm hab, hb⟩
      simp only [pinSupport, hb, ha, ite_true, pinHole, decide_true,
        true_and]
      unfold evaluation
      rw [← mul_prod_erase S (fun v => chi (z - x v)) ha,
        ← mul_prod_erase (S.erase a) (fun v => chi (z - x v)) hb', hx]
      by_cases hz : z = x a
      · simp [hz, chi_zero]
      · simp only [hz, ite_false, sub_zero]
        rw [← mul_assoc, ← sq, chi_sq_of_ne (sub_ne_zero.mpr hz), one_mul]
    · have ha' : a ∉ S.erase b := not_mem_subset (erase_subset _ _) ha
      simp only [pinSupport, hb, ha, ite_true, ite_false, pinHole, false_and,
        decide_false, Bool.false_eq_true, false_and, ite_false, sub_zero]
      unfold evaluation
      rw [prod_insert ha', ← mul_prod_erase S (fun v => chi (z - x v)) hb, hx]
  · simp [pinSupport, hb, pinHole]

theorem trace_pin (a b : Vertex) (hab : a ≠ b) (S : Support)
    (x : Vertex → ZMod p) (hx : x b = x a) :
    trace S x = trace (pinSupport a b S) x -
      (if pinHole a b S then evaluation (pinSupport a b S) x (x a) else 0) := by
  change (∑ z, evaluation S x z) = (∑ z, evaluation (pinSupport a b S) x z) - _
  simp_rw [evaluation_pin a b hab S x hx, sum_sub_distrib]
  congr 1
  by_cases hh : pinHole a b S
  · simp [hh]
  · simp [hh]

theorem abs_evaluation_le (S : Support) (x : Vertex → ZMod p) (z : ZMod p) :
    |evaluation S x z| ≤ 1 := by
  unfold evaluation
  rw [abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_chi_le_one _)

theorem trace_bound_injOn (hW : WeilBound (ZMod p)) (S : Support) (hS : S.Nonempty)
    (x : Vertex → ZMod p) (hx : Set.InjOn x S) :
    |trace S x| ≤ subsetBound (Real.sqrt p) S.card := by
  have he : trace S x = (rootSum (S.image x) : ℝ) := by
    simp only [trace, rootSum, Int.cast_sum, map_prod, Int.cast_prod]
    apply sum_congr rfl
    intro z _
    rw [prod_image hx]
  rw [he]
  have h := abs_rootSum_le hW (hS.image x)
  simpa only [card_image_of_injOn hx, ZMod.card] using h

end Sarkozy.PartV.CoherentDictionary
