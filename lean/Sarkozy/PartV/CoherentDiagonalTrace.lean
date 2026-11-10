module

public import Sarkozy.PartV.CoherentDiagonalData
public import Sarkozy.PartV.CoherentPinTrace

/-!
# Exact one-sided diagonal traces in the distinct-half chart

Each surviving pair has trace `-1`. Distinctness is required only within
each half, allowing collisions between opposite halves. Collecting first
also accounts for all singleton cancellations.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.L20Cap

variable {p : ℕ} [Fact p.Prime]

theorem trace_pair (hp : p ≠ 2) (S : Support) (hS : S.card = 2)
    (x : Vertex → ZMod p) (hx : Set.InjOn x S) : trace S x = -1 := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hS
  have hxab : x a ≠ x b := fun h => hab (hx (by simp) (by simp) h)
  simp only [trace, prod_pair hab]
  have h := sum_chi_mul_chi (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp)
    (x a) (x b)
  simpa only [hxab, ite_false, chi] using h

theorem oneSided_of_collected (isLayer : Bool) (S : Support)
    (hS : S ∈ collectedOneSided isLayer) : OneSided isLayer S := by
  have hs := (mem_filter.mp hS).1
  simp only [supports, List.mem_toFinset, List.mem_map] at hs
  obtain ⟨sc, hsc, rfl⟩ := hs
  exact of_decide_eq_true (List.mem_filter.mp hsc).2

theorem oneSided_collect_eval (isLayer : Bool) (f : Support → ℝ) :
    dictionaryEval (oneSidedRaw isLayer) f =
      ∑ S ∈ collectedOneSided isLayer, (coefficientAt (oneSidedRaw isLayer) S : ℝ) * f S := by
  rw [← collect_eval]
  symm
  apply sum_subset (filter_subset _ _)
  intro S hS hn
  have hc : coefficientAt (oneSidedRaw isLayer) S = 0 := by
    simpa only [collectedOneSided, mem_filter, hS, true_and, not_not] using hn
  simp only [hc, Rat.cast_zero, zero_mul]

theorem oneSided_trace (hp : p ≠ 2) (isLayer : Bool) (x : Vertex → ZMod p)
    (hleft : Set.InjOn x {v | cutSide isLayer v = true})
    (hright : Set.InjOn x {v | cutSide isLayer v = false}) :
    dictionaryEval (oneSidedRaw isLayer) (fun S => trace S x / p) =
      if isLayer then (8 / 75 : ℝ) / p else -(8 / 45 : ℝ) / p := by
  have ht (S : Support) (hS : S ∈ collectedOneSided isLayer) : trace S x = -1 := by
    apply trace_pair hp S (oneSided_pairs isLayer S hS) x
    rcases (oneSided_of_collected isLayer S hS).2 with hl | hr
    · exact hleft.mono (by intro v hv; exact hl v hv)
    · exact hright.mono (by intro v hv; exact hr v hv)
  rw [oneSided_collect_eval]
  calc
    _ = ∑ S ∈ collectedOneSided isLayer,
        (coefficientAt (oneSidedRaw isLayer) S : ℝ) * (-1 / p) := by
      apply sum_congr rfl
      intro S hS
      rw [ht S hS]
    _ = (∑ S ∈ collectedOneSided isLayer,
        (coefficientAt (oneSidedRaw isLayer) S : ℝ)) * (-1 / p) := by rw [sum_mul]
    _ = _ := by
      have h := congrArg (fun q : ℚ => (q : ℝ)) (oneSided_signed_mass isLayer)
      rw [Rat.cast_sum] at h
      rw [h]
      cases isLayer <;> norm_num <;> ring

theorem oneSided_trace_bound (hp : p ≠ 2) (isLayer : Bool) (x : Vertex → ZMod p)
    (hleft : Set.InjOn x {v | cutSide isLayer v = true})
    (hright : Set.InjOn x {v | cutSide isLayer v = false}) :
    |dictionaryEval (oneSidedRaw isLayer) (fun S => trace S x / p)| ≤ (8 / 25 : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [oneSided_trace hp isLayer x hleft hright]
  cases isLayer <;> norm_num [abs_div, abs_of_pos hp0]
  all_goals exact div_le_div_of_nonneg_right (by norm_num) hp0.le

end Sarkozy.PartV.CoherentDictionary
