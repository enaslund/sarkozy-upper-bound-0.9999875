module

public import Sarkozy.F3Kernel.LaneDecoding

/-!
# Horizontal summation of the count lanes

Multiplication by the all-ones lane word forms a convolution. Every resulting lane is at
most the sum of the input lanes, and lane 35 is exactly that sum. A bound on the total
therefore excludes carries in the checker's horizontal free-edge calculation.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

theorem LANE0_eq_packCounts : LANE0 = packCounts (fun _ : Fin 36 => 1) := by
  decide +kernel

theorem lane64_packCounts {n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, f i < 2 ^ 64)
    (v : Fin n) : lane64 (packCounts f) v = f v := by
  rw [← encodeLanes_ofFn, lane64_encode _ (by simpa only [List.forall_mem_ofFn_iff] using hf)]
  simp

def laneConvolution (h : Fin 36 → ℕ) (j : Fin 71) : ℕ :=
  ∑ i, if i.val ≤ j.val ∧ j.val < i.val + 36 then h i else 0

theorem laneConvolution_le (h : Fin 36 → ℕ) (j : Fin 71) :
    laneConvolution h j ≤ ∑ i, h i := by
  apply sum_le_sum
  intro i _
  split <;> omega

theorem laneConvolution_middle (h : Fin 36 → ℕ) : laneConvolution h 35 = ∑ i, h i := by
  apply sum_congr rfl
  intro i _
  exact ite_eq_left (by change i.val ≤ 35 ∧ 35 < i.val + 36; omega)

theorem packCounts_window (i : Fin 36) (a : ℕ) :
    packCounts (fun j : Fin 71 => if i.val ≤ j.val ∧ j.val < i.val + 36 then a else 0) =
      ∑ u : Fin 36, a * 2 ^ (64 * (i.val + u.val)) := by
  unfold packCounts
  simp only [ite_mul, zero_mul]
  rw [← sum_filter]
  symm
  refine sum_bij (fun u _ => (⟨i.val + u.val, by omega⟩ : Fin 71)) ?_ ?_ ?_ ?_
  · intro u _
    simp only [mem_filter, mem_univ, true_and]
    have := u.isLt
    omega
  · intro u _ v _ he
    apply Fin.ext
    have he' := congrArg Fin.val he
    change i.val + u.val = i.val + v.val at he'
    omega
  · intro j hj
    have hj' := (mem_filter.mp hj).2
    refine ⟨⟨j.val - i.val, by omega⟩, mem_univ _, ?_⟩
    apply Fin.ext
    change i.val + (j.val - i.val) = j.val
    omega
  · intro u _
    rfl

theorem packCounts_mul_LANE0 (h : Fin 36 → ℕ) :
    packCounts h * LANE0 = packCounts (laneConvolution h) := by
  have hs : packCounts (laneConvolution h) =
      ∑ i : Fin 36, packCounts (fun j : Fin 71 =>
        if i.val ≤ j.val ∧ j.val < i.val + 36 then h i else 0) := by
    simp only [packCounts, laneConvolution, sum_mul]
    rw [sum_comm]
  rw [hs, LANE0_eq_packCounts]
  simp only [packCounts, one_mul, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  change (∑ u : Fin 36, h i * 2 ^ (64 * i.val) * 2 ^ (64 * u.val)) =
    packCounts (fun j : Fin 71 => if i.val ≤ j.val ∧ j.val < i.val + 36 then h i else 0)
  rw [packCounts_window]
  apply sum_congr rfl
  intro u _
  rw [Nat.mul_add, pow_add]
  ring

theorem lane64_mul_LANE0 (h : Fin 36 → ℕ) (hh : ∑ i, h i < 2 ^ 64) :
    lane64 (packCounts h * LANE0) 35 = ∑ i, h i := by
  rw [packCounts_mul_LANE0]
  have hb (j : Fin 71) : laneConvolution h j < 2 ^ 64 :=
    (laneConvolution_le h j).trans_lt hh
  exact (lane64_packCounts _ hb 35).trans (laneConvolution_middle h)

end Sarkozy.F3Kernel
