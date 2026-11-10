module

public import Sarkozy.F3Kernel.LaneArithmetic
public import Sarkozy.F3Kernel.GraphData

/-!
# Packed count vectors and graph updates

Packing a finite vector is additive. Consequently the checker's adjacency updates add
exactly one to the lanes of the corresponding neighbours, with no loss from seven-bit
signature extraction when the accumulated counts are below 128.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

def packCounts {n : ℕ} (f : Fin n → ℕ) : ℕ := ∑ i, f i * 2 ^ (64 * i.val)

theorem encodeLanes_ofFn {n : ℕ} (f : Fin n → ℕ) :
    encodeLanes (List.ofFn f) = packCounts f := by
  induction n with
  | zero => simp [encodeLanes, packCounts]
  | succ n ih =>
      rw [List.ofFn_succ]
      change f 0 + 2 ^ 64 * encodeLanes (List.ofFn (fun i => f i.succ)) = _
      rw [ih]
      simp only [packCounts]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, mul_zero, pow_zero, mul_one, Fin.val_succ]
      congr 1
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro i _
      rw [Nat.mul_add, Nat.mul_one, pow_add]
      ring

theorem signature_packCounts {n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, f i < 128)
    (u : Fin n) : signature (packCounts f) u = f u := by
  rw [← encodeLanes_ofFn, signature_encode]
  · simp
  · simpa only [List.forall_mem_ofFn_iff] using hf

theorem packCounts_zero (n : ℕ) : packCounts (fun _ : Fin n => 0) = 0 := by
  simp [packCounts]

theorem packCounts_add {n : ℕ} (f g : Fin n → ℕ) :
    packCounts (fun i => f i + g i) = packCounts f + packCounts g := by
  simp only [packCounts, add_mul, sum_add_distrib]

theorem packCounts_list_sum {n : ℕ} (s : List ℕ) (f : ℕ → Fin n → ℕ) :
    packCounts (fun v => (s.map (fun u => f u v)).sum) =
      (s.map (fun u => packCounts (f u))).sum := by
  induction s with
  | nil => simp [packCounts_zero]
  | cons u s ih => simp only [List.map_cons, List.sum_cons, packCounts_add, ih]

/-- The indicator of a graph neighbour, extended by zero outside the certificate labels. -/
def neighbourCount (E : Fin 36 → Fin 36 → Prop) [DecidableRel E] (u : ℕ) (v : Fin 36) : ℕ :=
  if hu : u < 36 then if E ⟨u, hu⟩ v then 1 else 0 else 0

theorem neighbourCount_fin (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]
    (u v : Fin 36) : neighbourCount E u v = if E u v then 1 else 0 := by
  simp [neighbourCount, u.isLt]

theorem neighbourCount_le_one (E : Fin 36 → Fin 36 → Prop) [DecidableRel E]
    (u : ℕ) (v : Fin 36) : neighbourCount E u v ≤ 1 := by
  unfold neighbourCount
  split
  · split <;> omega
  · omega

def AdjacencyCounts (G : Consts) (E : Fin 36 → Fin 36 → Prop) [DecidableRel E] : Prop :=
  ∀ u : Fin 36, adj64 G u = packCounts (neighbourCount E u)

theorem LL20_adjacencyCounts : AdjacencyCounts LL20
    (fun u v => SpectralD.Root.LL20.Adj (GraphData.equiv20 u).val (GraphData.equiv20 v).val) := by
  intro u
  rw [GraphData.adj20, packCounts]
  apply sum_congr rfl
  intro v _
  rw [neighbourCount_fin]
  split <;> simp

theorem LL22_adjacencyCounts : AdjacencyCounts LL22
    (fun u v => SpectralD.Root.LL22.Adj (GraphData.equiv22 u).val (GraphData.equiv22 v).val) := by
  intro u
  rw [GraphData.adj22, packCounts]
  apply sum_congr rfl
  intro v _
  rw [neighbourCount_fin]
  split <;> simp

end Sarkozy.F3Kernel
