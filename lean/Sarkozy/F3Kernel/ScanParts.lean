module

public import Sarkozy.F3Kernel.OrderProducts

/-!
# The cover and integrated segments of a complete scan
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

theorem scan_order_left {c i : List ℕ} (ord : Fin 36 → ℕ)
    (ho : ∀ a ∈ listVertices (c ++ i), ∀ b ∈ listVertices (c ++ i),
      ord a < ord b ↔ (c ++ i).idxOf a.val < (c ++ i).idxOf b.val) :
    ∀ a ∈ listVertices c, ∀ b ∈ listVertices c,
      ord a < ord b ↔ c.idxOf a.val < c.idxOf b.val := by
  intro a ha b hb
  have ham := (mem_listVertices _ _).mp ha
  have hbm := (mem_listVertices _ _).mp hb
  have hr := ho a (by simp [ham]) b (by simp [hbm])
  simpa only [List.idxOf_append_of_mem ham, List.idxOf_append_of_mem hbm] using hr

theorem scan_order_right {c i : List ℕ} (hn : (c ++ i).Nodup) (ord : Fin 36 → ℕ)
    (ho : ∀ a ∈ listVertices (c ++ i), ∀ b ∈ listVertices (c ++ i),
      ord a < ord b ↔ (c ++ i).idxOf a.val < (c ++ i).idxOf b.val) :
    ∀ a ∈ listVertices i, ∀ b ∈ listVertices i,
      ord a < ord b ↔ i.idxOf a.val < i.idxOf b.val := by
  intro a ha b hb
  have ham := (mem_listVertices _ _).mp ha
  have hbm := (mem_listVertices _ _).mp hb
  have hac : a.val ∉ c := fun hc => (List.nodup_append.mp hn).2.2 _ hc _ ham rfl
  have hbc : b.val ∉ c := fun hc => (List.nodup_append.mp hn).2.2 _ hc _ hbm rfl
  have hr := ho a (by simp [ham]) b (by simp [hbm])
  simpa only [List.idxOf_append_of_notMem hac, List.idxOf_append_of_notMem hbc,
    Nat.add_lt_add_iff_left] using hr

theorem scan_integrated_vertices {w c i : List ℕ} (hn : (c ++ i).Nodup)
    (hc : ∀ v : Fin 36, v.val ∈ c ++ i ↔ v.val ∉ w) :
    listVertices i = univ \ (listVertices w ∪ listVertices c) := by
  ext v
  simp only [mem_listVertices, mem_sdiff, mem_univ, true_and, mem_union, not_or]
  constructor
  · intro hv
    exact ⟨(hc v).mp (List.mem_append_right _ hv),
      fun hvc => (List.nodup_append.mp hn).2.2 _ hvc _ hv rfl⟩
  · rintro ⟨hw, hcover⟩
    exact (List.mem_append.mp ((hc v).mpr hw)).resolve_left hcover

theorem scan_full_nodup {w c i : List ℕ} (hw : w.Nodup) (hs : (c ++ i).Nodup)
    (hb : ∀ u ∈ c ++ i, u < 36)
    (hc : ∀ v : Fin 36, v.val ∈ c ++ i ↔ v.val ∉ w) :
    (c ++ w ++ i).Nodup := by
  have hn : (w ++ (c ++ i)).Nodup := by
    refine List.nodup_append.mpr ⟨hw, hs, ?_⟩
    intro a ha b hb' heq
    subst a
    exact (hc ⟨b, hb b hb'⟩).mp hb' ha
  have hp : List.Perm (c ++ w ++ i) (w ++ (c ++ i)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := c) (l₂ := w)).append_right i
  exact hp.nodup_iff.mpr hn

theorem scan_full_complete {w c i : List ℕ}
    (hc : ∀ v : Fin 36, v.val ∈ c ++ i ↔ v.val ∉ w) (v : Fin 36) :
    v.val ∈ c ++ w ++ i := by
  by_cases hw : v.val ∈ w
  · simp [hw]
  · have hs := (hc v).mpr hw
    simpa only [List.mem_append, hw, or_false] using hs

end Sarkozy.F3Kernel
