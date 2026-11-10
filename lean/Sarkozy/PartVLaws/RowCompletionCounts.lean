module

public import Sarkozy.PartVLaws.RowFeasible

/-! Counts of compatible free rows are the graph's sequential completion counts. -/

@[expose] public section

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows

variable {p : ℕ} [Fact p.Prime]

theorem low_completion_count (c : RowCase) (b x : c.Index → ZMod p)
    (hb : Function.Injective b) (hx : x ∈ Coll.strictSet (c.allowed b)) :
    ((Coll.strictSet (c.allowed b)).filter fun y =>
      Coll.Compatible c.finSigns (c.labelEquiv x) (c.labelEquiv y)).card =
      extCount c.rowGraph (c.pinnedDomain 0) (c.pack b x x) := by
  classical
  unfold extCount
  apply card_bij (fun y _ => c.pack b x y)
  · intro y hy
    obtain ⟨hy, hc⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨(c.pack_mem_iff b x y hb).mpr ⟨hx, hy, hc⟩, ?_⟩
    rintro ⟨a, i⟩ ha
    rcases (mem_filter.mp ha).2 with rfl | rfl <;> rfl
  · intro y _ y' _ h
    exact funext fun i => congrFun h (2, i)
  · intro z hz
    obtain ⟨hz, hagree⟩ := mem_filter.mp hz
    have h0 (i : c.Index) : z (0, i) = x i :=
      hagree (0, i) (mem_filter.mpr ⟨mem_univ _, Or.inr rfl⟩)
    have h1 (i : c.Index) : z (1, i) = b i :=
      hagree (1, i) (mem_filter.mpr ⟨mem_univ _, Or.inl rfl⟩)
    have hpack : c.pack b x (fun i => z (2, i)) = z := by
      funext ⟨a, i⟩
      fin_cases a
      · exact (h0 i).symm
      · exact (h1 i).symm
      · rfl
    have hr := (c.pack_mem_iff b x (fun i => z (2, i)) hb).mp (hpack.symm ▸ hz)
    exact ⟨fun i => z (2, i), mem_filter.mpr ⟨hr.2.1, hr.2.2⟩, hpack⟩

theorem high_completion_count (c : RowCase) (b y : c.Index → ZMod p)
    (hb : Function.Injective b) (hy : y ∈ Coll.strictSet (c.allowed b)) :
    ((Coll.strictSet (c.allowed b)).filter fun x =>
      Coll.Compatible c.finSigns (c.labelEquiv x) (c.labelEquiv y)).card =
      extCount c.rowGraph (c.pinnedDomain 2) (c.pack b y y) := by
  classical
  unfold extCount
  apply card_bij (fun x _ => c.pack b x y)
  · intro x hx
    obtain ⟨hx, hc⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨(c.pack_mem_iff b x y hb).mpr ⟨hx, hy, hc⟩, ?_⟩
    rintro ⟨a, i⟩ ha
    rcases (mem_filter.mp ha).2 with rfl | rfl <;> rfl
  · intro x _ x' _ h
    exact funext fun i => congrFun h (0, i)
  · intro z hz
    obtain ⟨hz, hagree⟩ := mem_filter.mp hz
    have h2 (i : c.Index) : z (2, i) = y i :=
      hagree (2, i) (mem_filter.mpr ⟨mem_univ _, Or.inr rfl⟩)
    have h1 (i : c.Index) : z (1, i) = b i :=
      hagree (1, i) (mem_filter.mpr ⟨mem_univ _, Or.inl rfl⟩)
    have hpack : c.pack b (fun i => z (0, i)) y = z := by
      funext ⟨a, i⟩
      fin_cases a
      · rfl
      · exact (h1 i).symm
      · exact (h2 i).symm
    have hr := (c.pack_mem_iff b (fun i => z (0, i)) y hb).mp (hpack.symm ▸ hz)
    exact ⟨fun i => z (0, i), mem_filter.mpr ⟨hr.1, hr.2.2⟩, hpack⟩

end Sarkozy.PartVLaws.FieldGraphs.RowCase
