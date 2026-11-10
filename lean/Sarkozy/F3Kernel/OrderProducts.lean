module

public import Sarkozy.F3Kernel.ProductSets
public import Sarkozy.F3Kernel.GraphExponents

/-!
# Products in the mathematical vertex order

An ordered scan evaluates cover factors at earlier cover neighbours. An integrated scan,
after a prefix containing all other vertices, evaluates its factors at all earlier neighbours.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem countProd_cover (H : OrientedGraph (Fin 36)) (f : ℕ → ℝ)
    (h : Fin 36 → ℕ) (ord : Fin 36 → ℕ) {s : List ℕ}
    (hn : s.Nodup) (hs : ∀ u ∈ s, u < 36)
    (ho : ∀ a ∈ listVertices s, ∀ b ∈ listVertices s,
      ord a < ord b ↔ s.idxOf a.val < s.idxOf b.val) :
    countProd (graphAdj H) f h [] s =
      ∏ v ∈ listVertices s, f (h v + coverRowT H (listVertices s) ord v) := by
  rw [countProd_eq_finset _ f h [] hn hs]
  apply prod_congr rfl
  intro v hv
  simp only [List.nil_append]
  rw [neighbourSum_take_idxOf _ hn hs]
  apply congrArg f
  apply congrArg (h v + ·)
  unfold coverRowT coverRowEarlier nbrCount
  rw [filter_filter]
  congr 1
  apply filter_congr
  intro a ha
  exact and_congr (ho a ha v hv).symm Iff.rfl

theorem listVertices_prefix_earlier {p s : List ℕ} (ord : Fin 36 → ℕ)
    (hc : ∀ a : Fin 36, a.val ∈ p ++ s)
    (hp : ∀ a ∈ listVertices p, ∀ b ∈ listVertices s, ord a < ord b)
    (ho : ∀ a ∈ listVertices s, ∀ b ∈ listVertices s,
      ord a < ord b ↔ s.idxOf a.val < s.idxOf b.val)
    {v : Fin 36} (hv : v ∈ listVertices s) :
    listVertices (p ++ s.take (s.idxOf v.val)) = univ.filter (fun a => ord a < ord v) := by
  ext a
  simp only [mem_listVertices, List.mem_append, mem_filter, mem_univ, true_and]
  constructor
  · rintro (hap | has)
    · exact hp a (mem_listVertices _ _ |>.mpr hap) v hv
    · have ha := List.mem_of_mem_take has
      exact (ho a (mem_listVertices _ _ |>.mpr ha) v hv).mpr
        ((List.mem_take_iff_idxOf_lt ha).mp has)
  · intro hav
    rcases List.mem_append.mp (hc a) with hap | has
    · exact Or.inl hap
    · exact Or.inr ((List.mem_take_iff_idxOf_lt has).mpr
        ((ho a (mem_listVertices _ _ |>.mpr has) v hv).mp hav))

theorem countProd_integrated (H : OrientedGraph (Fin 36)) (f : ℕ → ℝ)
    (h : Fin 36 → ℕ) (ord : Fin 36 → ℕ) {p s : List ℕ}
    (hn : (p ++ s).Nodup) (hs : ∀ u ∈ p ++ s, u < 36)
    (hc : ∀ a : Fin 36, a.val ∈ p ++ s)
    (hp : ∀ a ∈ listVertices p, ∀ b ∈ listVertices s, ord a < ord b)
    (ho : ∀ a ∈ listVertices s, ∀ b ∈ listVertices s,
      ord a < ord b ↔ s.idxOf a.val < s.idxOf b.val) :
    countProd (graphAdj H) f h p s =
      ∏ v ∈ listVertices s, f (h v + ordT H ord v) := by
  have hsn : s.Nodup := (List.nodup_append.mp hn).2.1
  have hsb : ∀ u ∈ s, u < 36 := fun u hu => hs u (List.mem_append_right _ hu)
  rw [countProd_eq_finset _ f h p hsn hsb]
  apply prod_congr rfl
  intro v hv
  have hsub : List.Sublist (p ++ s.take (s.idxOf v.val)) (p ++ s) :=
    (List.Sublist.refl p).append (List.take_sublist _ _)
  rw [neighbourSum_eq_card _ (hn.sublist hsub) (fun u hu => hs u (hsub.subset hu)),
    listVertices_prefix_earlier ord hc hp ho hv]
  rfl

end Sarkozy.F3Kernel
