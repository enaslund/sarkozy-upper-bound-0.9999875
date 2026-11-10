module

public import Sarkozy.F3Kernel.ScanParts

/-!
# The complete side product in cover and integrated form
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem sideCountProd_ordered (H : OrientedGraph (Fin 36)) (m rho : ℕ → ℝ)
    (h : Fin 36 → ℕ) (C : ℕ) (ord : Fin 36 → ℕ) {w s : List ℕ}
    (hwn : w.Nodup) (hsn : s.Nodup)
    (hw : ∀ u ∈ w, u < 36) (hs : ∀ u ∈ s, u < 36)
    (hc : ∀ v : Fin 36, v.val ∈ s ↔ v.val ∉ w)
    (hcover : listVertices (s.takeWhile (bit C)) = decV C)
    (ho : RecordOrder (listVertices w) (decV C) ord)
    (hr : ∀ a ∈ listVertices s, ∀ b ∈ listVertices s,
      ord a < ord b ↔ s.idxOf a.val < s.idxOf b.val) :
    sideCountProd (graphAdj H) m rho h C w [] s =
      (∏ v ∈ decV C, rho (h v + coverRowT H (decV C) ord v)) *
        ∏ v ∈ univ \ (listVertices w ∪ decV C), m (h v + ordT H ord v) := by
  let c := s.takeWhile (bit C)
  let i := s.dropWhile (bit C)
  have hsplit : c ++ i = s := List.takeWhile_append_dropWhile
  have hn : (c ++ i).Nodup := hsplit.symm ▸ hsn
  have hb : ∀ u ∈ c ++ i, u < 36 := hsplit.symm ▸ hs
  have hcomplete : ∀ v : Fin 36, v.val ∈ c ++ i ↔ v.val ∉ w := hsplit.symm ▸ hc
  have horder : ∀ a ∈ listVertices (c ++ i), ∀ b ∈ listVertices (c ++ i),
      ord a < ord b ↔ (c ++ i).idxOf a.val < (c ++ i).idxOf b.val := hsplit.symm ▸ hr
  have hi : listVertices i = univ \ (listVertices w ∪ decV C) := by
    rw [scan_integrated_vertices hn hcomplete]
    exact congrArg (fun t => univ \ (listVertices w ∪ t)) hcover
  have hfull := scan_full_nodup hwn hn hb hcomplete
  have hfullb : ∀ u ∈ c ++ w ++ i, u < 36 := by
    intro u hu
    rcases List.mem_append.mp hu with hcw | hui
    · rcases List.mem_append.mp hcw with hcu | hwu
      · exact hb u (List.mem_append_left _ hcu)
      · exact hw u hwu
    · exact hb u (List.mem_append_right _ hui)
  have hp : ∀ a ∈ listVertices (c ++ w), ∀ b ∈ listVertices i, ord a < ord b := by
    intro a ha b hb'
    refine ho.integratedLast a ?_ b (hi ▸ hb')
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_not]
    have ha' := (mem_listVertices _ _).mp ha
    rcases List.mem_append.mp ha' with hac | haw
    · exact Or.inr (hcover ▸ (mem_listVertices _ _).mpr hac)
    · exact Or.inl ((mem_listVertices _ _).mpr haw)
  have hcp := countProd_cover H rho h ord (List.nodup_append.mp hn).1
    (fun u hu => hb u (List.mem_append_left _ hu)) (scan_order_left ord horder)
  have hip := countProd_integrated H m h ord hfull hfullb
    (scan_full_complete hcomplete) hp (scan_order_right hn ord horder)
  rw [sideCountProd_split, List.nil_append]
  change countProd (graphAdj H) rho h [] c * countProd (graphAdj H) m h (c ++ w) i = _
  rw [hcp, hip, hcover, hi]

end Sarkozy.F3Kernel
