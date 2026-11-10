module

public import Sarkozy.F3Kernel.GraphExponents

/-!
# Free-degree sums and the complete leaf exponent

Once the two initial count vectors encode the free degrees, the entire exponent returned
by an accepted leaf equals the exponent in the paper's extraction coefficient. The graph
updates, cover transition, internal witness edges, and two-cycle correction are all included.
The remaining initial encoding obligation is stated explicitly as `FreeDegreeCounts`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem cmpHx_le_36 (Fr : Finset (Fin 36 × Fin 36)) (u : Fin 36) : cmpHx Fr u ≤ 36 := by
  exact (card_le_card (filter_subset _ _)).trans (by simp)

theorem cmpHz_le_36 (Fr : Finset (Fin 36 × Fin 36)) (u : Fin 36) : cmpHz Fr u ≤ 36 := by
  exact (card_le_card (filter_subset _ _)).trans (by simp)

theorem sum_cmpHx (Fr : Finset (Fin 36 × Fin 36)) (V : Finset (Fin 36)) :
    ∑ v ∈ V, cmpHx Fr v = (Fr.filter (fun e => e.1 ∈ V)).card := by
  have he : ∑ v ∈ V, cmpHx Fr v = ((V ×ˢ univ).filter (fun e => e ∈ Fr)).card := by
    rw [card_filter, sum_product]
    exact sum_congr rfl fun v _ => card_filter _ _
  rw [he]
  congr 1
  ext e
  simp only [mem_filter, mem_product, mem_univ, and_true]
  tauto

theorem sum_cmpHz (Fr : Finset (Fin 36 × Fin 36)) (W : Finset (Fin 36)) :
    ∑ v ∈ W, cmpHz Fr v = (Fr.filter (fun e => e.2 ∈ W)).card := by
  have he : ∑ v ∈ W, cmpHz Fr v = ((univ ×ˢ W).filter (fun e => e ∈ Fr)).card := by
    rw [card_filter, sum_product_right]
    exact sum_congr rfl fun v _ => card_filter _ _
  rw [he]
  congr 1
  ext e
  simp only [mem_filter, mem_product, mem_univ, true_and]
  tauto

def freePairs (G : Consts) (c : Cyl) : Finset (Fin 36 × Fin 36) :=
  decM G.EM \ (decM c.pm ∪ decM c.am)

/-- The precise outstanding interface for the SWAR free-degree calculation. -/
def FreeDegreeCounts (G : Consts) (c : Cyl) : Prop :=
  freeRows G c = packCounts (cmpHx (freePairs G c)) ∧
    freeCols G c = packCounts (cmpHz (freePairs G c))

namespace LeafTrace

variable {G : Consts} {c : Cyl} {rec k value free : ℕ} (t : LeafTrace G c rec k value free)

theorem freeSumX (hf : FreeDegreeCounts G c) :
    hSum (freeRows G c) k (Record.xs rec) =
      ((freePairs G c).filter (fun e => e.1 ∈ witV t.witness)).card := by
  have hw := vmask_sound t.maskX
  rw [hf.1, hSum_packCounts _ (fun v => lt_of_le_of_lt (cmpHx_le_36 _ v) (by decide))
    (fun u hu => (hw.2.1 u hu).1), sumVertices_eq_sum _ hw.1
      (fun u hu => (hw.2.1 u hu).1), listVertices_witness t.maskX, ← t.witV_eq, sum_cmpHx]

theorem freeSumY (hf : FreeDegreeCounts G c) :
    hSum (freeCols G c) k (Record.ys rec) =
      ((freePairs G c).filter (fun e => e.2 ∈ witW t.witness)).card := by
  have hw := vmask_sound t.maskY
  rw [hf.2, hSum_packCounts _ (fun v => lt_of_le_of_lt (cmpHz_le_36 _ v) (by decide))
    (fun u hu => (hw.2.1 u hu).1), sumVertices_eq_sum _ hw.1
      (fun u hu => (hw.2.1 u hu).1), listVertices_witness t.maskY, ← t.witW_eq, sum_cmpHz]

/-- Exact equality with the paper's complete exponent, including the component correction. -/
theorem exponent_eq_recordExp (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) (hf : FreeDegreeCounts G c)
    (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am))
    (ht : Components.ValidEntry (componentTable G k) k t.pattern) :
    t.exponent = recordExp H (freePairs G c) (witV t.record.w) (witW t.record.w)
      t.record.ordX t.record.ordZ + 2 * twoCycleCount (witnessIdx (decM c.pm) t.record.w) := by
  have hx := t.eX_eq_ordT H hG (cmpHx_le_36 _) hf.1
  have hy := t.eY_eq_ordT H hG (cmpHz_le_36 _) hf.2
  have hc := (t.components hclass ht).2
  unfold exponent leafExponent
  rw [t.freeSumX hf, t.freeSumY hf, hx, hy, hc]
  change _ = recordExp H (freePairs G c) (witV t.witness) (witW t.witness) t.ordX t.ordY +
    2 * twoCycleCount (witnessIdx (decM c.pm) t.witness)
  unfold recordExp
  omega

end LeafTrace

end Sarkozy.F3Kernel
