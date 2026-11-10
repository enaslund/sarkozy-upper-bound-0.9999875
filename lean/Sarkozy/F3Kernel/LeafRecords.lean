module

public import Sarkozy.F3Kernel.OrderRank
public import Sarkozy.F3Kernel.LeafConsequences
public import Sarkozy.ExtractionK.Leaf

/-!
# Accepted leaves supply valid extraction records

For a class datum, successful LL20 and LL22 leaf checks now construct `LeafRecordData.Valid`:
injective witnesses, decided rectangles, vertex covers, injective orders with the required
segments, and strongly connected components of size at most two. Numerical coefficient
soundness additionally requires the signature/exponent identities and certified factor tables.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

theorem recordOrder_of_masks {k n xs r V C : ℕ} (hk : k ≤ 36) (hn : n ≤ 36)
    (hx : vmask k xs 0 = some V)
    (ho : vmask n r (Nat.lor V (FULL64 - FULL36)) = some FULL64)
    (hd : Nat.land C V = 0) :
    RecordOrder (decV V) (decV C) (orderRank (packedList k xs) (packedList n r) (decV C)) := by
  apply orderRank_recordOrder (by simpa only [packedList_length] using hk)
    (by simpa only [packedList_length] using hn)
  · intro v
    rw [vmask_order_mem ho, vmask_zero_bit hx]
    simp
  · intro v
    rw [mem_decV, vmask_zero_bit hx, decide_eq_true_eq]
  · exact decV_disjoint hd

namespace LeafTrace

variable {G : Consts} {c : Cyl} {rec k value free : ℕ} (t : LeafTrace G c rec k value free)

def ordX (_t : LeafTrace G c rec k value free) : Fin 36 → ℕ :=
  orderRank (packedList k (Record.xs rec)) (packedList (36 - k) (Record.order rec))
    (decV (Record.cx rec))

def ordY : Fin 36 → ℕ :=
  orderRank (packedList k (Record.ys rec)) (packedList (36 - k) t.rest) (decV (Record.cy rec))

include t in
theorem size_le : k ≤ 36 := by rcases t.admissible with h | h | h <;> omega

theorem witV_eq : witV t.witness = decV t.V := by
  ext v
  simpa only [witV, mem_image, mem_univ, true_and, witness] using
    (witnessOf_fst_mem t.maskX t.maskY v).symm

theorem witW_eq : witW t.witness = decV t.W := by
  ext v
  simpa only [witW, mem_image, mem_univ, true_and, witness] using
    (witnessOf_snd_mem t.maskX t.maskY v).symm

theorem orderX_valid : RecordOrder (witV t.witness) (decV (Record.cx rec)) t.ordX := by
  rw [t.witV_eq]
  exact recordOrder_of_masks t.size_le (Nat.sub_le _ _) t.maskX t.orderX_vmask t.disjX

theorem orderY_valid : RecordOrder (witW t.witness) (decV (Record.cy rec)) t.ordY := by
  rw [t.witW_eq]
  exact recordOrder_of_masks t.size_le (Nat.sub_le _ _) t.maskY t.orderY_vmask t.disjY

/-- The paper's record, constructed from a successful certificate trace. -/
def record : LeafRecordData (Fin 36) where
  k := k
  w := t.witness
  Cx := decV (Record.cx rec)
  Cz := decV (Record.cy rec)
  ordX := t.ordX
  ordZ := t.ordY

theorem record_valid (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am))
    (ht : Components.ValidEntry (componentTable G k) k t.pattern) :
    t.record.Valid (decM G.EM) (decM c.pm, decM c.am) where
  witness := t.isWitness hclass
  cover := t.isCover hclass
  injX := t.orderX_valid.injective
  injZ := t.orderY_valid.injective
  segX0 := t.orderX_valid.coverFirst
  segZ0 := t.orderY_valid.coverFirst
  segX1 := t.orderX_valid.integratedLast
  segZ1 := t.orderY_valid.integratedLast
  twoCycles := (t.components hclass ht).1

end LeafTrace

/-- A successful LL20 check supplies a valid record of the reported witness size. -/
theorem leafCheck_LL20_valid {c : Cyl} {rec k value free : ℕ}
    (hclass : IsClassDatum (decM LL20.EM) (decM c.pm, decM c.am))
    (h : leafCheck LL20 c rec = some (k, value, free)) :
    ∃ R : LeafRecordData (Fin 36), R.k = k ∧ R.Valid (decM LL20.EM) (decM c.pm, decM c.am) := by
  obtain ⟨t⟩ := leafCheck_trace h
  exact ⟨t.record, rfl,
    t.record_valid hclass (LL20_validEntry t.admissible t.pattern_lt t.pattern_diagZero)⟩

/-- A successful LL22 check supplies a valid record of the reported witness size. -/
theorem leafCheck_LL22_valid {c : Cyl} {rec k value free : ℕ}
    (hclass : IsClassDatum (decM LL22.EM) (decM c.pm, decM c.am))
    (h : leafCheck LL22 c rec = some (k, value, free)) :
    ∃ R : LeafRecordData (Fin 36), R.k = k ∧ R.Valid (decM LL22.EM) (decM c.pm, decM c.am) := by
  obtain ⟨t⟩ := leafCheck_trace h
  exact ⟨t.record, rfl,
    t.record_valid hclass (LL22_validEntry t.admissible t.pattern_lt t.pattern_diagZero)⟩

end Sarkozy.F3Kernel
