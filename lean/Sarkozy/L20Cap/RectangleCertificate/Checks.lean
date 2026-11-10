module

public import Sarkozy.L20Cap.RectangleCertificate.Data
public import Sarkozy.F3Kernel.Components

/-! Kernel checks for the rectangle partition and its extraction records. -/

@[expose] public section

namespace Sarkozy.L20Cap.RectangleCertificate

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

theorem valid0 : record0.Valid Ex8 datum0 where
  witness := by constructor <;> decide +kernel
  cover := by constructor <;> decide +kernel
  injX := by decide +kernel
  injZ := by decide +kernel
  segX0 := by decide +kernel
  segZ0 := by decide +kernel
  segX1 := by decide +kernel
  segZ1 := by decide +kernel
  twoCycles i := (card_le_univ _).trans (by decide)

theorem data_valid : ∀ i, IsClassDatum Ex8 (datum i) := by
  unfold IsClassDatum
  decide +kernel

theorem data_injective : Function.Injective datum := by decide +kernel

theorem data_separated : ∀ i j : Fin 42, i ≠ j →
    (∃ e ∈ (datum i).1, e ∈ (datum j).2) ∨
      (∃ e ∈ (datum j).1, e ∈ (datum i).2) := by decide +kernel

theorem partition_union :
    partition.biUnion (fun c => cls Ex8 c.1 c.2) = nonstars Ex8 := by decide +kernel

theorem partition_exact : IsExactPartition Ex8 partition (nonstars Ex8) := by
  refine ⟨?_, ?_, partition_union⟩
  · intro c hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    exact data_valid i
  · intro c hc d hd hne
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    obtain ⟨j, _, rfl⟩ := mem_image.mp hd
    have hij : i ≠ j := fun h => hne (congrArg datum h)
    apply disjoint_left.mpr
    intro S hSi hSj
    obtain ⟨hi, hiA⟩ := mem_cls.mp hSi
    obtain ⟨hj, hjA⟩ := mem_cls.mp hSj
    rcases data_separated i j hij with ⟨e, hei, hej⟩ | ⟨e, hej, hei⟩
    · exact (mem_sdiff.mp (hjA (hi hei))).2 hej
    · exact (mem_sdiff.mp (hiA (hj hej))).2 hei

end Sarkozy.L20Cap.RectangleCertificate
