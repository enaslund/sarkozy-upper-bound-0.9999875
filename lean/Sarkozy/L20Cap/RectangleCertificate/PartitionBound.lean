module

public import Sarkozy.L20Cap.RectangleCertificate.Coefficients

/-! Convert the indexed rectangle certificate into the extraction partition interface. -/

@[expose] public section

namespace Sarkozy.L20Cap.RectangleCertificate

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

noncomputable def recordOf (c : ClassDatum) : LeafRecordData (Fin 6) :=
  if h : ∃ i, datum i = c then record h.choose else record0

theorem recordOf_datum (i : Fin 42) : recordOf (datum i) = record i := by
  have h : ∃ j, datum j = datum i := ⟨i, rfl⟩
  rw [recordOf, dite_eq_left h]
  exact congrArg record (data_injective h.choose_spec)

theorem recordOf_valid (c : ClassDatum) (hc : c ∈ partition) :
    (recordOf c).Valid Ex8 c := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hc
  rw [recordOf_datum]
  exact records_valid i

theorem partition_coefficient_sum :
    ∑ c ∈ partition, leafCoef G6 D20Z anchor 6 Ex8 c (recordOf c) ≤ (282 : ℝ) := by
  rw [partition, sum_image (fun _ _ _ _ h => data_injective h)]
  simp_rw [recordOf_datum]
  exact coefficient_sum

theorem partition_bound (p : ℕ) :
    ∑ c ∈ partition, (Real.sqrt p)⁻¹ ^ (recordOf c).k *
      leafCoef G6 D20Z anchor 6 Ex8 c (recordOf c) ≤ 282 * (p : ℝ)⁻¹ := by
  rw [partition, sum_image (fun _ _ _ _ h => data_injective h)]
  simp_rw [recordOf_datum, records_size]
  rw [← mul_sum, inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  exact (mul_le_mul_of_nonneg_left coefficient_sum (by positivity)).trans_eq (by ring)

end Sarkozy.L20Cap.RectangleCertificate
