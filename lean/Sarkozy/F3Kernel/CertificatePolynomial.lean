module

public import Sarkozy.F3Kernel.SumBounds

/-!
# The three-term polynomial certified by a chunk chain
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

noncomputable def certificatePolynomial (H : OrientedGraph (Fin 36)) (q : ℝ) (n : ℕ)
    (cs : List CertificateChunk) (r : ℝ) : ℝ :=
  ∑ k ∈ ({2, 3, 4} : Finset ℕ),
    value64 (chunksAccumulator cs k) * completionFactor H q n k * r ^ k

theorem certificatePolynomial_eq (H : OrientedGraph (Fin 36)) (q : ℝ) (n : ℕ)
    (cs : List CertificateChunk) (r : ℝ) :
    certificatePolynomial H q n cs r =
      value64 (chunksAccumulator cs 2) * completionFactor H q n 2 * r ^ 2 +
      value64 (chunksAccumulator cs 3) * completionFactor H q n 3 * r ^ 3 +
      value64 (chunksAccumulator cs 4) * completionFactor H q n 4 * r ^ 4 := by
  norm_num [certificatePolynomial]
  ring

theorem chunks_coefficientPolynomial_le {G : Consts} (hM : MatrixWord G.EM)
    (hT : G.WellFormedT) (hcoh : G.Coherent) (htables : ValidComponentTables G)
    (H : OrientedGraph (Fin 36)) (hG : AdjacencyCounts G (graphAdj H))
    (sgn : Fin 36 → Fin 36 → ℤ) {q : ℝ} {n : ℕ} (hb : GradedTableBounds G H sgn q n)
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2) {cs : List CertificateChunk} {last : ℕ}
    (h : ChunksAccepted G last cs) {r : ℝ} (hr : 0 ≤ r) :
    (∑ d ∈ outputsFamily (chunksOutputs G last cs),
      r ^ (outputRecordFunction G (chunksOutputs G last cs) d).k *
        gpLeafCoef H sgn q n (decT G.ET) d
          (outputRecordFunction G (chunksOutputs G last cs) d)) ≤
      certificatePolynomial H q n cs r := by
  let os := chunksOutputs G last cs
  let R :=  outputRecordFunction G os
  have hsize : ∀ d ∈ outputsFamily os, (R d).k ∈ ({2, 3, 4} : Finset ℕ) := by
    intro d hd
    simpa only [mem_insert, mem_singleton] using
      outputRecords_size (chunksOutputs_nodup hT h) (fun _ ho => chunksOutputs_sound ho) hd
  change (∑ d ∈ outputsFamily os, r ^ (R d).k *
    gpLeafCoef H sgn q n (decT G.ET) d (R d)) ≤ _
  rw [← sum_fiberwise_of_maps_to (g := fun d => (R d).k)
    (t := ({2, 3, 4} : Finset ℕ)) hsize]
  apply sum_le_sum
  intro k hk
  have hk' : k = 2 ∨ k = 3 ∨ k = 4 := by
    simpa only [mem_insert, mem_singleton] using hk
  have hb' := chunks_groupedCoefficient_le hM hT hcoh htables H hG sgn hb hsq h hk'
  calc
    _ = groupedOutputCoefficient G H sgn q n os k * r ^ k := by
      rw [groupedOutputCoefficient, sum_mul]
      apply sum_congr rfl
      intro d hd
      rw [(mem_filter.mp hd).2]
      exact mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hb' (pow_nonneg hr _)

end Sarkozy.F3Kernel
