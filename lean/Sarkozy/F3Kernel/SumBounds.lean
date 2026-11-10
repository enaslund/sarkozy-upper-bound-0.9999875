module

public import Sarkozy.F3Kernel.RecordAssignments

/-!
# Bounding mathematical coefficient sums by certificate accumulators
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem value64_zero : value64 0 = 0 := by simp [value64]

theorem value64_add (a b : ℕ) : value64 (a + b) = value64 a + value64 b := by
  simp only [value64, Nat.cast_add, add_div]

theorem sum_value64_mul (os : List LeafOutput) (k : ℕ) (C : ℝ) :
    (os.map (fun o => value64 (o.contribution k) * C)).sum =
      value64 ((os.map (LeafOutput.contribution k)).sum) * C := by
  induction os with
  | nil => simp only [List.map_nil, List.sum_nil, value64_zero, zero_mul]
  | cons o os ih => simp only [List.map_cons, List.sum_cons, value64_add, add_mul, ih]

noncomputable def groupedOutputCoefficient (G : Consts) (H : OrientedGraph (Fin 36))
    (sgn : Fin 36 → Fin 36 → ℤ) (q : ℝ) (n : ℕ) (os : List LeafOutput) (k : ℕ) : ℝ :=
  ∑ d ∈ (outputsFamily os).filter (fun d => (outputRecordFunction G os d).k = k),
    gpLeafCoef H sgn q n (decT G.ET) d (outputRecordFunction G os d)

theorem groupedOutputCoefficient_le {G : Consts} (H : OrientedGraph (Fin 36))
    (sgn : Fin 36 → Fin 36 → ℤ) (q : ℝ) (n : ℕ) {os : List LeafOutput}
    (hn : (os.map LeafOutput.datum).Nodup)
    (hs : ∀ o ∈ os, leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free))
    (hb : ∀ o ∈ os, gpLeafCoef H sgn q n (decT G.ET) o.datum (o.mathRecord G) ≤
      value64 o.value * completionFactor H q n o.k) (k : ℕ) :
    groupedOutputCoefficient G H sgn q n os k ≤
      value64 ((os.map (LeafOutput.contribution k)).sum) * completionFactor H q n k := by
  rw [groupedOutputCoefficient, sum_filter, sum_outputsFamily hn, ← sum_value64_mul]
  apply List.sum_le_sum
  intro o ho
  rw [outputRecordFunction_apply hn ho, LeafOutput.mathRecord_size (hs o ho)]
  by_cases hk : o.k = k
  · simp only [hk, ite_true, LeafOutput.contribution]
    exact (hb o ho).trans_eq (by rw [hk])
  · simp only [hk, ite_false, LeafOutput.contribution, value64_zero, zero_mul, le_refl]

theorem chunks_groupedCoefficient_le {G : Consts} (hM : MatrixWord G.EM)
    (hT : G.WellFormedT) (hcoh : G.Coherent) (htables : ValidComponentTables G)
    (H : OrientedGraph (Fin 36)) (hG : AdjacencyCounts G (graphAdj H))
    (sgn : Fin 36 → Fin 36 → ℤ) {q : ℝ} {n : ℕ} (hb : GradedTableBounds G H sgn q n)
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2) {cs : List CertificateChunk} {last : ℕ}
    (h : ChunksAccepted G last cs) {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    groupedOutputCoefficient G H sgn q n (chunksOutputs G last cs) k ≤
      value64 (chunksAccumulator cs k) * completionFactor H q n k := by
  rw [chunks_accumulator hT h hk]
  exact groupedOutputCoefficient_le H sgn q n (chunksOutputs_nodup hT h)
    (fun _ ho => chunksOutputs_sound ho)
    (fun _ ho => (chunksOutput_bounds hM hT hcoh htables H hG sgn hb hsq h ho).2) k

end Sarkozy.F3Kernel
