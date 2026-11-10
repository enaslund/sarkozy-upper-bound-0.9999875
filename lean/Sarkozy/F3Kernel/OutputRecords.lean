module

public import Sarkozy.F3Kernel.RunSums
public import Sarkozy.F3Kernel.CertificateBounds

/-!
# Mathematical records for the leaf-output trace
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

def emptyRecord : LeafRecordData (Fin 36) where
  k := 0
  w := Fin.elim0
  Cx := ∅
  Cz := ∅
  ordX := Fin.val
  ordZ := Fin.val

noncomputable def LeafOutput.checkedTrace (G : Consts) (o : LeafOutput)
    (h : leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free)) :
    LeafTrace G o.cylinder o.encoded o.k o.value o.free := Classical.choice (leafCheck_trace h)

noncomputable def LeafOutput.mathRecord (G : Consts) (o : LeafOutput) :
    LeafRecordData (Fin 36) := by
  classical
  exact if h : leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free) then
    (o.checkedTrace G h).record else emptyRecord

theorem LeafOutput.mathRecord_eq {G : Consts} {o : LeafOutput}
    (h : leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free)) :
    o.mathRecord G = (o.checkedTrace G h).record := by
  simp only [mathRecord, dite_eq_left h]

theorem LeafOutput.mathRecord_size {G : Consts} {o : LeafOutput}
    (h : leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free)) :
    (o.mathRecord G).k = o.k := by
  rw [mathRecord_eq h]
  rfl

def ValidComponentTables (G : Consts) : Prop := ∀ k pat,
  (k = 2 ∨ k = 3 ∨ k = 4) → pat < 2 ^ (k * k) → Components.DiagZero k pat →
    Components.ValidEntry (componentTable G k) k pat

theorem LL20_validComponentTables : ValidComponentTables LL20 :=
  fun _ _ hk hp hz => LL20_validEntry hk hp hz

theorem LL22_validComponentTables : ValidComponentTables LL22 :=
  fun _ _ hk hp hz => LL22_validEntry hk hp hz

noncomputable def completionFactor (H : OrientedGraph (Fin 36)) (q : ℝ) (n k : ℕ) : ℝ :=
  grRowsR H (grGraded q) n univ ^ 2 / (1 - gpEhat H q n) ^ k

theorem completionFactor_nonneg (H : OrientedGraph (Fin 36)) (q : ℝ) (n k : ℕ)
    (he : gpEhat H q n < 1) : 0 ≤ completionFactor H q n k :=
  div_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _)

theorem chunkOutput_bounds {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hcoh : G.Coherent) (htables : ValidComponentTables G) (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) (sgn : Fin 36 → Fin 36 → ℤ)
    {q : ℝ} {n : ℕ} (hb : GradedTableBounds G H sgn q n) (hsq : Real.sqrt 2 ≤ value64 G.SQ2)
    {last : ℕ} {toks : List ℕ} {summary : Summary} (h : chunk G last toks = some summary)
    {o : LeafOutput} (ho : o ∈ leafOutputs G toks (startState last)) :
    (o.mathRecord G).Valid (decT G.ET) (dec o.cylinder) ∧
      gpLeafCoef H sgn q n (decT G.ET) (dec o.cylinder) (o.mathRecord G) ≤
        value64 o.value * completionFactor H q n o.k := by
  have hc : o.cylinder ∈ trace G toks (startState last) := by
    rw [← leafOutputs_cylinders]
    exact List.mem_map_of_mem ho
  have hl := leafOutputs_sound ho
  let t := o.checkedTrace G hl
  have ht := htables o.k t.pattern t.admissible t.pattern_lt t.pattern_diagZero
  have hbounds := chunk_gpLeafCoef_bound hM hT hcoh H hG sgn hb hsq h hc t ht
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  have hv := (run_valid hT hcoh toks (startState last) st hr
    (by simp [pend, startState])).2 o.cylinder hc
  rw [hcoh, hv.1.1, hv.1.2] at hbounds
  rw [LeafOutput.mathRecord_eq hl]
  refine ⟨hbounds.1, hbounds.2.trans_eq ?_⟩
  exact mul_div_assoc _ _ _

theorem chunksOutput_bounds {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hcoh : G.Coherent) (htables : ValidComponentTables G) (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) (sgn : Fin 36 → Fin 36 → ℤ)
    {q : ℝ} {n : ℕ} (hb : GradedTableBounds G H sgn q n) (hsq : Real.sqrt 2 ≤ value64 G.SQ2)
    {cs : List CertificateChunk} {last : ℕ} (h : ChunksAccepted G last cs)
    {o : LeafOutput} (ho : o ∈ chunksOutputs G last cs) :
    (o.mathRecord G).Valid (decT G.ET) (dec o.cylinder) ∧
      gpLeafCoef H sgn q n (decT G.ET) (dec o.cylinder) (o.mathRecord G) ≤
        value64 o.value * completionFactor H q n o.k := by
  induction cs generalizing last with
  | nil => cases ho
  | cons c cs ih =>
      rcases List.mem_append.mp ho with ho | ho
      · exact chunkOutput_bounds hM hT hcoh htables H hG sgn hb hsq h.1 ho
      · exact ih h.2 ho

end Sarkozy.F3Kernel
