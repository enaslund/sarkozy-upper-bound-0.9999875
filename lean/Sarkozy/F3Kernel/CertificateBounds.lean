module

public import Sarkozy.F3Kernel.CoefficientBounds
public import Sarkozy.F3Kernel.ConcreteGraphs
public import Sarkozy.F3Kernel.RunMaskBounds

/-!
# Accepted LL20 and LL22 chunks supply bounded mathematical records

All structural, graph, count, order, and exponent hypotheses are supplied by the checker
invariants. The remaining numerical interface is precisely the real factor-table bound.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

structure GradedTableBounds (G : Consts) (H : OrientedGraph (Fin 36))
    (sgn : Fin 36 → Fin 36 → ℤ) (q : ℝ) (n : ℕ) : Prop where
  q_pos : 0 < q
  error_lt_one : gpEhat H q n < 1
  integrated : ∀ s ≤ G.d,
    Real.sqrt (grLeafFm H sgn (grGraded q) q n (gpEhat H q n) s) ≤
      value64 (factorEntry G G.FT s)
  cover : ∀ s ≤ G.d,
    Real.sqrt (grLeafFrho H sgn (grGraded q) q n (gpEhat H q n) s) ≤
      value64 (factorEntry G (rhoTable G) s)

theorem chunk_gpLeafCoef_bound {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hcoh : G.Coherent) (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) (sgn : Fin 36 → Fin 36 → ℤ)
    {q : ℝ} {n : ℕ} (hb : GradedTableBounds G H sgn q n)
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) {c : Cyl}
    (hc : c ∈ trace G toks (startState last)) {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free)
    (ht : Components.ValidEntry (componentTable G k) k t.pattern) :
    t.record.Valid (decM G.EM) (decM c.pm, decM c.am) ∧
      gpLeafCoef H sgn q n (decM G.EM) (decM c.pm, decM c.am) t.record ≤
        value64 value * grRowsR H (grGraded q) n univ ^ 2 / (1 - gpEhat H q n) ^ k := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  have hv := (run_valid hT hcoh toks (startState last) st hr
    (by simp [pend, startState])).2 c hc
  have hclass := classDatum_M_of_T hcoh hv.1 hv.2
  have hf := chunk_freeDegreeCounts hM hT hcoh h c hc
  exact ⟨t.record_valid hclass ht, t.gpLeafCoef_bound H sgn q n hG hf hclass ht
    hb.q_pos hb.error_lt_one hb.integrated hb.cover hsq⟩

theorem LL20_chunk_gpLeafCoef_bound {q : ℝ} {n : ℕ}
    (hb : GradedTableBounds LL20 GraphData.graph20 GraphData.sign20 q n)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL20 last toks = some summary) {c : Cyl}
    (hc : c ∈ trace LL20 toks (startState last)) {rec k value free : ℕ}
    (t : LeafTrace LL20 c rec k value free) :
    t.record.Valid (decM LL20.EM) (decM c.pm, decM c.am) ∧
      gpLeafCoef GraphData.graph20 GraphData.sign20 q n (decM LL20.EM)
        (decM c.pm, decM c.am) t.record ≤ value64 value *
          grRowsR GraphData.graph20 (grGraded q) n univ ^ 2 /
            (1 - gpEhat GraphData.graph20 q n) ^ k :=
  chunk_gpLeafCoef_bound LL20_matrixWordM LL20_wellFormedT LL20_coherent
    GraphData.graph20 GraphData.graph20_adjacencyCounts GraphData.sign20 hb LL20_sqrtTwo
    h hc t (LL20_validEntry t.admissible t.pattern_lt t.pattern_diagZero)

theorem LL22_chunk_gpLeafCoef_bound {q : ℝ} {n : ℕ}
    (hb : GradedTableBounds LL22 GraphData.graph22 GraphData.sign22 q n)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL22 last toks = some summary) {c : Cyl}
    (hc : c ∈ trace LL22 toks (startState last)) {rec k value free : ℕ}
    (t : LeafTrace LL22 c rec k value free) :
    t.record.Valid (decM LL22.EM) (decM c.pm, decM c.am) ∧
      gpLeafCoef GraphData.graph22 GraphData.sign22 q n (decM LL22.EM)
        (decM c.pm, decM c.am) t.record ≤ value64 value *
          grRowsR GraphData.graph22 (grGraded q) n univ ^ 2 /
            (1 - gpEhat GraphData.graph22 q n) ^ k :=
  chunk_gpLeafCoef_bound LL22_matrixWordM LL22_wellFormedT LL22_coherent
    GraphData.graph22 GraphData.graph22_adjacencyCounts GraphData.sign22 hb LL22_sqrtTwo
    h hc t (LL22_validEntry t.admissible t.pattern_lt t.pattern_diagZero)

end Sarkozy.F3Kernel
