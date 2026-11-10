module

public import Sarkozy.F3Kernel.ProductBounds
public import Sarkozy.ExtractionK.GradedPartition

/-!
# Leaf coefficient soundness, including completion factors

Both the coarse and graded coefficients are bounded by the checked integer times the
paper's completion factor. Certifying the real factor tables remains a separate obligation.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

namespace LeafTrace

variable {G : Consts} {c : Cyl} {rec k value free : ℕ} (t : LeafTrace G c rec k value free)
variable (H : OrientedGraph (Fin 36)) (sgn : Fin 36 → Fin 36 → ℤ) (q : ℝ) (n : ℕ)
variable (hG : AdjacencyCounts G (graphAdj H)) (hf : FreeDegreeCounts G c)
variable (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am))
variable (ht : Components.ValidEntry (componentTable G k) k t.pattern)

include hG hf hclass ht

theorem leafCoef_bound (hehat : leafEhat H q n < 1)
    (hFT : ∀ s ≤ G.d, Real.sqrt (leafFm H sgn q n (leafEhat H q n) s) ≤
      value64 (factorEntry G G.FT s))
    (hFR : ∀ s ≤ G.d, Real.sqrt (leafFrho H sgn q n (leafEhat H q n) s) ≤
      value64 (factorEntry G (rhoTable G) s))
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2) :
    leafCoef H sgn q n (decM G.EM) (decM c.pm, decM c.am) t.record ≤
      value64 value * rowsR H q n univ ^ 2 / (1 - leafEhat H q n) ^ k := by
  have hb := t.recordProduct_bound H hG hf hclass ht
    (leafFm_nonneg H sgn hehat) (leafFrho_nonneg H sgn hehat) hFT hFR hsq
  unfold leafCoef
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

theorem gpLeafCoef_bound (hq : 0 < q) (hehat : gpEhat H q n < 1)
    (hFT : ∀ s ≤ G.d, Real.sqrt (grLeafFm H sgn (grGraded q) q n (gpEhat H q n) s) ≤
      value64 (factorEntry G G.FT s))
    (hFR : ∀ s ≤ G.d, Real.sqrt (grLeafFrho H sgn (grGraded q) q n (gpEhat H q n) s) ≤
      value64 (factorEntry G (rhoTable G) s))
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2) :
    gpLeafCoef H sgn q n (decM G.EM) (decM c.pm, decM c.am) t.record ≤
      value64 value * grRowsR H (grGraded q) n univ ^ 2 / (1 - gpEhat H q n) ^ k := by
  have hb := t.recordProduct_bound H hG hf hclass ht
    (gp_leafFm_nonneg H sgn hq n hehat) (gp_leafFrho_nonneg H sgn hq n hehat) hFT hFR hsq
  unfold gpLeafCoef
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

end LeafTrace

end Sarkozy.F3Kernel
