module

public import Sarkozy.F3Kernel.LeafProducts

/-!
# Numerical bounds for the mathematical record product

The checked value bounds the square root of the paper's exponent times product. The only
numerical hypotheses are upper bounds for the factor tables and the square-root-of-two
constant; the count and order identities are supplied by the preceding proofs.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem recordProduct_nonneg (H : OrientedGraph (Fin 36))
    (Fr : Finset (Fin 36 × Fin 36)) (R : LeafRecordData (Fin 36))
    {m rho : ℕ → ℝ} (hm : ∀ s, 0 ≤ m s) (hr : ∀ s, 0 ≤ rho s) :
    0 ≤ recordProduct H Fr R m rho := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (prod_nonneg (fun _ _ => hm _))
      (prod_nonneg (fun _ _ => hr _))) (prod_nonneg (fun _ _ => hm _)))
    (prod_nonneg (fun _ _ => hr _))

theorem recordProduct_pow (H : OrientedGraph (Fin 36))
    (Fr : Finset (Fin 36 × Fin 36)) (R : LeafRecordData (Fin 36))
    (m rho : ℕ → ℝ) (n : ℕ) :
    recordProduct H Fr R m rho ^ n =
      recordProduct H Fr R (fun s => m s ^ n) (fun s => rho s ^ n) := by
  simp only [recordProduct, mul_pow, prod_pow]

theorem recordProduct_sqrt (H : OrientedGraph (Fin 36))
    (Fr : Finset (Fin 36 × Fin 36)) (R : LeafRecordData (Fin 36))
    {m rho : ℕ → ℝ} (hm : ∀ s, 0 ≤ m s) (hr : ∀ s, 0 ≤ rho s) :
    recordProduct H Fr R (fun s => Real.sqrt (m s)) (fun s => Real.sqrt (rho s)) =
      Real.sqrt (recordProduct H Fr R m rho) := by
  rw [← Real.sqrt_sq (recordProduct_nonneg H Fr R
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)), recordProduct_pow]
  simp_rw [Real.sq_sqrt (hm _), Real.sq_sqrt (hr _)]

theorem LeafTrace.recordProduct_bound {G : Consts} {c : Cyl} {rec k value free : ℕ}
    (t : LeafTrace G c rec k value free) (H : OrientedGraph (Fin 36))
    (hG : AdjacencyCounts G (graphAdj H)) (hf : FreeDegreeCounts G c)
    (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am))
    (ht : Components.ValidEntry (componentTable G k) k t.pattern)
    {m rho : ℕ → ℝ} (hm : ∀ s, 0 ≤ m s) (hr : ∀ s, 0 ≤ rho s)
    (hFT : ∀ s ≤ G.d, Real.sqrt (m s) ≤ value64 (factorEntry G G.FT s))
    (hFR : ∀ s ≤ G.d, Real.sqrt (rho s) ≤ value64 (factorEntry G (rhoTable G) s))
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2) :
    Real.sqrt ((2 : ℝ) ^ (recordExp H (freePairs G c) (witV t.record.w)
      (witW t.record.w) t.record.ordX t.record.ordZ +
        2 * twoCycleCount (witnessIdx (decM c.pm) t.record.w)) *
          recordProduct H (freePairs G c) t.record m rho) ≤ value64 value := by
  have hb := t.product_bound (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
    hFT hFR hsq
  rw [t.product_eq_recordProduct H hG hf, recordProduct_sqrt H _ _ hm hr,
    t.exponent_eq_recordExp H hG hf hclass ht] at hb
  rwa [Real.sqrt_mul (by positivity)]

end Sarkozy.F3Kernel
