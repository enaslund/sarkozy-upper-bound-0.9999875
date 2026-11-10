module

public import Sarkozy.PositiveRoots.CoherentMeanGeometry
public import Sarkozy.PositiveRoots.CoherentTraceFactor

/-! Exact collection of the physical score's invariant part into its two certified blocks. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV Sarkozy.PartV.CoherentDictionary Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators ComplexConjugate

abbrev MeanTerm := Finset (Fin 6) × Finset (Fin 6) × ℚ

def meanPairs (k : CoherentMean.Kind) : List (Fin (CoherentMean.size k) ×
    Fin (CoherentMean.size k)) :=
  (List.finRange (CoherentMean.size k)).flatMap fun i =>
    (List.finRange (CoherentMean.size k)).map fun j => (i, j)

def meanPairCoeff (k : CoherentMean.Kind) (ij : Fin (CoherentMean.size k) ×
    Fin (CoherentMean.size k)) : ℚ :=
  CoherentMatrix.coefficient (CoherentMean.index k ij.1) (CoherentMean.index k ij.2)

def meanPairTerms (k : CoherentMean.Kind) : List MeanTerm :=
  ((meanPairs k).filter fun ij => meanPairCoeff k ij ≠ 0).map fun ij =>
    (meanSupport k ij.1, meanSupport k ij.2, meanPairCoeff k ij)

theorem mean_terms_permutation :
    (dictionary39.map fun sc =>
      (chamberSupport true sc.1, chamberSupport false sc.1, sc.2)).Perm
        (meanPairTerms .core ++ meanPairTerms .mixed) := by
  decide +kernel

theorem sum_filter_coeff {α : Type*} (l : List α) (c : α → ℚ) (F : α → ℂ) :
    ((l.filter fun a => c a ≠ 0).map fun a => (c a : ℂ) * F a).sum =
      (l.map fun a => (c a : ℂ) * F a).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hc : c a = 0
    · simp only [List.filter_cons, hc, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, List.map_cons, List.sum_cons, Rat.cast_zero,
        zero_mul, zero_add]
      exact ih
    · simp only [List.filter_cons, hc, ne_eq, not_false_eq_true, decide_true,
        ite_true, List.map_cons, List.sum_cons, ih]

theorem sum_flatMap_complex {α : Type*} (l : List α) (F : α → List ℂ) :
    (l.flatMap F).sum = (l.map fun a => (F a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem meanPair_eval (k : CoherentMean.Kind) (F : Finset (Fin 6) → Finset (Fin 6) → ℂ) :
    ((meanPairTerms k).map fun t => (t.2.2 : ℂ) * F t.1 t.2.1).sum =
      ∑ i, ∑ j, (meanPairCoeff k (i, j) : ℂ) * F (meanSupport k i) (meanSupport k j) := by
  unfold meanPairTerms
  simp only [List.map_map, Function.comp_def]
  rw [sum_filter_coeff]
  unfold meanPairs
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  rw [sum_flatMap_complex]
  simp only [← Fin.sum_univ_def]

variable {p : ℕ} [Fact p.Prime]

theorem scoreMeanForm_blocks (μ : (Fin 6 → ZMod p) → ℝ) (g f : (Fin 6 → ZMod p) → ℂ) :
    scoreMeanForm μ g f = (rp p : ℂ)⁻¹ *
      (bform (CoherentMean.leading .core)
          (fun i => StarMatrix.meanStarAdj μ (meanSupport .core i) g)
          (fun i => StarMatrix.meanStarAdj μ (meanSupport .core i) f) +
        bform (CoherentMean.leading .mixed)
          (fun i => StarMatrix.meanStarAdj μ (meanSupport .mixed i) g)
          (fun i => StarMatrix.meanStarAdj μ (meanSupport .mixed i) f)) := by
  have h := (mean_terms_permutation.map fun t => (t.2.2 : ℂ) *
    (conj (StarMatrix.meanStarAdj μ t.1 g) * StarMatrix.meanStarAdj μ t.2.1 f)).sum_eq
  simp only [List.map_map, Function.comp_def, List.map_append, List.sum_append] at h
  rw [meanPair_eval .core (fun A B =>
    conj (StarMatrix.meanStarAdj μ A g) * StarMatrix.meanStarAdj μ B f),
    meanPair_eval .mixed (fun A B =>
    conj (StarMatrix.meanStarAdj μ A g) * StarMatrix.meanStarAdj μ B f)] at h
  unfold scoreMeanForm
  simp only [mul_assoc]
  rw [h]
  congr 1
  unfold bform
  unfold meanPairCoeff
  congr 1
  · apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [CoherentMean.core_leading i j]
    ring
  · apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [CoherentMean.mixed_leading i j]
    ring

end Sarkozy.PositiveRoots.CoherentFrame
