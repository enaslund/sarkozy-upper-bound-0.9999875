module

public import Sarkozy.Variance.WeightedIdentityCertificate.Terms
public import Sarkozy.Variance.CharacterGraphMoments
public import Sarkozy.JointRows.StarPure

/-! Expand the concrete weighted soft count into the 400 checked graph moments. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap
open Sarkozy.JointRows.StarOps (expect_finset_sum)

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

noncomputable def softIntegrand (a b c d z : F) : ℝ :=
  chi (z - a) * chi (z - b) * chi (z - c) +
    chi (z - a) * chi (z - b) * chi (z - d) -
    chi (z - a) * chi (z - c) * chi (z - d) -
    chi (z - b) * chi (z - c) * chi (z - d) +
    chi (z - a) * chi (z - b) * chi (z - c) * chi (z - d)

theorem softIntegrand_sum (a b c d : F) :
    (∑ z : F, softIntegrand F a b c d z) = (RootMarginal.softW a b c d : ℝ) := by
  unfold softIntegrand RootMarginal.softW chi
  push_cast
  rfl

theorem softIntegrand_stars (x : Fin 6 → F) (v : Fin 6) :
    softIntegrand F (x 0) (x 3) (x 1) (x 4) (x v) =
      ∑ a : Fin 5, starSign a * edgeProd F (starGraph a v) x := by
  norm_num [softIntegrand, starGraph, starSign, edgeProd, Fin.sum_univ_succ]
  ring

noncomputable def admPolynomial (x : Fin 6 → F) : ℝ :=
  (1 + chi (x 1 - x 0)) * (1 + chi (x 4 - x 0)) *
    (1 + chi (x 1 - x 3)) * (1 + chi (x 4 - x 3))

theorem admPolynomial_expand (x : Fin 6 → F) :
    admPolynomial F x = ∑ h : Fin 16, edgeProd F (halfGraph h) x := by
  norm_num [admPolynomial, halfGraph, edgeProd, Fin.sum_univ_succ]
  ring

theorem edgeProd_append (G H : Graph) (x : Fin 6 → F) :
    edgeProd F (G ++ H) x = edgeProd F G x * edgeProd F H x := by
  induction G with
  | nil => simp only [List.nil_append, edgeProd, one_mul]
  | cons e es ih =>
    simp only [List.cons_append, edgeProd, ih, mul_assoc]

noncomputable def expandedMoment : ℝ := (labelLaw (Fin 6) F).expect (fun x =>
  admPolynomial F x * softIntegrand F (x 0) (x 3) (x 1) (x 4) (x 2) *
    softIntegrand F (x 0) (x 3) (x 1) (x 4) (x 5))

theorem expandedMoment_sum : expandedMoment F =
    ∑ a : Fin 5, ∑ b : Fin 5, ∑ h : Fin 16, termValue F a b h := by
  have hp (x : Fin 6 → F) :
      admPolynomial F x * softIntegrand F (x 0) (x 3) (x 1) (x 4) (x 2) *
        softIntegrand F (x 0) (x 3) (x 1) (x 4) (x 5) =
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ h : Fin 16,
        (starSign a * starSign b) * edgeProd F (termGraph a b h) x := by
    rw [softIntegrand_stars, softIntegrand_stars, admPolynomial_expand]
    simp only [mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro h _
    rw [termGraph, edgeProd_append, edgeProd_append]
    ring
  unfold expandedMoment
  simp_rw [hp]
  simp only [expect_finset_sum, FiniteLaw.expect_const_mul, termValue, moment]

end Sarkozy.Variance.WeightedIdentityCertificate
