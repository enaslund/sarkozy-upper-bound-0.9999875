module

public import Sarkozy.F3Kernel.ProductionTables

/-!
# Rational bounds for the production completion factors
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

def rationalCompletion (k : ℕ) : ℚ :=
  (((1 + rationalGraded 10 36) / (1 - rationalGraded 10 36)) ^ 36) ^ 2 /
    (1 - rationalGraded 10 36) ^ k

theorem rationalCompletion_cast (k : ℕ) :
    (rationalCompletion k : ℝ) =
      (((1 + (rationalGraded 10 36 : ℝ)) / (1 - (rationalGraded 10 36 : ℝ))) ^ 36) ^ 2 /
        (1 - (rationalGraded 10 36 : ℝ)) ^ k := by
  unfold rationalCompletion
  push_cast
  rfl

theorem grRowsR_anchor_le (H : OrientedGraph (Fin 36))
    (hd : univ.sup (rowsDeg0 H) ≤ 10) :
    grRowsR H (grGraded productionAnchor) 36 univ ≤
      ((1 + (rationalGraded 10 36 : ℝ)) / (1 - (rationalGraded 10 36 : ℝ))) ^ 36 := by
  have he := gpEhat_le_rational H hd
  have he1 := rationalGraded10_lt_one
  have hrow i := grGraded_le_gpEhat H productionAnchor_pos 36 i
  have h0 i := gp_grGraded_nonneg productionAnchor_pos (rowsDeg0 H i)
    (by norm_num : (0 : ℝ) ≤ (36 : ℕ))
  calc
    _ ≤ ∏ _i : Fin 36,
        (1 + (rationalGraded 10 36 : ℝ)) / (1 - (rationalGraded 10 36 : ℝ)) := by
      apply prod_le_prod₀
      · intro i _
        exact div_nonneg (by linarith [h0 i]) (by linarith [hrow i])
      · intro i _
        exact div_le_div₀ (by linarith [h0 i, hrow i]) (by linarith [hrow i])
          (by linarith) (by linarith [hrow i])
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin]

theorem completionFactor_anchor_le (H : OrientedGraph (Fin 36))
    (hd : univ.sup (rowsDeg0 H) ≤ 10) (k : ℕ) :
    completionFactor H productionAnchor 36 k ≤ (rationalCompletion k : ℝ) := by
  rw [completionFactor, rationalCompletion_cast]
  have he := gpEhat_le_rational H hd
  have he1 := rationalGraded10_lt_one
  have hR := grRowsR_anchor_le H hd
  have hR0 : 0 ≤ grRowsR H (grGraded productionAnchor) 36 univ :=
    zero_le_one.trans (gr_rowsR_ge_one H (grErr_graded productionAnchor_pos 36)
      (fun i => (grGraded_le_gpEhat H productionAnchor_pos 36 i).trans_lt
        (gpEhat_anchor_lt_one H hd)))
  exact div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ hR0 hR 2)
    (pow_pos (by linarith) k) (pow_le_pow_left₀ (by linarith) (by linarith) k)

def rationalCoefficient (total k : ℕ) : ℚ := (total : ℚ) / 2 ^ 64 * rationalCompletion k

theorem completed_value_le (H : OrientedGraph (Fin 36))
    (hd : univ.sup (rowsDeg0 H) ≤ 10) (total k : ℕ) :
    value64 total * completionFactor H productionAnchor 36 k ≤
      (rationalCoefficient total k : ℝ) := by
  have hb := mul_le_mul_of_nonneg_left (completionFactor_anchor_le H hd k)
    (value64_nonneg total)
  simpa only [rationalCoefficient, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat, value64] using hb

theorem certificatePolynomial_le_rational (H : OrientedGraph (Fin 36))
    (hd : univ.sup (rowsDeg0 H) ≤ 10) (cs : List CertificateChunk)
    (r : ℝ) (hr : 0 ≤ r) :
    certificatePolynomial H productionAnchor 36 cs r ≤
      ∑ k ∈ ({2, 3, 4} : Finset ℕ),
        (rationalCoefficient (chunksAccumulator cs k) k : ℝ) * r ^ k := by
  apply sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (completed_value_le H hd _ k) (pow_nonneg hr k)

end Sarkozy.F3Kernel
