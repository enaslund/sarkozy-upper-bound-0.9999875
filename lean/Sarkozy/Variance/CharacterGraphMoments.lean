module

public import Sarkozy.Variance.WeightedIdentityCertificate.Data
public import Sarkozy.Variance.AdmissibleMoment

/-! The three irreducible graph moments agree with the paper's normalized sums. -/

@[expose] public section

namespace Sarkozy.Variance.WeightedIdentityCertificate

open Finset Sarkozy.Variance.CharacterGraph Sarkozy.L20Cap

variable {p : ℕ} [Fact p.Prime]

theorem label_expect_six (f : (Fin 6 → ZMod p) → ℝ) :
    (labelLaw (Fin 6) (ZMod p)).expect f =
      (∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ∑ d : ZMod p, ∑ e : ZMod p,
        ∑ z : ZMod p, f ![a, b, c, d, e, z]) / (p : ℝ) ^ 6 := by
  rw [label_expect_fin_succ]
  simp_rw [label_expect_fin_succ]
  simp only [labelLaw, FiniteLaw.expect_uniform, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, pow_zero, Fintype.sum_unique, Nat.cast_one, div_one]
  simp only [← sum_div, div_div]
  congr 1
  ring

theorem g5_eq : g5 (ZMod p) = WeightedMoment.mG5 p := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold g5 moment
  rw [label_expect_six]
  simp only [edgeProd, Matrix.cons_val_zero, mul_one]
  unfold WeightedMoment.mG5 WeightedMoment.sG5
  push_cast
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, ← mul_sum, mul_assoc]
  unfold chi
  field_simp

theorem g10_eq : g10 (ZMod p) = WeightedMoment.mG10 p := by
  unfold g10 moment
  rw [label_expect_six]
  unfold WeightedMoment.mG10 WeightedMoment.sG10
  push_cast
  apply congrArg (fun t : ℝ => t / (p : ℝ) ^ 6)
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro z _
  norm_num [edgeProd, chi]
  ring

theorem g12_eq : g12 (ZMod p) = WeightedMoment.mG12 p := by
  unfold g12 moment
  rw [label_expect_six]
  unfold WeightedMoment.mG12 WeightedMoment.sG12
  push_cast
  apply congrArg (fun t : ℝ => t / (p : ℝ) ^ 6)
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro z _
  norm_num [edgeProd, chi]
  ring

end Sarkozy.Variance.WeightedIdentityCertificate
