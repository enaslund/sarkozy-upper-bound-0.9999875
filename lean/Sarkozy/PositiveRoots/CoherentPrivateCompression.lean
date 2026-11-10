module

public import Sarkozy.PositiveRoots.CoherentMixedFrame

/-! Conditioning the two private labels costs exactly `1/((1-4q)(1-5q))`. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Labellings
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem privateCube_expect (f : (Fin 2 → ZMod p) → ℝ) :
    (privateCube p).expect f = (∑ a, ∑ b, f ![a, b]) / (p : ℝ) ^ 2 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs : (∑ b : Fin 2 → ZMod p, f b) = ∑ a, ∑ b, f ![a, b] := by
    calc
      _ = ∑ ab : ZMod p × ZMod p, f ![ab.1, ab.2] := by
        apply Fintype.sum_equiv (finTwoArrowEquiv (ZMod p))
        intro b
        congr 1
        funext i
        fin_cases i <;> rfl
      _ = _ := Fintype.sum_prod_type _
  unfold FiniteLaw.expect privateCube FiveType.Blocks.blockLaw
  simp only [FiniteLaw.uniform, ZMod.card, Fin.prod_univ_two, ← mul_sum]
  rw [hs]
  field_simp

theorem pairLaw_le_privateCube [Nonempty (PairT (ZMod p))]
    (f : (Fin 2 → ZMod p) → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (pairLaw (F := ZMod p)).expect (fun b => f ![b.val.1, b.val.2]) ≤
      ((p : ℝ) / (p - 1)) * (privateCube p).expect f := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [pairLaw_expect (fun b : ZMod p × ZMod p => f ![b.1, b.2]), ZMod.card,
    privateCube_expect]
  calc
    _ ≤ (∑ a, ∑ b, f ![a, b]) / ((p : ℝ) * (p - 1)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact sub_le_self _ (sum_nonneg fun a _ => hf ![a, a])
    _ = _ := by field_simp

noncomputable def privateCompression (p : ℕ) : ℝ :=
  (p : ℝ) ^ 2 / ((p - 4) * (p - 5))

omit [Fact p.Prime] in
theorem privateCompression_eq (hp6 : 6 ≤ p) :
    privateCompression p = 1 / ((1 - 4 / (p : ℝ)) * (1 - 5 / (p : ℝ))) := by
  have hp : (6 : ℝ) ≤ p := by exact_mod_cast hp6
  unfold privateCompression
  field_simp

theorem halfLaw_private_compression [Nonempty (CoreT (ZMod p))]
    [Nonempty (PairT (ZMod p))] (hp6 : 6 ≤ p)
    (φ : CoreT (ZMod p) → (Fin 2 → ZMod p) → ℝ)
    (hφ : ∀ c b, 0 ≤ φ c b) {B : ℝ}
    (hB : ∀ c, (privateCube p).expect (φ c) ≤ B) :
    (halfLaw (by simpa only [ZMod.card] using hp6)).expect
      (fun x => φ x.1 ![x.2.val.1, x.2.val.2]) ≤ privateCompression p * B := by
  have hp : (6 : ℝ) ≤ p := by exact_mod_cast hp6
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp4 : (p : ℝ) - 4 ≠ 0 := by linarith
  have hp5 : (p : ℝ) - 5 ≠ 0 := by linarith
  have hP := hP_pos (F := ZMod p) (by simpa only [ZMod.card] using hp6)
  rw [halfLaw, condLaw_expect]
  calc
    _ ≤ (prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid)⁻¹ *
        ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))).expect
          (fun x => φ x.1 ![x.2.val.1, x.2.val.2]) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hP.le)
      apply FiniteLaw.expect_mono
      intro x
      split_ifs
      · simp only [one_mul, le_refl]
      · simpa only [zero_mul] using hφ x.1 ![x.2.val.1, x.2.val.2]
    _ ≤ (prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid)⁻¹ *
        ((p : ℝ) / (p - 1) * B) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hP.le)
      rw [FiniteLaw.expect_product]
      apply FiniteLaw.expect_le_const
      intro c
      exact (pairLaw_le_privateCube (φ c) (hφ c)).trans
        (mul_le_mul_of_nonneg_left (hB c) (div_nonneg (by positivity) (by linarith)))
    _ = _ := by
      rw [hP_eq, ZMod.card, privateCompression]
      field_simp [hp0, hp1, hp4, hp5]

end Sarkozy.PositiveRoots.CoherentFrame
