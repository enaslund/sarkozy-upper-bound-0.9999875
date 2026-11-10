module

public import Sarkozy.PositiveRoots.CoherentOffdiagPhysical

/-! The off-diagonal covariance bound on the actual accepting rectangle and induced half. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.Labellings
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def rectangleMassUpper (p : ℕ) [Fact p.Prime] : ℝ :=
  (1 + etaL (ZMod p)) ^ 2 / (1 - (p : ℝ)⁻¹)

theorem rectangleMassUpper_nonneg : 0 ≤ rectangleMassUpper p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr (inv_le_one_of_one_le₀ hp.le))

theorem rectangle_square_rows (hW : WeilBound (ZMod p)) (hp3 : p % 4 = 3)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] :
    (∀ c : CoreT (ZMod p), pairLaw.expect (fun b => Rk c b ^ 2) ≤ 256 * rectangleMassUpper p) ∧
      (∀ b : PairT (ZMod p), coreLaw.expect (fun c => Rk c b ^ 2) ≤ 256 * rectangleMassUpper p) := by
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have ha (c : CoreT (ZMod p)) : rmass c ≤ rectangleMassUpper p := by
    simpa only [rectangleMassUpper, ZMod.card] using rmass_le hm1 hF hW c
  constructor
  · intro c
    rw [rect_row_sq hm1]
    exact mul_le_mul_of_nonneg_left (ha c) (by norm_num)
  · intro b
    have he : (fun c : CoreT (ZMod p) => Rk c b ^ 2) = fun c => 256 * (Rk c b * 1) := by
      funext c
      rw [Rk_sq hm1]
      ring
    rw [he, FiniteLaw.expect_const_mul]
    have he' : coreLaw.expect (fun c : CoreT (ZMod p) => Rk c b * 1) = coreLaw.expect rmass :=
      adj_one hm1 b
    rw [he']
    exact mul_le_mul_of_nonneg_left (FiniteLaw.expect_le_const _ ha) (by norm_num)

theorem coherent_offdiag_rectangle (hW : WeilBound (ZMod p)) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (F G : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => Rk x.1 y.2 * Rk y.1 x.2 * coherentOffdiagKernel x y) F G| ≤
      (256 * rectangleMassUpper p * coherentOffdiagPrice p) *
        nrm (coreLaw.product pairLaw) F * nrm (coreLaw.product pairLaw) G := by
  obtain ⟨hrow, hcol⟩ := rectangle_square_rows hW hp3
  exact coherent_offdiag_bound hDLK hp3 hp7 Rk
    (mul_nonneg (by norm_num) rectangleMassUpper_nonneg) hrow hcol F G

omit [Fact p.Prime] in
theorem coherentOffdiagPrice_nonneg (hp7 : 7 < p) : 0 ≤ coherentOffdiagPrice p := by
  have hp : (7 : ℝ) < p := by exact_mod_cast hp7
  have hD := (coreCubeDensity_pos hp7).le
  have hfrac : 0 ≤ (p : ℝ) / (p - 1) := div_nonneg (by positivity) (by linarith)
  unfold coherentOffdiagPrice
  exact mul_nonneg (by positivity) (add_nonneg
    (mul_nonneg (by norm_num) hD) (mul_nonneg (by norm_num) hfrac))

theorem hP_inv_le_privateCompression [Nonempty (CoreT (ZMod p))]
    [Nonempty (PairT (ZMod p))] (hp6 : 6 ≤ p) :
    (prob ((coreLaw (F := ZMod p)).product pairLaw) Avoid)⁻¹ ≤ privateCompression p := by
  have hp : (6 : ℝ) ≤ p := by exact_mod_cast hp6
  have hden : 0 < ((p : ℝ) - 4) * (p - 5) := mul_pos (by linarith) (by linarith)
  rw [hP_eq, ZMod.card, privateCompression, inv_div]
  apply div_le_div_of_nonneg_right _ hden.le
  nlinarith

theorem coherent_offdiag_actual (hW : WeilBound (ZMod p)) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp7 : 7 < p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw (by rw [ZMod.card]; omega)) (halfLaw (by rw [ZMod.card]; omega))
      (fun x y => Rk x.1 y.2 * Rk y.1 x.2 * coherentOffdiagKernel x y) f f| ≤
      (256 * rectangleMassUpper p * coherentOffdiagPrice p * privateCompression p) *
        nrm (halfLaw (by rw [ZMod.card]; omega)) f ^ 2 := by
  have hp6 : 6 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have h := condLaw_abs (coreLaw.product pairLaw) Avoid (hP_pos hp6)
    (fun x y => Rk x.1 y.2 * Rk y.1 x.2 * coherentOffdiagKernel x y)
    (c := 256 * rectangleMassUpper p * coherentOffdiagPrice p)
    (fun F => by
      have hb := coherent_offdiag_rectangle hW hDLK hp3 hp7 F F
      simpa only [mul_assoc, pow_two] using hb) f
  change _ ≤ (256 * rectangleMassUpper p * coherentOffdiagPrice p) /
    prob (coreLaw.product pairLaw) Avoid * nrm (halfLaw hp6) f ^ 2 at h
  refine h.trans ?_
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (hP_inv_le_privateCompression (by omega))
    (mul_nonneg (mul_nonneg (by norm_num) rectangleMassUpper_nonneg)
      (coherentOffdiagPrice_nonneg hp7))

end Sarkozy.PositiveRoots.CoherentFrame
