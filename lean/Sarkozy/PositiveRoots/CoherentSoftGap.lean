module

public import Sarkozy.PositiveRoots.CoherentMassNumerics
public import Sarkozy.PositiveRoots.CoherentGapNumerics
public import Sarkozy.L20Cap.RectangleDeflated

/-! The accepting soft kernel differs from the constant kernel by at most 15 / √p. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.SpectralC Sarkozy.SpectralD

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

theorem rectangle_mass_norm_small_40 (hW : Labellings.WeilBound (ZMod p))
    (hAO : Target.AhlgrenOno) (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) :
    nrm coreLaw (rmass (F := ZMod p)) ≤ (1001 / 1000 : ℝ) := by
  have hb := rectangle_mass_variation_small_40 hW hAO hp3 hp40
  have hr := rp_small_40 hp40
  have ht := nrm_add_le coreLaw (fun C : CoreT (ZMod p) => rmass C - 1) (fun _ => 1)
  have he : (fun C : CoreT (ZMod p) => (rmass C - 1) + 1) = rmass := by funext C; ring
  rw [he, nrm_one] at ht
  linarith

theorem Ksoft_sub_one_action (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    recOp (coreLaw.product pairLaw) (fun x y => Ksoft x y - 1) f =
      fun x => swapOp coreLaw pairLaw Rk f x - (coreLaw.product pairLaw).expect f := by
  funext x
  unfold recOp swapOp
  rw [← FiniteLaw.expect_sub]
  exact (coreLaw.product pairLaw).expect_congr fun y => by unfold Ksoft; ring

theorem Ksoft_sub_one_norm_small_40 (hW : Labellings.WeilBound (ZMod p))
    (hAO : Target.AhlgrenOno) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    nrm (coreLaw.product pairLaw) (recOp (coreLaw.product pairLaw)
      (fun x y => Ksoft x y - 1) f) ≤
      (15 * rp p) * nrm (coreLaw.product pairLaw) f := by
  have hr0 := rp_nonneg (p := p)
  have hr := rp_small_40 hp40
  have hb := rectangle_constant_gap (JointRows.PaleyGauss.chi_neg_one hp3)
    (c := (59 / 10 : ℝ) * rp p) (s := (1001 / 1000 : ℝ)) (d := (9 / 2 : ℝ) * rp p)
    (by positivity) (rectangle_centered_norm_small_40 hW hDLK hp3 hp40)
    (rectangle_mass_norm_small_40 hW hAO hp3 hp40) (by linarith)
    (rectangle_mass_variation_small_40 hW hAO hp3 hp40) f
  rw [Ksoft_sub_one_action]
  exact hb.trans (mul_le_mul_of_nonneg_right (by nlinarith) (nrm_nonneg _ _))

theorem Ksoft_sub_one_form_small_40 (hW : Labellings.WeilBound (ZMod p))
    (hAO : Target.AhlgrenOno) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p)
    (f g : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (coreLaw.product pairLaw) (coreLaw.product pairLaw)
      (fun x y => Ksoft x y - 1) f g| ≤
      (15 * rp p) * nrm (coreLaw.product pairLaw) f * nrm (coreLaw.product pairLaw) g := by
  rw [kernelForm_apply]
  change |ip (coreLaw.product pairLaw) f
    (recOp (coreLaw.product pairLaw) (fun x y => Ksoft x y - 1) g)| ≤ _
  exact (abs_ip_le _ _ _).trans ((mul_le_mul_of_nonneg_left
    (Ksoft_sub_one_norm_small_40 hW hAO hDLK hp3 hp40 g) (nrm_nonneg _ _)).trans_eq (by ring))

end Sarkozy.PositiveRoots.CoherentFrame
