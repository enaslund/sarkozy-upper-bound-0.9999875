module

public import Sarkozy.L20Cap.Rectangle
public import Sarkozy.Cuts.SwappedDeflated

/-! The swapped rectangle after removing its mass tensor. -/

@[expose] public section

namespace Sarkozy.L20Cap

open Sarkozy.Cuts Sarkozy.Recentering

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

theorem rectangle_deflated_norm (hm1 : quadraticChar F (-1) = -1) {c s : ℝ}
    (hc : 0 ≤ c)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ c * nrm pairLaw h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : c ≤ s)
    (f : CoreT F × PairT F → ℝ) :
    nrm (coreLaw.product pairLaw) (fun x => swapOp coreLaw pairLaw Rk f x -
      ip (coreLaw.product pairLaw) f (fun y => rmass y.1) * rmass x.1) ≤
      s * c * nrm (coreLaw.product pairLaw) f := by
  let σ := nrm (coreLaw (F := F)) rmass
  have hσ0 : 0 ≤ σ := nrm_nonneg _ _
  by_cases hσ : σ = 0
  · have hr0 := rmass_eq_zero_of_nrm hσ
    have he : (Rk : CoreT F → PairT F → ℝ) = Rc := by
      funext C b
      simp only [Rc, hr0, sub_zero]
    have hb := nrm_swapOp_le coreLaw pairLaw Rk hc (by simpa only [he] using hRc) f
    simp only [hr0, mul_zero, sub_zero]
    exact hb.trans (mul_le_mul_of_nonneg_right (by nlinarith : c ^ 2 ≤ s * c)
      (nrm_nonneg _ _))
  · have hσp : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσ)
    have hu : nrm coreLaw (fun C : CoreT F => σ⁻¹ * rmass C) = 1 := by
      rw [nrm_smul, abs_of_pos (inv_pos.mpr hσp)]
      exact inv_mul_cancel₀ hσ
    have hA (C : CoreT F) (b : PairT F) : Rk C b = σ * (σ⁻¹ * rmass C) * 1 + Rc C b := by
      unfold Rc
      field_simp
      ring
    have hAu (b : PairT F) : recAdj coreLaw Rc (fun C : CoreT F => σ⁻¹ * rmass C) b = 0 := by
      unfold recAdj Rc
      have he : (fun C : CoreT F => (Rk C b - rmass C) * (σ⁻¹ * rmass C)) =
          fun C => σ⁻¹ * (Rk C b * rmass C - rmass C ^ 2) := by
        funext C; ring
      rw [he, FiniteLaw.expect_const_mul, FiniteLaw.expect_sub]
      have hadj := adj_rmass hm1 b
      unfold recAdj at hadj
      rw [hadj, ← nrm_sq_expect]
      ring
    have hb := swap_norm_deflated coreLaw pairLaw Rk Rc (σ := σ)
      (fun C => σ⁻¹ * rmass C) (fun _ => 1) hu (nrm_one _) hσ0 hA recOp_Rc_one
      hAu hc hRc hs hcs f
    simp only [mul_one] at hb
    have hip : ip (coreLaw.product pairLaw) f (fun x : CoreT F × PairT F => σ⁻¹ * rmass x.1) =
        σ⁻¹ * ip (coreLaw.product pairLaw) f (fun x => rmass x.1) := by
      rw [ip_comm, ip_smul_left, ip_comm]
    rw [hip] at hb
    have he (x : CoreT F × PairT F) :
        σ ^ 2 * (σ⁻¹ * ip (coreLaw.product pairLaw) f (fun y => rmass y.1)) * (σ⁻¹ * rmass x.1) =
          ip (coreLaw.product pairLaw) f (fun y => rmass y.1) * rmass x.1 := by
      field_simp
    simpa only [he] using hb

theorem rectangle_constant_gap (hm1 : quadraticChar F (-1) = -1) {c s d : ℝ}
    (hc : 0 ≤ c)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ c * nrm pairLaw h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : c ≤ s)
    (hd : nrm coreLaw (fun C : CoreT F => rmass C - 1) ≤ d)
    (f : CoreT F × PairT F → ℝ) :
    nrm (coreLaw.product pairLaw) (fun x => swapOp coreLaw pairLaw Rk f x -
      (coreLaw.product pairLaw).expect f) ≤
      (s * c + (s + 1) * d) * nrm (coreLaw.product pairLaw) f := by
  have hs0 : 0 ≤ s := (nrm_nonneg _ _).trans hs
  have hd0 : 0 ≤ d := (nrm_nonneg _ _).trans hd
  have ha : nrm (coreLaw.product pairLaw) (fun x : CoreT F × PairT F => rmass x.1) =
      nrm coreLaw (rmass (F := F)) := by
    simpa only [mul_one, nrm_one] using nrm_tensor coreLaw pairLaw (rmass (F := F)) (fun _ => 1)
  have had : nrm (coreLaw.product pairLaw) (fun x : CoreT F × PairT F => rmass x.1 - 1) =
      nrm coreLaw (fun C : CoreT F => rmass C - 1) := by
    simpa only [mul_one, nrm_one] using nrm_tensor coreLaw pairLaw
      (fun C : CoreT F => rmass C - 1) (fun _ => 1)
  have hrank := rank_one_difference_norm (coreLaw.product pairLaw)
    (fun x : CoreT F × PairT F => rmass x.1) (fun _ => 1) f
  rw [ha, nrm_one, had] at hrank
  have hrank' : nrm ((coreLaw (F := F)).product (pairLaw (F := F)))
      (fun x => ip (coreLaw.product pairLaw) f (fun y => rmass y.1) * rmass x.1 -
        ip (coreLaw.product pairLaw) f (fun _ => 1) * 1) ≤
      ((s + 1) * d) * nrm (coreLaw.product pairLaw) f := by
    apply hrank.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (by linarith : nrm coreLaw (rmass (F := F)) + 1 ≤ s + 1)
        hd (nrm_nonneg _ _) (by linarith))
      (nrm_nonneg _ _)
  have hdef := rectangle_deflated_norm hm1 hc hRc hs hcs f
  have h1 : ip (coreLaw.product pairLaw) f (fun _ => 1) =
      (coreLaw.product pairLaw).expect f := by rw [ip_comm, ip_one_left]
  have he : (fun x => swapOp coreLaw pairLaw Rk f x - (coreLaw.product pairLaw).expect f) =
      fun x => (swapOp coreLaw pairLaw Rk f x -
        ip (coreLaw.product pairLaw) f (fun y => rmass y.1) * rmass x.1) +
      (ip (coreLaw.product pairLaw) f (fun y => rmass y.1) * rmass x.1 -
        ip (coreLaw.product pairLaw) f (fun _ => 1) * 1) := by
    funext x; rw [h1]; ring
  rw [he]
  exact (nrm_add_le _ _ _).trans ((add_le_add hdef hrank').trans_eq (by ring))

end Sarkozy.L20Cap
