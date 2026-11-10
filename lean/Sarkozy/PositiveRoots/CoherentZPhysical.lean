module

public import Sarkozy.PositiveRoots.CoherentZException

/-! Identification of the signed product estimate with the actual centered K feature Z. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.JointRows.StarOps (expect_finset_sum)

variable {p : ℕ} [Fact p.Prime]

theorem normalizedStarProduct_expect {U : Type*} (S T : Finset U)
    (F : ZMod p × ZMod p → ℝ) (x : U → ZMod p) :
    normalizedStarProduct S T F x = (p : ℝ) * ((fieldLaw p).product (fieldLaw p)).expect
      (fun z => StarMatrix.psi S z.1 x * StarMatrix.psi T z.2 x * F z) := by
  rw [FiniteLaw.expect_product]
  rfl

theorem Kz_nonempty_expansion (x : Fin 4 → ZMod p) (z : ZMod p) :
    Kz z x = 1 + ∑ T ∈ nonemptySets (Fin 4), sig T * StarMatrix.psi T z x := by
  have he : nonemptySets (Fin 4) = univ.erase ∅ := by
    ext T
    simp [nonemptySets, nonempty_iff_ne_empty]
  rw [he, Kz_expand]
  have hs := sum_erase_add (s := (univ : Finset (Finset (Fin 4))))
    (fun T => sig T * StarMatrix.psi T z x) (mem_univ ∅)
  have hzero : sig ∅ * StarMatrix.psi ∅ z x = 1 := by
    simp only [sig, StarMatrix.psi, prod_empty, one_mul]
  rw [hzero] at hs
  change (∑ T : Finset (Fin 4), sig T * StarMatrix.psi T z x) = _
  linarith

noncomputable def coreZKernel (x : Fin 4 → ZMod p) (z : ZMod p) : ℝ :=
  (Kz z x - Kbar x) / (Real.sqrt 15 * rp p)

theorem coreZKernel_mean_zero (x : Fin 4 → ZMod p) :
    (fieldLaw p).expect (coreZKernel x) = 0 := by
  have he : (fieldLaw p).expect (fun z => Kz z x) = Kbar x := by
    rw [fieldLaw, FiniteLaw.expect_uniform]
    rfl
  change (fieldLaw p).expect (fun z => (Kz z x - Kbar x) / (Real.sqrt 15 * rp p)) = 0
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, FiniteLaw.expect_sub,
    FiniteLaw.expect_const, he, sub_self, zero_mul]

theorem Kz_centered_row (x : Fin 4 → ZMod p) (G : ZMod p → ℝ)
    (hG : (fieldLaw p).expect G = 0) :
    (fieldLaw p).expect (fun z => (Kz z x - Kbar x) * G z) =
      ∑ T ∈ nonemptySets (Fin 4), sig T * (fieldLaw p).expect (fun z => StarMatrix.psi T z x * G z) := by
  have he (z : ZMod p) : (Kz z x - Kbar x) * G z =
      (1 - Kbar x) * G z + ∑ T ∈ nonemptySets (Fin 4), sig T * (StarMatrix.psi T z x * G z) := by
    rw [Kz_nonempty_expansion]
    calc
      _ = (1 - Kbar x) * G z + (∑ T ∈ nonemptySets (Fin 4), sig T * StarMatrix.psi T z x) * G z := by ring
      _ = _ := by simp only [sum_mul, mul_assoc]
  simp_rw [he, FiniteLaw.expect_add, FiniteLaw.expect_const_mul, hG, mul_zero, zero_add,
    expect_finset_sum, FiniteLaw.expect_const_mul]

theorem coreZProduct_physical (S : Finset (Fin 4)) (F : ZMod p × ZMod p → ℝ)
    (hrow : ∀ u, (fieldLaw p).expect (fun v => F (u, v)) = 0) (x : Fin 4 → ZMod p) :
    ((fieldLaw p).product (fieldLaw p)).expect
      (fun z => (StarMatrix.psi S z.1 x / rp p) * coreZKernel x z.2 * F z) = coreZProduct S F x := by
  have hscale : (rp p)⁻¹ * (Real.sqrt 15 * rp p)⁻¹ = (p : ℝ) * (Real.sqrt 15)⁻¹ := by
    calc
      _ = (rp p ^ 2)⁻¹ * (Real.sqrt 15)⁻¹ := by
        rw [mul_inv_rev, ← inv_pow]
        ring
      _ = _ := by rw [rp_sq, inv_inv]
  have he (z : ZMod p × ZMod p) :
      (StarMatrix.psi S z.1 x / rp p) * coreZKernel x z.2 * F z =
        ((p : ℝ) * (Real.sqrt 15)⁻¹) *
          (StarMatrix.psi S z.1 x * ((Kz z.2 x - Kbar x) * F z)) := by
    unfold coreZKernel
    calc
      _ = ((rp p)⁻¹ * (Real.sqrt 15 * rp p)⁻¹) *
          (StarMatrix.psi S z.1 x * ((Kz z.2 x - Kbar x) * F z)) := by ring
      _ = _ := by rw [hscale]
  simp_rw [he]
  rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_product]
  simp_rw [FiniteLaw.expect_const_mul, Kz_centered_row x _ (hrow _), mul_sum,
    expect_finset_sum]
  unfold coreZProduct normalizedStarProduct starProduct
  simp_rw [mul_assoc, FiniteLaw.expect_const_mul, mul_left_comm (StarMatrix.psi S _ x),
    FiniteLaw.expect_const_mul]
  simp only [mul_sum]
  apply sum_congr rfl
  intro T _
  unfold StarMatrix.psi
  ring

theorem coreZProduct_physical_bound [Nonempty (CoreT (ZMod p))]
    (hW : Labellings.WeilBound (ZMod p)) (hDLK : Target.FourCycle)
    (hp3 : p % 4 = 3) (hp40 : 2 ^ 40 ≤ p) (S : Finset (Fin 4)) (hS : 2 ≤ S.card)
    (F : ZMod p × ZMod p → ℝ)
    (hrow : ∀ u, (fieldLaw p).expect (fun v => F (u, v)) = 0)
    (hcol : ∀ v, (fieldLaw p).expect (fun u => F (u, v)) = 0) :
    nrm coreLaw (fun c : CoreT (ZMod p) => ((fieldLaw p).product (fieldLaw p)).expect
      (fun z => (StarMatrix.psi S z.1 c.val / rp p) * coreZKernel c.val z.2 * F z) -
        coreZExceptional S F) ≤ 22 * nrm ((fieldLaw p).product (fieldLaw p)) F := by
  simp_rw [coreZProduct_physical S F hrow]
  exact coreZProduct_residual_norm hW hDLK hp3 hp40 S hS F hrow hcol

end Sarkozy.PositiveRoots.CoherentFrame
