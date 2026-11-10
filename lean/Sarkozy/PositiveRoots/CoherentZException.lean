module

public import Sarkozy.PositiveRoots.CoherentZProduct

/-! The exact rank-one exceptional coefficient of the coherent Z product. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Sarkozy.L20Cap Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.Cuts Sarkozy.Recentering

variable {p : ℕ} [Fact p.Prime]

theorem entangledCoefficient_le_norm (hp : 3 ≤ p) (F : ZMod p × ZMod p → ℝ)
    (hrow : ∀ u, (fieldLaw p).expect (fun v => F (u, v)) = 0)
    (hcol : ∀ v, (fieldLaw p).expect (fun u => F (u, v)) = 0) :
    |entangledCoefficient F| ≤ nrm ((fieldLaw p).product (fieldLaw p)) F := by
  rw [entangledCoefficient_abs (by omega : 2 ≤ p)]
  have hc : 3 ≤ Fintype.card (ZMod p) := by simpa only [ZMod.card] using hp
  have h := diagonal_parts_energy hc F hrow hcol
  have hn := nrm_nonneg ((fieldLaw p).product (fieldLaw p)) F
  have hn0 := nrm_nonneg ((fieldLaw p).product (fieldLaw p)) (constantDiagonalPart F)
  change nrm ((fieldLaw p).product (fieldLaw p)) F ^ 2 =
    nrm ((fieldLaw p).product (fieldLaw p)) (constantDiagonalPart F) ^ 2 +
      nrm ((fieldLaw p).product (fieldLaw p)) (variableDiagonalPart F) ^ 2 +
      nrm ((fieldLaw p).product (fieldLaw p)) (offDiagonalPart F) ^ 2 at h
  nlinarith [sq_nonneg (nrm ((fieldLaw p).product (fieldLaw p)) (variableDiagonalPart F)),
    sq_nonneg (nrm ((fieldLaw p).product (fieldLaw p)) (offDiagonalPart F))]

omit [Fact p.Prime] in
theorem coreZ_exception_coefficient (hp40 : 2 ^ 40 ≤ p) (S : Finset (Fin 4)) :
    |sig S / Real.sqrt 15 * ((p : ℝ) / Real.sqrt (p - 1))| ≤ (259 / 1000 : ℝ) / rp p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hr : 0 < rp p := by unfold rp; positivity
  have hs : (3872 / 1000 : ℝ) ≤ Real.sqrt 15 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [abs_mul, abs_div, abs_coreSign, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by positivity : 0 ≤ (p : ℝ) / Real.sqrt (p - 1)), le_div_iff₀ hr]
  have h := entangled_factor_times_r_le hp40
  calc
    _ = (((p : ℝ) / Real.sqrt (p - 1)) * rp p) / Real.sqrt 15 := by ring
    _ ≤ (1001 / 1000 : ℝ) / Real.sqrt 15 :=
      div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 15)]
      linarith

theorem coreZExceptional_bound (hp40 : 2 ^ 40 ≤ p) (S : Finset (Fin 4))
    (F : ZMod p × ZMod p → ℝ)
    (hrow : ∀ u, (fieldLaw p).expect (fun v => F (u, v)) = 0)
    (hcol : ∀ v, (fieldLaw p).expect (fun u => F (u, v)) = 0) :
    |coreZExceptional S F| ≤ ((259 / 1000 : ℝ) / rp p) *
      nrm ((fieldLaw p).product (fieldLaw p)) F := by
  have he : coreZExceptional S F =
      (sig S / Real.sqrt 15 * ((p : ℝ) / Real.sqrt (p - 1))) * entangledCoefficient F := by
    unfold coreZExceptional
    ring
  rw [he, abs_mul]
  exact mul_le_mul (coreZ_exception_coefficient hp40 S)
    (entangledCoefficient_le_norm (by omega : 3 ≤ p) F hrow hcol)
    (abs_nonneg _) (by have := rp_nonneg (p := p); positivity)

end Sarkozy.PositiveRoots.CoherentFrame
