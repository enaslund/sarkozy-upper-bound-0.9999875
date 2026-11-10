module

public import Sarkozy.L20Cap.Mellin
public import Sarkozy.TargetMellin





@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

theorem legT_eq (p : ℕ) [Fact p.Prime] (t : ZMod p) : legT t = Target.legendreSum p t := rfl

/-- **`λ_ρ ≥ -(3r + q - q²)`** for every nontrivial multiplicative character `ρ` of `𝔽_p`, from
the proposed H7 (`lem:rectangle-mellin`, the lower bound at the level of the eigenvalues). -/
theorem eigen_lower (hH7 : Target.SymSquareMellin) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {ρ : MulChar (ZMod p) ℂ} (hρ : ρ ≠ 1) :
    -(3 / Real.sqrt p + (p : ℝ)⁻¹ - (p : ℝ)⁻¹ ^ 2) ≤
      (∑ t, (Hu (0 : ZMod p) 1 t : ℂ) * ρ t).re := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [eigen_formula hF hρ]
  set S := ∑ t ∈ univ.filter (fun t : ZMod p => t ≠ 0 ∧ t ≠ 1),
    ρ t * ((legT t ^ 2 - (Fintype.card (ZMod p) : ℤ) : ℤ) : ℂ) with hS
  have hS' : ‖S‖ ≤ 3 * (p : ℝ) ^ ((3 : ℝ) / 2) := by
    have h := hH7 p hp2 ρ hρ
    rw [hS, hcard]
    simpa only [legT_eq] using h
  have hre : |S.re| ≤ 3 * (p : ℝ) ^ ((3 : ℝ) / 2) := (Complex.abs_re_le_norm S).trans hS'
  rw [hcard]
  have hval : (-((p : ℝ)⁻¹ : ℂ) + ((p : ℝ)⁻¹ : ℂ) ^ 2 + ((p : ℝ)⁻¹ : ℂ) ^ 2 * S).re =
      -(p : ℝ)⁻¹ + (p : ℝ)⁻¹ ^ 2 + (p : ℝ)⁻¹ ^ 2 * S.re := by
    simp [Complex.add_re, Complex.mul_re, pow_two]
  rw [hval]
  -- `q² · 3p^{3/2} = 3/√p`
  have hpow : (p : ℝ) ^ ((3 : ℝ) / 2) = p * Real.sqrt p := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hsq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hkey : (p : ℝ)⁻¹ ^ 2 * (3 * (p : ℝ) ^ ((3 : ℝ) / 2)) = 3 / Real.sqrt p := by
    rw [hpow]
    field_simp
    nlinarith [hss]
  have hlow : -(3 / Real.sqrt p) ≤ (p : ℝ)⁻¹ ^ 2 * S.re := by
    have h1 : -(3 * (p : ℝ) ^ ((3 : ℝ) / 2)) ≤ S.re := (abs_le.mp hre).1
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ((p : ℝ)⁻¹))
    rw [mul_neg, hkey] at h2
    exact h2
  linarith

end Sarkozy.L20Cap
