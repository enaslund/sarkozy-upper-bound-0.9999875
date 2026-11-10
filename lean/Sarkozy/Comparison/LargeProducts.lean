module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Rankin's trick for large selections

The summation step of `lem:record:density-lp` (`paper/sections/08_scale_comparison.tex`):
for nonnegative coefficients `η_B` and atom moduli `q_B ≥ 1`,

`∑_{E : q_E > X} ∏_{B∈E} η_B ≤ X^(-1/4) ∏_B (1 + η_B q_B^(1/4))`,

where `q_E = ∏_{B∈E} q_B`. With `X = N^τ`, and the per-selection bound
`|∫ ∏ᵥ G_v dκ'_E| ≤ c (∏_{B∈E} η_B) M` supplied by Hölder's inequality and the lift
moments, this gives the large-product remainder `c M Π_H N^(-τ/4)`. The analytic
inputs (Hölder in `L⁷²` with uniform marginals and the order-72 lift moment) are the
project's `Sarkozy.FiniteLaw.abs_expect_prod_le_lpNorm` and the
`Sarkozy.FourierArithmetic` moment theorems; this module proves the combinatorial
part, uniformly in the finite family of atoms.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Comparison

variable {ι : Type*}


/-- `∑_{E ⊆ 𝒜} ∏_{B∈E} a_B = ∏_{B∈𝒜} (1 + a_B)`. -/
theorem sum_powerset_prod_eq (𝒜 : Finset ι) (a : ι → ℝ) :
    ∑ E ∈ 𝒜.powerset, ∏ B ∈ E, a B = ∏ B ∈ 𝒜, (1 + a B) :=
  (Finset.prod_one_add 𝒜).symm

/-- **Rankin's trick.** -/
theorem rankin_large_selections (𝒜 : Finset ι) (η q : ι → ℝ) (hη : ∀ B ∈ 𝒜, 0 ≤ η B)
    (hq : ∀ B ∈ 𝒜, 1 ≤ q B) {X : ℝ} (hX : 0 < X) :
    ∑ E ∈ 𝒜.powerset.filter (fun E => X < ∏ B ∈ E, q B), ∏ B ∈ E, η B ≤
      X ^ (-(1 / 4 : ℝ)) * ∏ B ∈ 𝒜, (1 + η B * q B ^ (1 / 4 : ℝ)) := by
  have hterm : ∀ E ∈ 𝒜.powerset.filter (fun E => X < ∏ B ∈ E, q B),
      ∏ B ∈ E, η B ≤ X ^ (-(1 / 4 : ℝ)) * ∏ B ∈ E, (η B * q B ^ (1 / 4 : ℝ)) := by
    intro E hE
    obtain ⟨hEs, hEX⟩ := Finset.mem_filter.mp hE
    have hEs' := Finset.mem_powerset.mp hEs
    have hq0 : ∀ B ∈ E, 0 ≤ q B := fun B hB => (zero_le_one.trans (hq B (hEs' hB)))
    have hprodq : 0 ≤ ∏ B ∈ E, q B := Finset.prod_nonneg hq0
    have hroot : X ^ (1 / 4 : ℝ) ≤ (∏ B ∈ E, q B) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hX.le hEX.le (by norm_num)
    have hsplit : ∏ B ∈ E, (η B * q B ^ (1 / 4 : ℝ)) =
        (∏ B ∈ E, η B) * (∏ B ∈ E, q B) ^ (1 / 4 : ℝ) := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow E q hq0]
    have hη0 : 0 ≤ ∏ B ∈ E, η B := Finset.prod_nonneg fun B hB => hη B (hEs' hB)
    have hXpos : 0 < X ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hX _
    rw [hsplit, Real.rpow_neg hX.le, ← mul_assoc, mul_comm (X ^ (1 / 4 : ℝ))⁻¹,
      mul_assoc]
    calc ∏ B ∈ E, η B = (∏ B ∈ E, η B) * (X ^ (1 / 4 : ℝ) * (X ^ (1 / 4 : ℝ))⁻¹) := by
          rw [mul_inv_cancel₀ hXpos.ne', mul_one]
      _ ≤ (∏ B ∈ E, η B) * ((X ^ (1 / 4 : ℝ))⁻¹ * (∏ B ∈ E, q B) ^ (1 / 4 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hη0
          rw [mul_comm ((X ^ (1 / 4 : ℝ))⁻¹)]
          exact mul_le_mul_of_nonneg_right hroot (inv_nonneg.mpr hXpos.le)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX.le _)
  have hnn : ∀ E ∈ 𝒜.powerset, 0 ≤ ∏ B ∈ E, (η B * q B ^ (1 / 4 : ℝ)) := by
    intro E hE
    have hEs' := Finset.mem_powerset.mp hE
    exact Finset.prod_nonneg fun B hB =>
      mul_nonneg (hη B (hEs' hB)) (Real.rpow_nonneg (zero_le_one.trans (hq B (hEs' hB))) _)
  calc ∑ E ∈ 𝒜.powerset.filter (fun E => X < ∏ B ∈ E, q B), ∏ B ∈ E, (η B * q B ^ (1 / 4 : ℝ))
      ≤ ∑ E ∈ 𝒜.powerset, ∏ B ∈ E, (η B * q B ^ (1 / 4 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun E hE _ => hnn E hE)
    _ = ∏ B ∈ 𝒜, (1 + η B * q B ^ (1 / 4 : ℝ)) := sum_powerset_prod_eq 𝒜 _

/-- **The large-product remainder** (the summation of `lem:record:density-lp`): if every
selection `E` with `q_E > X` has a term bounded by `c (∏_{B∈E} η_B) M`, the sum of the
absolute values of these terms is at most `c M X^(-1/4) Π_H`. -/
theorem large_product_remainder (𝒜 : Finset ι) (η q : ι → ℝ) (hη : ∀ B ∈ 𝒜, 0 ≤ η B)
    (hq : ∀ B ∈ 𝒜, 1 ≤ q B) {X c M : ℝ} (hX : 0 < X) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (term : Finset ι → ℝ)
    (hterm : ∀ E ∈ 𝒜.powerset, X < ∏ B ∈ E, q B → |term E| ≤ c * (∏ B ∈ E, η B) * M) :
    ∑ E ∈ 𝒜.powerset.filter (fun E => X < ∏ B ∈ E, q B), |term E| ≤
      c * M * X ^ (-(1 / 4 : ℝ)) * ∏ B ∈ 𝒜, (1 + η B * q B ^ (1 / 4 : ℝ)) := by
  have h1 : ∑ E ∈ 𝒜.powerset.filter (fun E => X < ∏ B ∈ E, q B), |term E| ≤
      ∑ E ∈ 𝒜.powerset.filter (fun E => X < ∏ B ∈ E, q B), c * M * ∏ B ∈ E, η B := by
    refine Finset.sum_le_sum fun E hE => ?_
    obtain ⟨hEs, hEX⟩ := Finset.mem_filter.mp hE
    refine (hterm E hEs hEX).trans_eq ?_
    ring
  refine h1.trans ?_
  rw [← Finset.mul_sum, mul_assoc (c * M)]
  exact mul_le_mul_of_nonneg_left (rankin_large_selections 𝒜 η q hη hq hX) (mul_nonneg hc hM)

end Sarkozy.Comparison
