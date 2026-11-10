module

public import Sarkozy.Moments.Holder
public import Sarkozy.ProbabilityConstructions

@[expose] public section

/-!
# Step 2 of `lem:record:density-can`: the moments

`paper/sections/08_scale_comparison.tex`, proof of `lem:record:density-can`, Step 2: "Under `ϱ`
every `z_w` is uniform on `G_N`. By Hölder with `70` factors and
`lem:record:lift-moments`(c) with moments of order `140`,
`∫ ‖W_x‖₂² dϱ_pre = ∫ ∏_{w ≠ u,v} |G_w(z_w)|² dϱ ≤ ∏_{w ≠ u,v} ‖G_w‖₁₄₀² ≤ C_ε N^ε α`,
and by Cauchy–Schwarz and the fourth moments `∫ ‖φ_x‖₂² ≤ ‖G_u‖₄² ‖G_v‖₄² ≤ C_ε N^ε α`.
The density exponents are `70·2/140 = 1` and `2·2/4 = 1`."

`step2_holder_moments` is the Hölder step for `n` factors with uniform one-slot marginals and
the moment input `E|G_w|^{2n} ≤ M` (`lem:record:lift-moments`(c), a hypothesis): the integral of
`∏_w |G_w(z_w)|²` is at most `M`. With `n = 70` it is the first bound, with `n = 2` the second.
It uses the finite Hölder inequality `Sarkozy.FiniteLaw.abs_expect_prod_le_lpNorm`
(`Sarkozy.Moments.Holder`).

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset

/-- **Step 2 of `lem:record:density-can` (Hölder with `n` factors).** Let `ϱ` be a law on `Ω`
under which every slot `z_i` is uniform on `Z`, and let `E_unif |G_i|^{2n} ≤ M` for each of the
`n` factors. Then `∫ ∏_i |G_i(z_i)|² dϱ ≤ ∏_i ‖G_i‖_{2n}² ≤ M`. -/
theorem step2_holder_moments {Ω I Z : Type*} [Fintype Ω] [Fintype I] [Fintype Z] [Nonempty Z]
    (ϱ : FiniteLaw Ω) (n : ℕ) (hn : Fintype.card I = n) (hn0 : 0 < n)
    (z : I → Ω → Z) (G : I → Z → ℝ)
    (hunif : ∀ i (f : Z → ℝ), ϱ.expect (fun ω => f (z i ω)) = (FiniteLaw.uniform Z).expect f)
    {M : ℝ} (hM : 0 ≤ M)
    (hmom : ∀ i, (FiniteLaw.uniform Z).expect (fun y => |G i y| ^ ((2 * n : ℕ) : ℝ)) ≤ M) :
    ϱ.expect (fun ω => ∏ i, G i (z i ω) ^ 2) ≤ M := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsum : ∑ _i : I, 1 / (n : ℝ) = 1 := by
    rw [sum_const, card_univ, hn, nsmul_eq_mul]
    field_simp
  have hH := ϱ.abs_expect_prod_le_lpNorm (fun _ => (n : ℝ)) (fun _ => hnr) hsum
    (fun i ω => G i (z i ω) ^ 2)
  have hnorm : ∀ i, ϱ.lpNorm (n : ℝ) (fun ω => G i (z i ω) ^ 2) ≤ M ^ (1 / (n : ℝ)) := by
    intro i
    unfold FiniteLaw.lpNorm FiniteLaw.moment
    have he : ϱ.expect (fun ω => |G i (z i ω) ^ 2| ^ (n : ℝ)) =
        (FiniteLaw.uniform Z).expect (fun y => |G i y| ^ ((2 * n : ℕ) : ℝ)) := by
      rw [← hunif i (fun y => |G i y| ^ ((2 * n : ℕ) : ℝ))]
      apply ϱ.expect_congr
      intro ω
      rw [abs_pow, Real.rpow_natCast, Real.rpow_natCast, ← pow_mul, mul_comm]
    rw [he]
    apply Real.rpow_le_rpow ((FiniteLaw.uniform Z).expect_nonneg
      (fun y => Real.rpow_nonneg (abs_nonneg _) _)) (hmom i) (by positivity)
  have hprod : ∏ i, ϱ.lpNorm (n : ℝ) (fun ω => G i (z i ω) ^ 2) ≤ M := by
    calc ∏ i, ϱ.lpNorm (n : ℝ) (fun ω => G i (z i ω) ^ 2) ≤ ∏ _i : I, M ^ (1 / (n : ℝ)) :=
          prod_le_prod₀ (fun i _ => ϱ.lpNorm_nonneg _ _) (fun i _ => hnorm i)
      _ = M := by
          rw [prod_const, card_univ, hn, ← Real.rpow_natCast, ← Real.rpow_mul hM]
          rw [one_div_mul_cancel hnr.ne', Real.rpow_one]
  exact (le_abs_self _).trans (hH.trans hprod)

end Sarkozy.Cancellation
