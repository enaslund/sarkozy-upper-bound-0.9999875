module

public import Sarkozy.DensityFibre.FoldedMarginals
public import Sarkozy.DensityChain.LargeTerms

@[expose] public section

/-!
# `lem:record:density-lp`, first two steps, at a folded energy

LP (8 November 2026). The large pieces of `lem:sharp-first` are the terms
`w_φ √𝔈₊(φ) √𝔈₋(φ)` with `q_E > N^τ` (or an unrevealed interval), where `𝔈_±(φ)` are folded
energies `∫ (a ∘ φ_±) d(⊗_𝔟 L^±_{𝔟,φ_𝔟})` of positive records. The paper's proof of
`lem:record:density-lp` bounds each `I^±_E` by Hölder in `L^{72}` with the uniform one-slot
marginals, then Hölder over the index law: "The same bound holds for `I_E^±`, hence for
`(I_E^+I_E^-)^{1/2}`." This file does this for one folded energy, with inputs read through an
arbitrary relabelling `e : Y ≃ ∏_𝔟 X_𝔟` (the CRT labels) and an arbitrary slot map `fo`
(`φ₊` or `φ₋`):

* `moment_uniform_equiv`: the `p`-th moment under the uniform law is invariant under relabelling;
* `totalVariation_tensorLaw`: the total variation of a tensor of positive records is the product
  of their masses;
* **`expect_abs_tensor_le`**: `E_ω |∫ ∏_v a^ω_{fo v}(e⁻¹ z_v) d(⊗_𝔟 Λ_𝔟)(z)| ≤ (∏_𝔟 Λ_𝔟(1)) B`
  when every `Λ_𝔟` is a positive record and `E_ω ‖a^ω_v‖_{72}^{72} ≤ B` at every slot;
* `sqrt_mul_sqrt_le_abs`: `√x √y ≤ (|x| + |y|)/2` for all real `x, y` (no sign condition on the
  folded energies is needed);
* `expect_le_of_weight_ne_zero`: an expectation is at most `c` when the integrand is at most `c`
  on the support of the law (used for the depth vectors with an unrevealed interval, which have
  zero query weight).
-/

namespace Sarkozy.LargeSums

open Finset Function
open scoped BigOperators
open Sarkozy.TheoremC Sarkozy.Structured Sarkozy.DensityChain

/-- **The moments of the uniform law are invariant under relabelling.** -/
theorem moment_uniform_equiv {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (e : Y ≃ X) (p : ℝ) (g : Y → ℝ) :
    (FiniteLaw.uniform X).moment p (fun x => g (e.symm x)) = (FiniteLaw.uniform Y).moment p g := by
  unfold FiniteLaw.moment
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform,
    Equiv.sum_comp e.symm (fun y => |g y| ^ p), Fintype.card_congr e]

/-- `√x √y ≤ (|x| + |y|)/2` for all real `x, y`. -/
theorem sqrt_mul_sqrt_le_abs (x y : ℝ) :
    Real.sqrt x * Real.sqrt y ≤ (|x| + |y|) / 2 := by
  have hx : Real.sqrt x = Real.sqrt |x| ∨ Real.sqrt x = 0 := by
    rcases le_or_gt 0 x with h | h
    · left; rw [abs_of_nonneg h]
    · right; exact Real.sqrt_eq_zero'.mpr h.le
  have hy : Real.sqrt y = Real.sqrt |y| ∨ Real.sqrt y = 0 := by
    rcases le_or_gt 0 y with h | h
    · left; rw [abs_of_nonneg h]
    · right; exact Real.sqrt_eq_zero'.mpr h.le
  have hxy : Real.sqrt |x| * Real.sqrt |y| ≤ (|x| + |y|) / 2 := by
    have h := sq_nonneg (Real.sqrt |x| - Real.sqrt |y|)
    rw [sub_sq, Real.sq_sqrt (abs_nonneg x), Real.sq_sqrt (abs_nonneg y)] at h
    linarith
  have h0 : 0 ≤ (|x| + |y|) / 2 := by positivity
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp only [hx, hy, mul_zero, zero_mul]
  all_goals first | exact hxy | exact h0

/-- **An expectation bounded on the support of the law.** -/
theorem expect_le_of_weight_ne_zero {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) {f : Ω → ℝ}
    {c : ℝ} (h : ∀ ω, μ.weight ω ≠ 0 → f ω ≤ c) : μ.expect f ≤ c := by
  have h1 : μ.expect f ≤ μ.expect (fun _ => c) := by
    unfold FiniteLaw.expect
    refine sum_le_sum fun ω _ => ?_
    rcases eq_or_ne (μ.weight ω) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (h ω h0) (μ.nonneg ω)
  rwa [FiniteLaw.expect_const] at h1

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ b, Fintype (X b)]
  [∀ b, DecidableEq (X b)] [∀ b, Nonempty (X b)]

omit [∀ b, Nonempty (X b)] in
/-- **The total variation of a tensor of positive records** is the product of their masses. -/
theorem totalVariation_tensorLaw (Λ : ∀ b, SlotMeasure (X b))
    (hΛ : ∀ b, IsPositiveRecord (Λ b)) :
    totalVariation (lawDensity (tensorLaw Λ)) = ∏ b, mass (Λ b) := by
  have hρ : lawDensity (tensorLaw Λ) = fun z => ∏ b, lawDensity (Λ b) (fun v => z v b) := by
    funext z
    exact Sarkozy.DensityDC.lawDensity_tensorLaw Λ z
  rw [hρ, totalVariation_prod]
  exact prod_congr rfl fun b _ => totalVariation_lawDensity_of_positive (hΛ b)

/-- **`lem:record:density-lp`, Hölder in `L^{72}` and over the index law, at one tensor energy
with relabelled inputs** (see the module docstring): if every `Λ_𝔟` is a positive record and the
averaged `72`-th moments of the inputs are at most `B` at every slot, then
`E_ω |∫ ∏_v a^ω_{fo v}(e⁻¹ z_v) d(⊗_𝔟 Λ_𝔟)(z)| ≤ (∏_𝔟 Λ_𝔟(1)) B`. -/
theorem expect_abs_tensor_le {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (Λ : ∀ b, SlotMeasure (X b)) (hΛ : ∀ b, IsPositiveRecord (Λ b))
    {Y : Type} [Fintype Y] [Nonempty Y] (e : Y ≃ (∀ b, X b)) (fo : Slot → Slot)
    (a : Ω → Slot → Y → ℝ) {B : ℝ}
    (hB : ∀ v, P.expect (fun ω => (FiniteLaw.uniform Y).moment 72 (a ω v)) ≤ B) :
    P.expect (fun ω => |multilinearIntegral (tensorLaw Λ)
        (fun v (x : ∀ b, X b) => a ω (fo v) (e.symm x))|) ≤ (∏ b, mass (Λ b)) * B := by
  set ρ := lawDensity (tensorLaw Λ) with hρdef
  have hρ : ρ = fun z => ∏ b, lawDensity (Λ b) (fun v => z v b) := by
    funext z
    exact Sarkozy.DensityDC.lawDensity_tensorLaw Λ z
  have hunif : selectedMarginalsUniform ρ := by
    rw [hρ]
    exact selectedMarginalsUniform_prod (fun b => lawDensity (Λ b))
      fun b => selectedMarginalsUniform_lawDensity (hΛ b)
  have hE : ∀ ω, multilinearIntegral (tensorLaw Λ)
      (fun v (x : ∀ b, X b) => a ω (fo v) (e.symm x)) =
      ∑ z, ρ z * ∏ v, (fun ω v (x : ∀ b, X b) => a ω (fo v) (e.symm x)) ω v (z v) := by
    intro ω
    unfold multilinearIntegral
    rw [apply_eq_sum_lawDensity']
  have hB' : ∀ v, P.expect (fun ω => (FiniteLaw.uniform (∀ b, X b)).moment 72
      ((fun ω v (x : ∀ b, X b) => a ω (fo v) (e.symm x)) ω v)) ≤ B := by
    intro v
    refine le_of_eq_of_le (FiniteLaw.expect_congr _ fun ω => ?_) (hB (fo v))
    exact moment_uniform_equiv e 72 (a ω (fo v))
  rw [FiniteLaw.expect_congr _ fun ω => congrArg abs (hE ω)]
  refine (expect_abs_signed_energy_le_moment P ρ hunif _ hB').trans (le_of_eq ?_)
  rw [hρdef, totalVariation_tensorLaw Λ hΛ]

end Tensor

end Sarkozy.LargeSums
