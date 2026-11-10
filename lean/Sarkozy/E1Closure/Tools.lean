module

public import Sarkozy.LargeSums.All

@[expose] public section

/-!
# Three generic steps of `lem:record:density-lp` at the (E1) terms (EC)

EC, 8 November 2026.

* **`abs_diag_le_dom`** (Hölder in `L^{72}` with the uniform one-slot marginals, the first step of
  the proof of `lem:record:density-lp`): if every atom law `Λ_𝔟` is dominated pointwise in density
  by a positive record `ν_𝔟`, then `|∫ ∏_v g(z_v) d(⊗_𝔟 Λ_𝔟)(z)| ≤ (∏_𝔟 ν_𝔟(1)) ‖g‖_{72}^{72}`.
  The domination handles the whole differences `κ' − κ` (dominated by `κ' + κ`) without the
  Jordan parts, as in `lem:sharp-first` ("not into its Jordan parts, whose marginals need not be
  uniform"). It is LP's `expect_abs_tensor_le` at a one-point index law, after the triangle
  inequality.
* **`rankin_term`** (Rankin's trick): if `T < ∏_𝔟 q_𝔟`, then
  `∏_𝔟 w_𝔟 ≤ T^{-1/4} ∏_𝔟 w_𝔟 q_𝔟^{1/4}`.
* **`sum_sum_prod`**: `∑_ω ∑_f ∏_𝔟 g_𝔟(ω_𝔟, f_𝔟) = ∏_𝔟 ∑_o ∑_y g_𝔟(o, y)` (the sums over
  the selections and the pieces factor over the atoms).
-/

namespace Sarkozy.E1Closure

open Finset Function
open scoped BigOperators
open Sarkozy.TheoremC Sarkozy.Structured ReflectionCut

section Holder

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} [∀ b, Fintype (X b)]
  [∀ b, DecidableEq (X b)] [∀ b, Nonempty (X b)]

omit [∀ b, Nonempty (X b)] in
/-- The diagonal integral of a tensor law, in coordinates. -/
theorem diag_tensor_eq (Λ : ∀ b, SlotMeasure (X b)) (g : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw Λ) g =
      ∑ z : ∀ b, Slot → X b, (∏ b, lawDensity (Λ b) (z b)) * ∏ v, g (fun b => z b v) := rfl

/-- **`lem:record:density-lp`, Hölder step, with a dominating positive record per atom.** -/
theorem abs_diag_le_dom (Λ ν : ∀ b, SlotMeasure (X b)) (hν : ∀ b, IsPositiveRecord (ν b))
    (hdom : ∀ b z, |lawDensity (Λ b) z| ≤ lawDensity (ν b) z)
    (g : (∀ b, X b) → ℝ) {B : ℝ} (hB : (FiniteLaw.uniform (∀ b, X b)).moment 72 g ≤ B) :
    |diagonalIntegral (tensorLaw Λ) g| ≤ (∏ b, mass (ν b)) * B := by
  have h1 : |diagonalIntegral (tensorLaw Λ) g| ≤
      diagonalIntegral (tensorLaw ν) (fun x => |g x|) := by
    rw [diag_tensor_eq, diag_tensor_eq]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun z _ => ?_)
    rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
    exact mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun b _ => abs_nonneg _) fun b _ => hdom b (z b))
      (prod_nonneg fun v _ => abs_nonneg _)
  have h2 := Sarkozy.LargeSums.expect_abs_tensor_le (FiniteLaw.uniform Unit) ν hν
    (Equiv.refl (∀ b, X b)) id (fun _ _ y => |g y|) (B := B) (fun v => by
      rw [FiniteLaw.expect_const]
      refine le_of_eq_of_le ?_ hB
      unfold FiniteLaw.moment
      simp only [abs_abs])
  rw [FiniteLaw.expect_const] at h2
  refine h1.trans (le_trans (le_abs_self _) (le_of_eq_of_le ?_ h2))
  rfl

end Holder

/-- **Rankin's trick, one term**: if `T < ∏_𝔟 q_𝔟` (all `q_𝔟, w_𝔟 ≥ 0`, `T > 0`), then
`∏_𝔟 w_𝔟 ≤ T^{-1/4} ∏_𝔟 w_𝔟 q_𝔟^{1/4}`. -/
theorem rankin_term {ι : Type*} (s : Finset ι) (w q : ι → ℝ) (hw : ∀ b ∈ s, 0 ≤ w b)
    (hq : ∀ b ∈ s, 0 ≤ q b) {T : ℝ} (hT : 0 < T) (hlarge : T < ∏ b ∈ s, q b) :
    ∏ b ∈ s, w b ≤ T ^ (-((1 : ℝ) / 4)) * ∏ b ∈ s, (w b * q b ^ ((1 : ℝ) / 4)) := by
  have hQ : T ^ ((1 : ℝ) / 4) ≤ (∏ b ∈ s, q b) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hT.le hlarge.le (by norm_num)
  have hprod : (∏ b ∈ s, q b) ^ ((1 : ℝ) / 4) = ∏ b ∈ s, q b ^ ((1 : ℝ) / 4) :=
    (Real.finsetProd_rpow s q hq _).symm
  have hone : 1 ≤ T ^ (-((1 : ℝ) / 4)) * ∏ b ∈ s, q b ^ ((1 : ℝ) / 4) := by
    rw [← hprod, Real.rpow_neg hT.le]
    have hT4 : 0 < T ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hT _
    rw [inv_mul_eq_div, le_div_iff₀ hT4, one_mul]
    exact hQ
  have hw0 : 0 ≤ ∏ b ∈ s, w b := prod_nonneg hw
  calc ∏ b ∈ s, w b ≤ (∏ b ∈ s, w b) * (T ^ (-((1 : ℝ) / 4)) * ∏ b ∈ s, q b ^ ((1 : ℝ) / 4)) :=
        le_mul_of_one_le_right hw0 hone
    _ = T ^ (-((1 : ℝ) / 4)) * ∏ b ∈ s, (w b * q b ^ ((1 : ℝ) / 4)) := by
        rw [prod_mul_distrib]
        ring

/-- **The sums over the selections and the pieces factor over the atoms.** -/
theorem sum_sum_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : ι → Type*}
    [∀ b, Fintype (X b)] [∀ b, Fintype (Y b)] (g : ∀ b, X b → Y b → ℝ) :
    ∑ ω : (∀ b, X b), ∑ f : (∀ b, Y b), ∏ b, g b (ω b) (f b) = ∏ b, ∑ o, ∑ y, g b o y := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun ω _ => ?_
  rw [Fintype.prod_sum]

end Sarkozy.E1Closure
