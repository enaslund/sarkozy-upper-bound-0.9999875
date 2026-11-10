module

public import Sarkozy.JointRows.PaleyAllPrimes

/-!
# Centred star features at both odd prime classes

The covariance Gram bound and the Schur product argument need only the
Paley contraction. Thus every nonempty exact leaf support has feature
norm at most sqrt(kappa/p), with no restriction modulo four.
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]

theorem gam_quad_le_odd (hp : p ≠ 2) (ν : FiniteLaw (ZMod p)) {κ : ℝ}
    (hκ : ∀ a, ν.weight a ≤ κ / p) (h : ZMod p → ℝ) :
    ∑ t, ∑ t', h t * gam ν t t' * h t' ≤ κ * ∑ t, h t * h t := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hκ0 : 0 ≤ κ := by
    have := (ν.nonneg 0).trans (hκ 0)
    rwa [le_div_iff₀ hp0, zero_mul] at this
  rw [gam_quad]
  simp only [sum_mul_phi]
  have h2 : ν.expect (fun a => (Real.sqrt p * (paley p h a - ν.expect (paley p h))) ^ 2) =
      p * (ν.expect (fun a => paley p h a ^ 2) - ν.expect (paley p h) ^ 2) := by
    rw [show (fun a => (Real.sqrt p * (paley p h a - ν.expect (paley p h))) ^ 2) =
        fun a => (p : ℝ) * (paley p h a - ν.expect (paley p h)) ^ 2 from
        funext fun a => by rw [mul_pow, Real.sq_sqrt hp0.le]]
    rw [FiniteLaw.expect_const_mul, FiniteLaw.expect_sq_sub_mean]
  rw [h2]
  have h3 : ν.expect (fun a => paley p h a ^ 2) ≤ κ / p * ∑ a, paley p h a * paley p h a := by
    unfold FiniteLaw.expect
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => by
      simp only [sq]; exact mul_le_mul_of_nonneg_right (hκ a) (mul_self_nonneg _)
  have h4 := sum_paley_sq_le_odd hp h
  have h5 := sq_nonneg (ν.expect (paley p h))
  calc (p : ℝ) * (ν.expect (fun a => paley p h a ^ 2) - ν.expect (paley p h) ^ 2)
      ≤ p * ν.expect (fun a => paley p h a ^ 2) := by nlinarith
    _ ≤ p * (κ / p * ∑ a, paley p h a * paley p h a) := mul_le_mul_of_nonneg_left h3 hp0.le
    _ = κ * ∑ a, paley p h a * paley p h a := by field_simp
    _ ≤ κ * ∑ t, h t * h t := mul_le_mul_of_nonneg_left h4 hκ0

theorem gamMat_le_odd (hp : p ≠ 2) (ν : FiniteLaw (ZMod p)) {κ : ℝ}
    (hκ : ∀ a, ν.weight a ≤ κ / p) :
    (κ • (1 : Matrix (ZMod p) (ZMod p) ℝ) - gamMat ν).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (IsHermitian.ext fun i j => ?_) fun x => ?_
  · simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, gamMat, Matrix.of_apply,
      star_trivial, smul_eq_mul]
    rw [gam_comm ν j i]
    by_cases hij : i = j
    · subst hij; rfl
    · simp only [Ne.symm hij, hij, ↓reduceIte]
  · simp only [star_trivial]
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, quad_eq]
    simp only [gamMat, of_apply]
    have := gam_quad_le_odd hp ν hκ x
    have hd : x ⬝ᵥ x = ∑ t, x t * x t := rfl
    rw [hd]
    linarith

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **`‖W_S‖ ≤ √κ r`** (Step 1): if the coordinate laws `ν_i`, `i ∈ S`, have densities at most
`κ` (`ν_i(a) ≤ κ/p`) and `S ≠ ∅`, then `‖W_S f‖²_{ν_X} ≤ κ r² ‖f‖²`, `r² = 1/p`. -/
theorem wOp_norm_le_odd (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p)) (S : Finset X)
    (hS : S.Nonempty) {κ : ℝ} (hκ : ∀ i ∈ S, ∀ a, (νp i).weight a ≤ κ / p) (f : ZMod p → ℝ) :
    ip (blockLaw νp) (wOp νp S f) (wOp νp S f) ≤
      κ * (p : ℝ)⁻¹ * ip (FiniteLaw.uniform (ZMod p)) f f := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨i₁, hi₁⟩ := hS
  have hκ0 : 0 ≤ κ := by
    have := ((νp i₁).nonneg 0).trans (hκ i₁ hi₁ 0)
    rwa [le_div_iff₀ hp0, zero_mul] at this
  have hP := Star.prod_gamma_le S hi₁ (fun i => gamMat (νp i)) (fun i _ => gamMat_posSemidef _)
    (fun i _ t => gam_self_le_one _ _) hκ0 (gamMat_le_odd hp _ (hκ i₁ hi₁))
  have hq := hP.dotProduct_mulVec_nonneg f
  simp only [star_trivial] at hq
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    quad_eq] at hq
  simp only [of_apply, gamMat] at hq
  have hd : f ⬝ᵥ f = ∑ t, f t * f t := rfl
  rw [hd] at hq
  rw [wOp_gram]
  simp only [FiniteLaw.expect_uniform, ZMod.card, ip]
  rw [Finset.sum_div]
  have hs : ∑ t, (∑ t', f t * f t' * ∏ i ∈ S, gam (νp i) t t') / p / p =
      (∑ t, ∑ t', f t * (∏ i ∈ S, gam (νp i) t t') * f t') / p / p := by
    rw [← Finset.sum_div, ← Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => by ring
  rw [hs]
  rw [div_div, show κ * (p : ℝ)⁻¹ * ((∑ t, f t * f t) / p) = κ * (∑ t, f t * f t) / (p * p) by
    field_simp]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end Sarkozy.JointRows.StarOps
