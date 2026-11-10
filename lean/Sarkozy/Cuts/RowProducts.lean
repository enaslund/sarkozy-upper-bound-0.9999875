module

public import Sarkozy.Cuts.Rows
public import Sarkozy.Cuts.CutBlock
public import Sarkozy.Cuts.Tilt

/-!
# Cuts, II′: products of row couplings (`lem:row-comparison` (c))

`13_cuts_correlations.tex`, `lem:row-comparison` (c). Let `X = ∏_i X_i`, `ν = ⊗_i ν_i` and
`π = ⊗_i π_i` (`prodCoupling`, a law on `X × X`).

* `prodCoupling_marginals`: `r_L = ∏_i r_{L,i}` and `r_R = ∏_i r_{R,i}`.
* `chiSq_tensor_eq`: `1 + ‖r - 1‖² = ∏_i (1 + ‖r_i - 1‖²)` for densities of mean one.
* `marginal_density_mean`: marginal densities have mean one.

The remaining clause, `ρ_π = max_i ρ_{π_i}`, is `Sarkozy.Cuts.maxCorr_prodCoupling` in
`Sarkozy.Cuts.RowCorrelation`, via Peyre's theorem for independent pairs.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering

section Single

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω Ξ : ι → Type*} [∀ i, Fintype (Ω i)]
  [∀ i, Fintype (Ξ i)] [∀ i, DecidableEq (Ξ i)]

/-- **Products of image laws.** If under `λ_i` the map `T_i` has the law `k_i μ_i`, then under
`⊗_i λ_i` the product map has the law `(∏_i k_i) ⊗_i μ_i`. -/
theorem pi_single_law (lam : ∀ i, FiniteLaw (Ω i)) (μ : ∀ i, FiniteLaw (Ξ i))
    (T : ∀ i, Ω i → Ξ i) (k : ∀ i, Ξ i → ℝ)
    (hone : ∀ i a, (lam i).expect (fun y => if T i y = a then (1 : ℝ) else 0) =
      (μ i).weight a * k i a)
    (Φ : (∀ i, Ξ i) → ℝ) :
    (FiniteLaw.pi lam).expect (fun y => Φ (fun i => T i (y i))) =
      (FiniteLaw.pi μ).expect (fun ξ => (∏ i, k i (ξ i)) * Φ ξ) := by
  have hexp : ∀ y : ∀ i, Ω i, Φ (fun i => T i (y i)) =
      ∑ ξ, Φ ξ * ∏ i, (if T i (y i) = ξ i then (1 : ℝ) else 0) := by
    intro y
    rw [fun_eq_sum_indicator Φ]
    refine Finset.sum_congr rfl (fun ξ _ => ?_)
    rw [indicator_pi_eq ξ (fun i => T i (y i))]
  simp only [hexp]
  rw [Sarkozy.Peyre.expect_sum]
  simp only [FiniteLaw.expect_const_mul]
  have hprod : ∀ ξ : ∀ i, Ξ i, (FiniteLaw.pi lam).expect
      (fun y => ∏ i, (if T i (y i) = ξ i then (1 : ℝ) else 0)) =
      ∏ i, ((μ i).weight (ξ i) * k i (ξ i)) := by
    intro ξ
    rw [FiniteLaw.expect_pi_product lam (fun i y => if T i y = ξ i then (1 : ℝ) else 0)]
    exact Finset.prod_congr rfl (fun i _ => hone i (ξ i))
  simp only [hprod]
  unfold FiniteLaw.expect
  refine Finset.sum_congr rfl (fun ξ _ => ?_)
  rw [Finset.prod_mul_distrib]
  change Φ ξ * ((∏ i, (μ i).weight (ξ i)) * ∏ i, k i (ξ i)) =
    (∏ i, (μ i).weight (ξ i)) * ((∏ i, k i (ξ i)) * Φ ξ)
  ring

end Single

section Couplings

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  [∀ i, DecidableEq (X i)]

/-- The product coupling `⊗_i π_i`, a law on `(∏_i X_i) × (∏_i X_i)`. -/
noncomputable def prodCoupling (π : ∀ i, FiniteLaw (X i × X i)) :
    FiniteLaw ((∀ i, X i) × (∀ i, X i)) :=
  (FiniteLaw.pi π).map (fun q => (fun i => (q i).1, fun i => (q i).2))

omit [DecidableEq ι] [∀ i, DecidableEq (X i)] in
/-- Marginal densities have mean one. -/
theorem marginal_density_mean {Y : Type*} [Fintype Y] (ν : FiniteLaw Y) (π : FiniteLaw (Y × Y))
    {rL rR : Y → ℝ} (hr : HasMarginalDensities ν π rL rR) :
    ν.expect rL = 1 ∧ ν.expect rR = 1 := by
  have h1 := hr.left (fun _ => 1)
  have h2 := hr.right (fun _ => 1)
  simp only [mul_one, FiniteLaw.expect_const] at h1 h2
  exact ⟨h1.symm.trans (by rfl), h2.symm.trans (by rfl)⟩

/-- **`lem:row-comparison` (c).** The marginal densities of a product coupling are the products
of the marginal densities: `r_L = ∏_i r_{L,i}`, `r_R = ∏_i r_{R,i}`. -/
theorem prodCoupling_marginals (ν : ∀ i, FiniteLaw (X i)) (π : ∀ i, FiniteLaw (X i × X i))
    (rL rR : ∀ i, X i → ℝ) (hr : ∀ i, HasMarginalDensities (ν i) (π i) (rL i) (rR i)) :
    HasMarginalDensities (FiniteLaw.pi ν) (prodCoupling π) (fun x => ∏ i, rL i (x i))
      (fun x => ∏ i, rR i (x i)) := by
  have hind : ∀ (r : ∀ i, X i → ℝ) (i : ι) (a : X i),
      (ν i).expect (fun x => r i x * (if x = a then (1 : ℝ) else 0)) = (ν i).weight a * r i a := by
    intro r i a
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  constructor
  · intro φ
    unfold prodCoupling
    rw [FiniteLaw.expect_map]
    exact pi_single_law π ν (fun i q => q.1) rL
      (fun i a => by rw [(hr i).left (fun x => if x = a then (1 : ℝ) else 0), hind rL i a]) φ
  · intro φ
    unfold prodCoupling
    rw [FiniteLaw.expect_map]
    exact pi_single_law π ν (fun i q => q.2) rR
      (fun i a => by rw [(hr i).right (fun x => if x = a then (1 : ℝ) else 0), hind rR i a]) φ

omit [∀ i, DecidableEq (X i)] in
/-- **`lem:row-comparison` (c).** For densities `g_i` of mean one,
`1 + ‖⊗_i g_i - 1‖² = ∏_i (1 + ‖g_i - 1‖²)`. -/
theorem chiSq_tensor_eq (ν : ∀ i, FiniteLaw (X i)) (g : ∀ i, X i → ℝ)
    (hg1 : ∀ i, (ν i).expect (g i) = 1) :
    1 + (FiniteLaw.pi ν).expect (fun x => (∏ i, g i (x i) - 1) ^ 2) =
      ∏ i, (1 + (ν i).expect (fun y => (g i y - 1) ^ 2)) := by
  have hsq : ∀ i, (ν i).expect (fun y => g i y ^ 2) =
      1 + (ν i).expect (fun y => (g i y - 1) ^ 2) := by
    intro i
    have e : (fun y => (g i y - 1) ^ 2) = fun y => (g i y ^ 2 - 2 * g i y) + 1 := by
      funext y; ring
    rw [e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const, hg1 i]
    ring
  have e1 : (FiniteLaw.pi ν).expect (fun x => (∏ i, g i (x i) - 1) ^ 2) =
      (FiniteLaw.pi ν).expect (fun x => ∏ i, g i (x i) ^ 2) -
        2 * (FiniteLaw.pi ν).expect (fun x => ∏ i, g i (x i)) + 1 := by
    have e : (fun x : ∀ i, X i => (∏ i, g i (x i) - 1) ^ 2) =
        fun x => (∏ i, g i (x i) ^ 2 - 2 * ∏ i, g i (x i)) + 1 := by
      funext x
      rw [Finset.prod_pow]
      ring
    rw [e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const]
  rw [e1, FiniteLaw.expect_pi_product ν (fun i y => g i y ^ 2), FiniteLaw.expect_pi_product ν g]
  simp only [hg1, Finset.prod_const_one, hsq]
  ring

end Couplings

end Sarkozy.Cuts
