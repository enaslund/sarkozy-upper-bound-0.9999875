module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Cuts, VIII: tensor-product constants and weighted frames

`13_cuts_correlations.tex`, `subsec:cuts:blocks`.

* `card_le_of_log_prod_le`, `sum_inv_le_of_log_prod_le`: `lem:spec:tensorcomp` (c).
* `prod_ge_neg_of_mem_Icc`, `prod_one_add_le_exp`, `tensorcomp_scalar`: the scalar steps of
  `lem:spec:tensorcomp` (a), (b). The first says a product of numbers `λ_i ∈ [-g_i, 1 + b_i]` is at
  least `-g_i ∏_{j ≠ i} (1 + b_j)` for some `i`. The others are `∏ (1 + b_j) ≤ exp(∑ b_j)` and
  `g_p ∏_{p' ≠ p} (1 + b_{p'}) ≤ g b^{-1/2} ∏_{p'} (1 + b_{p'})`. The operator statements of
  (a) and (b) are in `Sarkozy.Cuts.TensorSpectrum`; they are proved without eigenvalues.
* `weighted_frame`: `lem:weighted-frame` (a) with the row-sum bound. Let
  `V_i : H_i → H` satisfy `|⟨V_i z, V_j z'⟩| ≤ G_{ij} ‖z‖ ‖z'‖` (that is,
  `‖V_i^* V_j‖ ≤ G_{ij}`), with `G` symmetric and nonnegative, and let `d_i ≥ 0`. Then the
  synthesis map `(z_i) ↦ ∑_i √d_i V_i z_i` has squared norm at most `max_i ∑_j G_{ij} d_j`.
  The bound by `λ_max(D^{1/2} G D^{1/2})` is `Sarkozy.Cuts.weighted_frame_psd` (in
  `Sarkozy.Cuts.Schur`), and part (c) (the Perron gate) is in `Sarkozy.Cuts.PerronGate`. Part (b)
  (Kronecker products) is in `Sarkozy.Cuts.FrameTensor` (two families) and
  `Sarkozy.Cuts.FramePi` (`n` families), for kernel operators between `L²` spaces of finite
  laws.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

/-! ### `lem:spec:tensorcomp` (c) -/

/-- **`lem:spec:tensorcomp` (c), first claim.** If every `p ∈ B` satisfies `p ≥ b > 1` and
`log ∏_{p ∈ B} p ≤ L`, then `|B| ≤ L / log b`. -/
theorem card_le_of_log_prod_le (B : Finset ℕ) {b : ℕ} {L : ℝ} (hb : 1 < b)
    (hB : ∀ p ∈ B, b ≤ p) (hL : Real.log (∏ p ∈ B, (p : ℝ)) ≤ L) :
    (B.card : ℝ) ≤ L / Real.log b := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  rw [Real.log_prod (fun p hp => by
    have := hB p hp
    have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    exact this.ne')] at hL
  rw [le_div_iff₀ hlogb]
  calc (B.card : ℝ) * Real.log b = ∑ p ∈ B, Real.log b := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ B, Real.log p := Finset.sum_le_sum (fun p hp => Real.log_le_log
        (by positivity) (by exact_mod_cast hB p hp))
    _ ≤ L := hL

/-- **`lem:spec:tensorcomp` (c), second claim.** Under the same hypotheses,
`∑_{p ∈ B} 1/p ≤ L / (b log b)`. -/
theorem sum_inv_le_of_log_prod_le (B : Finset ℕ) {b : ℕ} {L : ℝ} (hb : 1 < b)
    (hB : ∀ p ∈ B, b ≤ p) (hL : Real.log (∏ p ∈ B, (p : ℝ)) ≤ L) :
    ∑ p ∈ B, (1 : ℝ) / p ≤ L / (b * Real.log b) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hden : 0 < (b : ℝ) * Real.log b := mul_pos hb0 hlogb
  rw [Real.log_prod (fun p hp => by
    have := hB p hp
    have : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    exact this.ne')] at hL
  have key : ∀ p ∈ B, (1 : ℝ) / p ≤ Real.log p / (b * Real.log b) := by
    intro p hp
    have hbp : (b : ℝ) ≤ p := by exact_mod_cast hB p hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : Real.log b ≤ Real.log p := Real.log_le_log hb0 hbp
    rw [div_le_div_iff₀ hp0 hden]
    nlinarith
  calc ∑ p ∈ B, (1 : ℝ) / p ≤ ∑ p ∈ B, Real.log p / (b * Real.log b) := Finset.sum_le_sum key
    _ = (∑ p ∈ B, Real.log p) / (b * Real.log b) := by rw [Finset.sum_div]
    _ ≤ L / (b * Real.log b) := div_le_div_of_nonneg_right hL hden.le

/-! ### Scalar steps of `lem:spec:tensorcomp` (a), (b) -/

/-- `∏_j (1 + b_j) ≤ exp(∑_j b_j)` for `b_j ≥ 0`. -/
theorem prod_one_add_le_exp {ι : Type*} (s : Finset ι) (b : ι → ℝ) (hb : ∀ j ∈ s, 0 ≤ b j) :
    ∏ j ∈ s, (1 + b j) ≤ Real.exp (∑ j ∈ s, b j) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun j hj => by linarith [hb j hj]) (fun j _ => ?_)
  linarith [Real.add_one_le_exp (b j)]

/-- **`lem:spec:tensorcomp` (b), scalar step.** If `g_p ≤ g'` and `b_{p'} ≥ 0`, then
`g_p ∏_{p' ≠ p} (1 + b_{p'}) ≤ g' ∏_{p'} (1 + b_{p'}) ≤ g' exp(∑ b_{p'})`. -/
theorem tensorcomp_scalar {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ j ∈ s, 0 ≤ b j) {i : ι} (hi : i ∈ s) {gi g' : ℝ} (hgi : 0 ≤ gi) (hg : gi ≤ g') :
    gi * ∏ j ∈ s.erase i, (1 + b j) ≤ g' * ∏ j ∈ s, (1 + b j) ∧
      g' * ∏ j ∈ s, (1 + b j) ≤ g' * Real.exp (∑ j ∈ s, b j) := by
  have hpos : ∀ j ∈ s, 0 ≤ 1 + b j := fun j hj => by linarith [hb j hj]
  have h1 : ∏ j ∈ s.erase i, (1 + b j) ≤ ∏ j ∈ s, (1 + b j) := by
    rw [← Finset.mul_prod_erase s (fun j => 1 + b j) hi]
    have h0 : 0 ≤ ∏ j ∈ s.erase i, (1 + b j) :=
      Finset.prod_nonneg (fun j hj => hpos j (Finset.mem_of_mem_erase hj))
    nlinarith [hb i hi]
  have hg0 : 0 ≤ g' := hgi.trans hg
  refine ⟨?_, mul_le_mul_of_nonneg_left (prod_one_add_le_exp s b hb) hg0⟩
  exact mul_le_mul hg h1 (Finset.prod_nonneg (fun j hj => hpos j (Finset.mem_of_mem_erase hj)))
    hg0

/-- **`lem:spec:tensorcomp` (a), scalar core.** Let `λ_i ∈ [-g_i, 1 + b_i]` with
`0 ≤ g_i ≤ 1 + b_i`. If `∏_i λ_i < 0`, then some `i` has `∏_i λ_i ≥ -g_i ∏_{j ≠ i} (1 + b_j)`.
Applied to the eigenvalues of `⊗_i C_i`, which are the products of eigenvalues of the factors,
this gives the lower bound of (a). -/
theorem prod_ge_neg_of_mem_Icc {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam g b : ι → ℝ)
    (hg0 : ∀ i ∈ s, 0 ≤ g i) (hgb : ∀ i ∈ s, g i ≤ 1 + b i) (hlo : ∀ i ∈ s, -g i ≤ lam i)
    (hhi : ∀ i ∈ s, lam i ≤ 1 + b i) (hneg : ∏ i ∈ s, lam i < 0) :
    ∃ i ∈ s, -(g i * ∏ j ∈ s.erase i, (1 + b j)) ≤ ∏ i ∈ s, lam i := by
  -- some factor is negative
  obtain ⟨i, hi, hli⟩ : ∃ i ∈ s, lam i < 0 := by
    by_contra h
    push Not at h
    exact absurd (Finset.prod_nonneg h) (not_le.mpr hneg)
  refine ⟨i, hi, ?_⟩
  have habs : ∀ j ∈ s, |lam j| ≤ 1 + b j := fun j hj => abs_le.mpr
    ⟨by linarith [hlo j hj, hgb j hj], hhi j hj⟩
  have hb0 : ∀ j ∈ s, 0 ≤ 1 + b j := fun j hj => (abs_nonneg _).trans (habs j hj)
  have hrest : |∏ j ∈ s.erase i, lam j| ≤ ∏ j ∈ s.erase i, (1 + b j) := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun j _ => abs_nonneg _)
      (fun j hj => habs j (Finset.mem_of_mem_erase hj))
  have hli' : |lam i| ≤ g i := by
    rw [abs_of_neg hli]
    linarith [hlo i hi]
  rw [← Finset.mul_prod_erase s lam hi]
  have hprod : |lam i * ∏ j ∈ s.erase i, lam j| ≤ g i * ∏ j ∈ s.erase i, (1 + b j) := by
    rw [abs_mul]
    exact mul_le_mul hli' hrest (abs_nonneg _) (hg0 i hi)
  linarith [neg_abs_le (lam i * ∏ j ∈ s.erase i, lam j)]

/-! ### `lem:weighted-frame` (a) -/

/-- The Schur test for a symmetric nonnegative matrix:
`∑_{i,j} G_{ij} √(d_i d_j) w_i w_j ≤ M ∑_i w_i²` when every row sum `∑_j G_{ij} d_j ≤ M`. -/
theorem schur_rowsum {ι : Type*} [Fintype ι] (G : ι → ι → ℝ) (hGs : ∀ i j, G i j = G j i)
    (hG0 : ∀ i j, 0 ≤ G i j) (d w : ι → ℝ) (hd : ∀ i, 0 ≤ d i) {M : ℝ}
    (hM : ∀ i, ∑ j, G i j * d j ≤ M) :
    ∑ i, ∑ j, G i j * (√(d i) * √(d j)) * (w i * w j) ≤ M * ∑ i, w i ^ 2 := by
  have hamgm : ∀ i j, G i j * (√(d i) * √(d j)) * (w i * w j) ≤
      G i j * (d j * w i ^ 2 + d i * w j ^ 2) / 2 := by
    intro i j
    have h1 := Real.sq_sqrt (hd i)
    have h2 := Real.sq_sqrt (hd j)
    have hsq : 0 ≤ (√(d j) * w i - √(d i) * w j) ^ 2 := sq_nonneg _
    have : 2 * (√(d i) * √(d j)) * (w i * w j) ≤ d j * w i ^ 2 + d i * w j ^ 2 := by
      nlinarith
    have := mul_le_mul_of_nonneg_left this (hG0 i j)
    linarith
  have hsplit : ∑ i, ∑ j, G i j * (d j * w i ^ 2 + d i * w j ^ 2) / 2 =
      ∑ i, w i ^ 2 * ∑ j, G i j * d j := by
    have e1 : ∑ i, ∑ j, G i j * (d j * w i ^ 2 + d i * w j ^ 2) / 2 =
        (∑ i, ∑ j, G i j * d j * w i ^ 2 + ∑ i, ∑ j, G i j * d i * w j ^ 2) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have e2 : ∑ i, ∑ j, G i j * d i * w j ^ 2 = ∑ i, ∑ j, G i j * d j * w i ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hGs]))
    rw [e1, e2]
    have e3 : ∀ i, ∑ j, G i j * d j * w i ^ 2 = w i ^ 2 * ∑ j, G i j * d j := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp only [e3]
    ring
  calc ∑ i, ∑ j, G i j * (√(d i) * √(d j)) * (w i * w j)
      ≤ ∑ i, ∑ j, G i j * (d j * w i ^ 2 + d i * w j ^ 2) / 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hamgm i j))
    _ = ∑ i, w i ^ 2 * ∑ j, G i j * d j := hsplit
    _ ≤ ∑ i, w i ^ 2 * M :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hM i) (sq_nonneg _))
    _ = M * ∑ i, w i ^ 2 := by rw [← Finset.sum_mul, mul_comm]

/-- **`lem:weighted-frame` (a), row-sum form.** Let `V_i : H_i → H` be linear maps between real
inner product spaces with `|⟨V_i z, V_j z'⟩| ≤ G_{ij} ‖z‖ ‖z'‖` (that is, `‖V_i^* V_j‖ ≤ G_{ij}`),
`G` symmetric and nonnegative, and `d_i ≥ 0`. If `∑_j G_{ij} d_j ≤ M` for every `i`, then
`‖∑_i √d_i V_i z_i‖² ≤ M ∑_i ‖z_i‖²`. -/
theorem weighted_frame {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (V : ∀ i, E i →ₗ[ℝ] F) (G : ι → ι → ℝ) (hGs : ∀ i j, G i j = G j i)
    (hG0 : ∀ i j, 0 ≤ G i j)
    (hV : ∀ i j (z : E i) (z' : E j), |inner ℝ (V i z) (V j z')| ≤ G i j * ‖z‖ * ‖z'‖)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) {M : ℝ} (hM : ∀ i, ∑ j, G i j * d j ≤ M)
    (z : ∀ i, E i) :
    ‖∑ i, √(d i) • V i (z i)‖ ^ 2 ≤ M * ∑ i, ‖z i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  refine le_trans ?_ (schur_rowsum G hGs hG0 d (fun i => ‖z i‖) hd hM)
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  have h := hV i j (z i) (z j)
  have hs : 0 ≤ √(d i) * √(d j) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have e : √(d j) * (√(d i) * inner ℝ (V i (z i)) (V j (z j))) =
      (√(d i) * √(d j)) * inner ℝ (V i (z i)) (V j (z j)) := by ring
  rw [e]
  calc (√(d i) * √(d j)) * inner ℝ (V i (z i)) (V j (z j))
      ≤ (√(d i) * √(d j)) * |inner ℝ (V i (z i)) (V j (z j))| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hs
    _ ≤ (√(d i) * √(d j)) * (G i j * ‖z i‖ * ‖z j‖) := mul_le_mul_of_nonneg_left h hs
    _ = G i j * (√(d i) * √(d j)) * (‖z i‖ * ‖z j‖) := by ring

end Sarkozy.Cuts
