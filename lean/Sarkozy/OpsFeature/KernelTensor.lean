module

public import Sarkozy.EnvelopeSteps.FeatureCorr

@[expose] public section

/-!
# The maximal correlation of a product of kernels (`lem:sector`(c), `cor:peyre-independent`)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`, proof Steps 1 and 4: for a product of
independent pairs, the maximal correlation of the products is the largest one-coordinate maximal
correlation (`cor:peyre-independent`; in the operator form, `lem:sector`(c)).

Here in the bilinear form for unnormalized nonnegative kernels `W_j(a, b)` on `A_j × B_j`, with the
marginal weights `W₀_j(a) = ∑_b W_j(a, b)`, `W₂_j(b) = ∑_a W_j(a, b)`: if every coordinate satisfies
`|∑ W_j f g| ≤ c √(∑ W₀_j f²) √(∑ W₂_j g²)` for `W₀_j`-centred `f` and `W₂_j`-centred `g`, `c ≤ 1`,
then the product kernel satisfies the same bound for `∏ W₀_j`-centred `X` and every `Y`
(**`kernel_tensor_corr`**). The proof normalizes the kernels to conditional expectation matrices
`T_j(b, a) = W_j(a, b)/W₂_j(b)` and applies Mixing's `general_markov_tensor_max` (whose source and
target laws may differ), as B11's `block_correlation` does for one law; zero marginal weights are
allowed.
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.OpsFeature

open Sarkozy.Mixing Sarkozy.EnvelopeSteps

section Kernel

variable {A B : Type*} [Fintype A] [Fintype B]

omit [Fintype B] in
/-- A nonnegative kernel vanishes on the columns of zero marginal weight. -/
theorem kernel_zero_of_marg {W : A → B → ℝ} (hW : ∀ a b, 0 ≤ W a b) {b : B}
    (hb : ∑ a, W a b = 0) (a : A) : W a b = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hW a b)).mp hb a (mem_univ a)

omit [Fintype B] in
/-- `W(a, b) = W₂(b) (W(a, b)/W₂(b))`, also where `W₂(b) = 0`. -/
theorem kernel_factor {W : A → B → ℝ} (hW : ∀ a b, 0 ≤ W a b) (a : A) (b : B) :
    W a b = (∑ a', W a' b) * (W a b / ∑ a', W a' b) := by
  by_cases hb : ∑ a', W a' b = 0
  · rw [kernel_zero_of_marg hW hb a, hb]; simp
  · field_simp

/-- **One coordinate, operator form**: the bilinear bound for centred functions gives
`∑ W₂ (T f)² ≤ c² ∑ W₀ f²` for `W₀`-centred `f`, `T f(b) = ∑_a W(a, b) f(a)/W₂(b)`. -/
theorem kernel_op_bound {W : A → B → ℝ} (hW : ∀ a b, 0 ≤ W a b) {c : ℝ} (hc : 0 ≤ c)
    (hprime : ∀ (f : A → ℝ) (g : B → ℝ), ∑ a, (∑ b, W a b) * f a = 0 →
      ∑ b, (∑ a, W a b) * g b = 0 →
      |∑ a, ∑ b, W a b * f a * g b| ≤
        c * (Real.sqrt (∑ a, (∑ b, W a b) * f a ^ 2) * Real.sqrt (∑ b, (∑ a, W a b) * g b ^ 2)))
    (f : A → ℝ) (hf : ∑ a, (∑ b, W a b) * f a = 0) :
    ∑ b, (∑ a, W a b) * (∑ a, W a b * f a / ∑ a', W a' b) ^ 2 ≤
      c ^ 2 * ∑ a, (∑ b, W a b) * f a ^ 2 := by
  set g : B → ℝ := fun b => ∑ a, W a b * f a / ∑ a', W a' b with hg
  have hWg : ∀ b, (∑ a, W a b) * g b = ∑ a, W a b * f a := by
    intro b
    simp only [hg]
    by_cases hb : ∑ a', W a' b = 0
    · rw [hb, zero_mul]
      exact (sum_eq_zero fun a _ => by rw [kernel_zero_of_marg hW hb a, zero_mul]).symm
    · rw [← sum_div, mul_div_cancel₀ _ hb]
  have hgc : ∑ b, (∑ a, W a b) * g b = 0 := by
    simp only [hWg]
    rw [sum_comm]
    simp only [← sum_mul]
    exact hf
  have hS : ∑ a, ∑ b, W a b * f a * g b = ∑ b, (∑ a, W a b) * g b ^ 2 := by
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [sq, ← mul_assoc, hWg, sum_mul]
  have h := hprime f g hf hgc
  rw [hS] at h
  set S := ∑ b, (∑ a, W a b) * g b ^ 2 with hSd
  set Q := ∑ a, (∑ b, W a b) * f a ^ 2 with hQd
  have hS0 : 0 ≤ S := sum_nonneg fun b _ =>
    mul_nonneg (sum_nonneg fun a _ => hW a b) (sq_nonneg _)
  have hQ0 : 0 ≤ Q := sum_nonneg fun a _ =>
    mul_nonneg (sum_nonneg fun b _ => hW a b) (sq_nonneg _)
  rw [abs_of_nonneg hS0] at h
  have hsS := Real.sq_sqrt hS0
  have hsQ := Real.sq_sqrt hQ0
  have hsS0 := Real.sqrt_nonneg S
  have hsQ0 := Real.sqrt_nonneg Q
  -- `√S ≤ c √Q`
  have hroot : Real.sqrt S ≤ c * Real.sqrt Q := by
    rcases hsS0.eq_or_lt with h0 | h0
    · rw [← h0]; exact mul_nonneg hc hsQ0
    · have : Real.sqrt S * Real.sqrt S ≤ c * Real.sqrt Q * Real.sqrt S := by
        rw [← sq, hsS]; linarith
      exact le_of_mul_le_mul_right this h0
  have := mul_self_le_mul_self hsS0 hroot
  nlinarith

end Kernel

section Tensor

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (B j)]

/-- **The maximal correlation of a product of kernels** (`lem:sector`(c),
`cor:peyre-independent`, bilinear form): if every coordinate kernel `W_j ≥ 0` (of positive mass)
has correlation at most `c ≤ 1` between its two marginals, so has the product kernel, for every
`∏ W₀_j`-centred `X` and every `Y`. -/
theorem kernel_tensor_corr (W : ∀ j, A j → B j → ℝ) (hW : ∀ j a b, 0 ≤ W j a b)
    (hZ : ∀ j, 0 < ∑ a, ∑ b, W j a b) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hprime : ∀ j (f : A j → ℝ) (g : B j → ℝ), ∑ a, (∑ b, W j a b) * f a = 0 →
      ∑ b, (∑ a, W j a b) * g b = 0 →
      |∑ a, ∑ b, W j a b * f a * g b| ≤
        c * (Real.sqrt (∑ a, (∑ b, W j a b) * f a ^ 2) *
          Real.sqrt (∑ b, (∑ a, W j a b) * g b ^ 2)))
    (X : (∀ j, A j) → ℝ) (Y : (∀ j, B j) → ℝ)
    (hX : ∑ a, (∏ j, ∑ b, W j (a j) b) * X a = 0) :
    |∑ a, ∑ b, (∏ j, W j (a j) (b j)) * X a * Y b| ≤
      c * (Real.sqrt (∑ a, (∏ j, ∑ b, W j (a j) b) * X a ^ 2) *
        Real.sqrt (∑ b, (∏ j, ∑ a, W j a (b j)) * Y b ^ 2)) := by
  set Z : K → ℝ := fun j => ∑ a, ∑ b, W j a b with hZd
  set π : ∀ j, A j → ℝ := fun j a => (∑ b, W j a b) / Z j with hπd
  set β : ∀ j, B j → ℝ := fun j b => (∑ a, W j a b) / Z j with hβd
  set T : ∀ j, Matrix (B j) (A j) ℝ := fun j b a => W j a b / ∑ a', W j a' b with hTd
  have hZ0 : ∀ j, Z j ≠ 0 := fun j => (hZ j).ne'
  have hπ : ∀ j a, 0 ≤ π j a := fun j a =>
    div_nonneg (sum_nonneg fun b _ => hW j a b) (hZ j).le
  have hβ : ∀ j b, 0 ≤ β j b := fun j b =>
    div_nonneg (sum_nonneg fun a _ => hW j a b) (hZ j).le
  have hπ1 : ∀ j, ∑ a, π j a = 1 := fun j => by
    simp only [hπd, ← sum_div]; exact div_self (hZ0 j)
  have hrow : ∀ j b, β j b ≠ 0 → ∑ a, T j b a = 1 := by
    intro j b hb
    have hb' : ∑ a', W j a' b ≠ 0 := by
      intro h; apply hb; simp only [hβd, h, zero_div]
    simp only [hTd, ← sum_div]
    exact div_self hb'
  -- the pointwise factorization `W = Z β T`
  have hfac : ∀ j a b, W j a b = Z j * (β j b * T j b a) := by
    intro j a b
    have := kernel_factor (hW j) a b
    simp only [hβd, hTd]
    rw [this]
    field_simp [hZ0 j]
  have hcol : ∀ j a, ∑ b, β j b * T j b a = π j a := by
    intro j a
    simp only [hπd]
    rw [eq_div_iff (hZ0 j), sum_mul]
    refine sum_congr rfl fun b _ => ?_
    rw [hfac j a b]; ring
  -- the coordinate bounds in operator form
  have hδ : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ c ^ 2 * ∑ a, π j a * f a ^ 2 := by
    intro j f hf
    have hf' : ∑ a, (∑ b, W j a b) * f a = 0 := by
      have : ∑ a, π j a * f a = (∑ a, (∑ b, W j a b) * f a) / Z j := by
        rw [sum_div]; exact sum_congr rfl fun a _ => by simp only [hπd]; ring
      rw [this, div_eq_zero_iff] at hf
      exact hf.resolve_right (hZ0 j)
    have h := kernel_op_bound (hW j) hc (hprime j) f hf'
    have e1 : ∀ b, (T j *ᵥ f) b = ∑ a, W j a b * f a / ∑ a', W j a' b := by
      intro b
      simp only [Matrix.mulVec, dotProduct, hTd]
      exact sum_congr rfl fun a _ => by ring
    simp only [e1, hβd, hπd]
    have e2 : ∀ (u : B j → ℝ),
        ∑ b, (∑ a, W j a b) / Z j * u b = (∑ b, (∑ a, W j a b) * u b) / Z j :=
      fun u => by rw [sum_div]; exact sum_congr rfl fun b _ => by ring
    have e3 : ∀ (u : A j → ℝ),
        ∑ a, (∑ b, W j a b) / Z j * u a = (∑ a, (∑ b, W j a b) * u a) / Z j :=
      fun u => by rw [sum_div]; exact sum_congr rfl fun a _ => by ring
    rw [e2 (fun b => (∑ a, W j a b * f a / ∑ a', W j a' b) ^ 2), e3 (fun a => f a ^ 2),
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h (hZ j).le
  have hcontr : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ 1 ^ 2 * ∑ a, π j a * f a ^ 2 := by
    intro j f hf
    have h := hδ j f hf
    have hs : 0 ≤ ∑ a, π j a * f a ^ 2 := sum_nonneg fun a _ => mul_nonneg (hπ j a) (sq_nonneg _)
    have hc2 : c ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hc hc1 2
    nlinarith
  have hglob := (general_markov_tensor_max π β T hπ hπ1 hβ hrow hcol hcontr hc).mpr hδ X
  -- the product normalization
  set P := ∏ j, Z j with hP
  have hP0 : 0 < P := prod_pos fun j _ => hZ j
  have hπX : ∀ a, prodW π a = (∏ j, ∑ b, W j (a j) b) / P := by
    intro a
    simp only [prodW, hπd, prod_div_distrib, hP]
  have hβY : ∀ b, prodW β b = (∏ j, ∑ a, W j a (b j)) / P := by
    intro b
    simp only [prodW, hβd, prod_div_distrib, hP]
  have hmean : ∑ a, prodW π a * X a = 0 := by
    simp only [hπX, div_mul_eq_mul_div, ← sum_div, hX, zero_div]
  rw [hmean] at hglob
  simp only [sub_zero] at hglob
  have hbil : ∑ a, ∑ b, (∏ j, W j (a j) (b j)) * X a * Y b =
      P * ∑ b, prodW β b * Y b * (prodOp T *ᵥ X) b := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    simp only [Matrix.mulVec, dotProduct, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have e : ∏ j, W j (a j) (b j) = P * (prodW β b * prodOp T b a) := by
      simp only [hfac, prod_mul_distrib, hP, prodW, prodOp]
    rw [e]
    ring
  have hw : ∀ b ∈ (univ : Finset (∀ j, B j)), 0 ≤ prodW β b :=
    fun b _ => prod_nonneg fun j _ => hβ j (b j)
  have hcs := abs_wsum_le univ (prodW β) Y (prodOp T *ᵥ X) hw
  have hsq : Real.sqrt (∑ b, prodW β b * (prodOp T *ᵥ X) b ^ 2) ≤
      c * Real.sqrt (∑ a, prodW π a * X a ^ 2) := by
    rw [← Real.sqrt_sq hc, ← Real.sqrt_mul (sq_nonneg c)]
    exact Real.sqrt_le_sqrt hglob
  set SX := ∑ a, (∏ j, ∑ b, W j (a j) b) * X a ^ 2 with hSX
  set SY := ∑ b, (∏ j, ∑ a, W j a (b j)) * Y b ^ 2 with hSY
  have eX : ∑ a, prodW π a * X a ^ 2 = SX / P := by
    simp only [hπX, hSX, sum_div]; exact sum_congr rfl fun a _ => by ring
  have eY : ∑ b, prodW β b * Y b ^ 2 = SY / P := by
    simp only [hβY, hSY, sum_div]; exact sum_congr rfl fun b _ => by ring
  rw [eX] at hsq
  rw [eY] at hcs
  have hSX0 : 0 ≤ SX := sum_nonneg fun a _ =>
    mul_nonneg (prod_nonneg fun j _ => sum_nonneg fun b _ => hW j _ b) (sq_nonneg _)
  have hSY0 : 0 ≤ SY := sum_nonneg fun b _ =>
    mul_nonneg (prod_nonneg fun j _ => sum_nonneg fun a _ => hW j a _) (sq_nonneg _)
  rw [hbil, abs_mul, abs_of_pos hP0]
  have hsP : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP0.le
  have hsP0 : 0 < Real.sqrt P := Real.sqrt_pos.2 hP0
  rw [Real.sqrt_div' _ hP0.le] at hsq hcs
  calc P * |∑ b, prodW β b * Y b * (prodOp T *ᵥ X) b|
      ≤ P * (Real.sqrt SY / Real.sqrt P *
          Real.sqrt (∑ b, prodW β b * (prodOp T *ᵥ X) b ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hP0.le
    _ ≤ P * (Real.sqrt SY / Real.sqrt P * (c * (Real.sqrt SX / Real.sqrt P))) := by
        apply mul_le_mul_of_nonneg_left _ hP0.le
        exact mul_le_mul_of_nonneg_left hsq (div_nonneg (Real.sqrt_nonneg _) hsP0.le)
    _ = c * (Real.sqrt SX * Real.sqrt SY) * (P / (Real.sqrt P * Real.sqrt P)) := by ring
    _ = c * (Real.sqrt SX * Real.sqrt SY) := by rw [hsP, div_self hP0.ne', mul_one]

end Tensor

end Sarkozy.OpsFeature
