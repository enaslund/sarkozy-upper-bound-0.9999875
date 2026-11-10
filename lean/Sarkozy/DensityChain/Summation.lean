module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# The summations of the density chain over the terms of the bracket expansion

The first bounds of `lem:bracket-energy` are indexed by pairs of choice functions `(f, g)` on the
atoms (`f`: the atoms carrying the increment `Q`, `g ⊥ f`: those carrying a reserved record).
Each chain-covered term contributes `∏_{f ∪ g} ‖Λ_𝔟‖ · C_dc L^{-σ} α`, and each term with a large
selected modulus is bounded by `lem:record:density-lp`. This file proves the two summations, for
any per-atom weights `G 𝔟 x y` (`x = f 𝔟`, `y = g 𝔟`):

* **`sum_choice_prod_le`** (the summation of the chain remainders):
  `∑_f ∑_{g ∈ S f} ∏_𝔟 G(𝔟, f 𝔟, g 𝔟) ≤ ∏_𝔟 ∑_{x,y} G(𝔟, x, y)`, for nonnegative `G` and any
  family of sets `S f`;
* **`sum_choice_large_le`** (Rankin's trick in `lem:record:density-lp`): if every term of a
  subfamily has `T < ∏_{𝔟 ∈ f ∪ g} w_𝔟`, then its sum is at most
  `T^{-1/4} ∏_𝔟 ∑_{x,y} G(𝔟, x, y) w_𝔟^{[x ∨ y]/4}`;
* **`prod_one_add_le_exp`**: `∏ (1 + x_𝔟) ≤ exp(∑ x_𝔟)` for `x ≥ 0`, which turns the price totals of
  the data (`∑ u ≤ U₀`, `∑ envPrice ≤ T`) into the uniform constants of the summation.
-/

namespace Sarkozy.DensityChain

open Finset
open scoped BigOperators

/-- A sum over choice functions of a product is the product of the sums. -/
theorem sum_fun_prod_eq_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → Bool → ℝ) :
    ∑ f : ι → Bool, ∏ b, K b (f b) = ∏ b, ∑ x, K b x := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **The summation over the terms of the bracket expansion.** -/
theorem sum_choice_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → Bool → Bool → ℝ)
    (hG : ∀ b x y, 0 ≤ G b x y) (S : (ι → Bool) → Finset (ι → Bool)) :
    ∑ f, ∑ g ∈ S f, ∏ b, G b (f b) (g b) ≤ ∏ b, ∑ x, ∑ y, G b x y := by
  calc ∑ f, ∑ g ∈ S f, ∏ b, G b (f b) (g b)
      ≤ ∑ f : ι → Bool, ∑ g : ι → Bool, ∏ b, G b (f b) (g b) :=
        sum_le_sum fun f _ => sum_le_univ_sum_of_nonneg fun g => prod_nonneg fun b _ => hG _ _ _
    _ = ∑ f : ι → Bool, ∏ b, ∑ y, G b (f b) y := by
        apply sum_congr rfl
        intro f _
        exact sum_fun_prod_eq_prod_sum (fun b y => G b (f b) y)
    _ = ∏ b, ∑ x, ∑ y, G b x y := sum_fun_prod_eq_prod_sum (fun b x => ∑ y, G b x y)

/-- The quarter power of a selected product. -/
theorem prod_ite_rpow {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ b, 0 ≤ w b) (f g : ι → Bool) :
    (∏ b, (if (f b || g b) = true then w b else 1)) ^ ((1 : ℝ) / 4) =
      ∏ b, (if (f b || g b) = true then w b ^ ((1 : ℝ) / 4) else 1) := by
  rw [← Real.finsetProd_rpow _ _ (fun b _ => by split_ifs; exacts [hw b, zero_le_one])]
  apply prod_congr rfl
  intro b _
  split_ifs
  · rfl
  · exact Real.one_rpow _

/-- **Rankin's trick** (`lem:record:density-lp`): the terms whose selected product exceeds `T`
sum to at most `T^{-1/4}` times the `w^{1/4}`-weighted product. -/
theorem sum_choice_large_le {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → Bool → Bool → ℝ)
    (hG : ∀ b x y, 0 ≤ G b x y) (w : ι → ℝ) (hw : ∀ b, 0 ≤ w b) {T : ℝ} (hT : 0 < T)
    (S : (ι → Bool) → Finset (ι → Bool))
    (hlarge : ∀ f, ∀ g ∈ S f, T < ∏ b, (if (f b || g b) = true then w b else 1)) :
    ∑ f, ∑ g ∈ S f, ∏ b, G b (f b) (g b) ≤
      T ^ (-((1 : ℝ) / 4)) *
        ∏ b, ∑ x, ∑ y, G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1) := by
  have hT4 : 0 < T ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hT _
  have hTinv : T ^ (-((1 : ℝ) / 4)) = (T ^ ((1 : ℝ) / 4))⁻¹ := Real.rpow_neg hT.le _
  have hpt : ∀ f, ∀ g ∈ S f, ∏ b, G b (f b) (g b) ≤
      T ^ (-((1 : ℝ) / 4)) * ∏ b, (G b (f b) (g b) *
        (if (f b || g b) = true then w b ^ ((1 : ℝ) / 4) else 1)) := by
    intro f g hg
    have h1 : T ^ ((1 : ℝ) / 4) ≤
        ∏ b, (if (f b || g b) = true then w b ^ ((1 : ℝ) / 4) else 1) := by
      rw [← prod_ite_rpow w hw f g]
      exact Real.rpow_le_rpow hT.le (hlarge f g hg).le (by norm_num)
    have h2 : 1 ≤ T ^ (-((1 : ℝ) / 4)) *
        ∏ b, (if (f b || g b) = true then w b ^ ((1 : ℝ) / 4) else 1) := by
      rw [hTinv, ← div_eq_inv_mul, le_div_iff₀ hT4, one_mul]
      exact h1
    rw [prod_mul_distrib, ← mul_assoc, mul_comm (T ^ _) (∏ b, G b (f b) (g b)), mul_assoc]
    have h0 : 0 ≤ ∏ b, G b (f b) (g b) := prod_nonneg fun b _ => hG _ _ _
    nlinarith
  have hG' : ∀ b x y, 0 ≤ G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1) := by
    intro b x y
    apply mul_nonneg (hG b x y)
    split_ifs
    · exact Real.rpow_nonneg (hw b) _
    · exact zero_le_one
  calc ∑ f, ∑ g ∈ S f, ∏ b, G b (f b) (g b)
      ≤ ∑ f, ∑ g ∈ S f, T ^ (-((1 : ℝ) / 4)) * ∏ b, (G b (f b) (g b) *
          (if (f b || g b) = true then w b ^ ((1 : ℝ) / 4) else 1)) :=
        sum_le_sum fun f _ => sum_le_sum fun g hg => hpt f g hg
    _ = T ^ (-((1 : ℝ) / 4)) * ∑ f, ∑ g ∈ S f, ∏ b, (G b (f b) (g b) *
          (if (f b || g b) = true then w b ^ ((1 : ℝ) / 4) else 1)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro f _
        rw [mul_sum]
    _ ≤ T ^ (-((1 : ℝ) / 4)) *
          ∏ b, ∑ x, ∑ y, G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hT.le _)
        exact sum_choice_prod_le
          (fun b x y => G b x y * (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1)) hG' S

/-- `∏ (1 + x_b) ≤ exp (∑ x_b)` for nonnegative `x`. -/
theorem prod_one_add_le_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ b ∈ s, 0 ≤ x b) :
    ∏ b ∈ s, (1 + x b) ≤ Real.exp (∑ b ∈ s, x b) := by
  rw [Real.exp_sum]
  apply prod_le_prod₀
  · intro b hb
    linarith [hx b hb]
  · intro b _
    have := Real.add_one_le_exp (x b)
    linarith

end Sarkozy.DensityChain
