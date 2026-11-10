module

public import Sarkozy.JointRows.StarMeanTerm
public import Sarkozy.JointRows.StarParity

/-!
# A uniform bound for the complementary means

For the tail range, a coarse count of exact supports suffices. Each proper
nonempty support retains Paley decay, so the total error is `O(κ r β)`.
The estimate holds for either odd prime class and only requires the means
to be small at centres charged by their coordinate laws.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {p : ℕ} [Fact p.Prime]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem bform_swap (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (K : (X → ZMod p) → (Y → ZMod p) → ℝ)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    bform νp νq K f g = bform νq νp (fun y x => K x y) g f := by
  unfold bform
  rw [expect_swap]
  apply FiniteLaw.expect_congr
  intro y
  apply FiniteLaw.expect_congr
  intro x
  ring

theorem rowMean_sum_bound (hp : p ≠ 2)
    (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (𝒮 : Finset (Finset Y)) (A : X → Finset Y → ℝ)
    {κ β : ℝ} (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hA : ∀ i T, |A i T| ≤ 1)
    (hdensX : ∀ i t, (νp i).weight t ≤ κ / p)
    (hdensY : ∀ j t, (νq j).weight t ≤ κ / p)
    (hm : ∀ i j t, (νp i).weight t ≠ 0 → |mchi (νq j) t| ≤ β)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ)
    (hg : (blockLaw νq).expect g = 0) :
    |bform νp νq (fun x y => ∑ i, ∑ T ∈ 𝒮, A i T *
      ((∏ j ∈ T, (mchi (νq j) (x i) + phi (νq j) (x i) (y j))) -
        ∏ j ∈ T, phi (νq j) (x i) (y j))) f g| ≤
      (Fintype.card X : ℝ) * 𝒮.card * 2 ^ Fintype.card Y *
        κ * (Real.sqrt p)⁻¹ * β * nrm (blockLaw νp) f * nrm (blockLaw νq) g := by
  let C := κ * (Real.sqrt p)⁻¹ * β * nrm (blockLaw νp) f * nrm (blockLaw νq) g
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hκ (by positivity)) hβ0)
      (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _)
  simp only [bform_sum]
  calc
    _ ≤ ∑ _i : X, ∑ _T ∈ 𝒮, (2 : ℝ) ^ Fintype.card Y * C := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro i _
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro T _
      have ht := rowMean_term_bound hp νp νq i T (hA i T) hκ hβ0 hβ1
        (hdensX i) (fun j _ => hdensY j) (fun j _ => hm i j) f g hg
      have hpow : (2 : ℝ) ^ T.card ≤ 2 ^ Fintype.card Y :=
        pow_le_pow_right₀ (by norm_num) (card_le_univ T)
      apply ht.trans
      calc
        _ = (2 : ℝ) ^ T.card * C := by dsimp [C]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow hC
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_univ]; dsimp [C]; ring

omit [Fintype X] [DecidableEq X] in
theorem abs_prod_le_one (T : Finset X) (a : X → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |∏ i ∈ T, a i| ≤ 1 := by
  rw [abs_prod]
  simpa only [prod_const_one] using
    (prod_le_prod₀ (s := T) (fun _ _ => abs_nonneg _) (fun i _ => ha i))

omit [Fintype X] [DecidableEq X] in
theorem abs_rowParityCoef_le_one (D : X → X → ℝ) (hD : ∀ i j, |D i j| ≤ 1)
    (i : X) (T : Finset X) : |rowParityCoef (p := p) D i T| ≤ 1 := by
  rw [rowParityCoef, abs_mul, abs_pow]
  have hpow : |PaleyGauss.chiR p (-1)| ^ T.card ≤ 1 :=
    pow_le_one₀ (abs_nonneg _) (abs_chiR_le_one _)
  exact (mul_le_mul hpow (abs_prod_le_one T (D i) (hD i))
    (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [Fintype X] [DecidableEq X] in
theorem abs_coefB_le_one (D : X → X → ℝ) (hD : ∀ i j, |D i j| ≤ 1)
    (j : X) (S : Finset X) : |coefB D j S| ≤ 1 :=
  abs_prod_le_one S (fun i => D i j) (fun i => hD i j)

theorem meanKernelPrime_bound (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p))
    (D : X → X → ℝ) (𝒮 : Finset (Finset X))
    {κ β : ℝ} (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hD : ∀ i j, |D i j| ≤ 1)
    (hdens : ∀ i t, (νp i).weight t ≤ κ / p)
    (hm : ∀ i j t, (νp i).weight t ≠ 0 → |mchi (νp j) t| ≤ β)
    (f g : (X → ZMod p) → ℝ)
    (hf : (blockLaw νp).expect f = 0) (hg : (blockLaw νp).expect g = 0) :
    |bform νp νp (meanKernelPrime νp D 𝒮) f g| ≤
      2 * Fintype.card X * 𝒮.card * 2 ^ Fintype.card X *
        κ * (Real.sqrt p)⁻¹ * β * nrm (blockLaw νp) f * nrm (blockLaw νp) g := by
  unfold meanKernelPrime
  rw [bform_add]
  apply (abs_add_le _ _).trans
  have hr := rowMean_sum_bound hp νp νp 𝒮 (rowParityCoef (p := p) D)
    hκ hβ0 hβ1 (abs_rowParityCoef_le_one D hD) hdens hdens hm f g hg
  have hc := rowMean_sum_bound hp νp νp 𝒮 (coefB D)
    hκ hβ0 hβ1 (abs_coefB_le_one D hD) hdens hdens hm g f hf
  nth_rw 2 [bform_swap]
  exact (add_le_add hr hc).trans_eq (by ring)

end Sarkozy.JointRows.StarOps
