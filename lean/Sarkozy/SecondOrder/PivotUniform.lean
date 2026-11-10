module

public import Sarkozy.SecondOrder.PivotSums

/-!
# Coarse bounds for the six pivot sums

The tail argument only needs a uniform finite bound before multiplication by
p^(-1/2). There are at most 2^36 possible supports, every star coefficient
has magnitude at most 36, and every support has at most 36 vertices.
-/

@[expose] public section

namespace Sarkozy.SecondOrder

open Finset Sarkozy.Target

variable {ι : Type*} [Fintype ι]

theorem sum_le_pivot_budget (hn : Fintype.card ι ≤ 2 ^ 36) (f : ι → ℝ)
    (hf : ∀ i, f i ≤ 2 ^ 16) : ∑ i, f i ≤ 2 ^ 60 := by
  calc ∑ i, f i ≤ ∑ _i : ι, (2 : ℝ) ^ 16 := sum_le_sum fun i _ => hf i
    _ = (Fintype.card ι : ℝ) * 2 ^ 16 := by rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ 36 * 2 ^ 16 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
    _ ≤ 2 ^ 60 := by norm_num

structure PivotBudgets (b : ι → ℝ) (s : ι → ℕ) : Prop where
  A : pivA b ≤ 2 ^ 60
  L : pivL b ≤ 2 ^ 60
  U : pivU b s ≤ 2 ^ 60
  V : pivV b s ≤ 2 ^ 60
  W : pivW b s ≤ 2 ^ 60
  X : pivX b s ≤ 2 ^ 60

theorem pivotBudgets_of_card (hn : Fintype.card ι ≤ 2 ^ 36) (b : ι → ℝ) (s : ι → ℕ)
    (hb : ∀ i, |b i| ≤ 36) (hs0 : ∀ i, 1 ≤ s i) (hs : ∀ i, s i ≤ 36) :
    PivotBudgets b s := by
  have hsR : ∀ i, (s i : ℝ) ≤ 36 := fun i => by exact_mod_cast hs i
  have hg : ∀ i, (gam (s i) : ℝ) ≤ 36 := by
    intro i
    have : gam (s i) ≤ 36 := by unfold gam; have := hs i; omega
    exact_mod_cast this
  have hsR0 : ∀ i, 0 ≤ (s i : ℝ) - 1 := fun i => by
    have : (1 : ℝ) ≤ s i := by exact_mod_cast hs0 i
    linarith
  constructor
  · apply sum_le_pivot_budget hn
    intro i
    have hi := (abs_le.mp (hb i))
    nlinarith [sq_nonneg (b i + 36), sq_nonneg (b i - 36)]
  · apply sum_le_pivot_budget hn
    intro i
    exact (hb i).trans (by norm_num)
  · apply sum_le_pivot_budget hn
    intro i
    have h := mul_le_mul (hb i) (hg i) (Nat.cast_nonneg _) (by norm_num)
    exact h.trans (by norm_num)
  · apply sum_le_pivot_budget hn
    intro i
    have h1 : |b i| * ((s i : ℝ) - 1) ≤ 36 * 36 :=
      mul_le_mul (hb i) (by linarith [hsR i]) (hsR0 i) (by norm_num)
    have h2 := mul_le_mul h1 (hg i) (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 36 * 36)
    exact h2.trans (by norm_num)
  · apply sum_le_pivot_budget hn
    intro i
    have h := mul_le_mul (hb i) (hsR i) (Nat.cast_nonneg _) (by norm_num)
    exact h.trans (by norm_num)
  · apply sum_le_pivot_budget hn
    intro i
    have h := mul_le_mul (hb i) (pow_le_pow_left₀ (Nat.cast_nonneg _) (hsR i) 2)
      (sq_nonneg _) (by norm_num)
    exact h.trans (by norm_num)

theorem pivE_uniform (b : ι → ℝ) (s : ι → ℕ) (hs : ∀ i, 1 ≤ s i)
    (hb : PivotBudgets b s) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {d : ℕ} (hd : d ≤ 10) : pivE r d b s ≤ 2 ^ 140 := by
  have hdR : (d : ℝ) ≤ 10 := by exact_mod_cast hd
  have hU := pivU_nonneg b s
  have hV := pivV_nonneg b hs
  have hL := pivL_nonneg b
  have hW := pivW_nonneg b s
  have hX := pivX_nonneg b s
  unfold pivE
  calc _ ≤ (2 : ℝ) ^ 10 *
      (2 * 2 ^ 60 * 2 ^ 60 + (10 / 2 + 1) * (2 ^ 60) ^ 2 + (2 ^ 60) ^ 2 +
        1 * (2 * 2 ^ 60 * 2 ^ 60 + 10 / 2 * (2 ^ 60) ^ 2)) := by
        gcongr <;> first
        | assumption
        | exact hb.U
        | exact hb.V
        | exact hb.L
        | exact hb.W
        | exact hb.X
        | norm_num
    _ ≤ 2 ^ 140 := by norm_num

theorem pivD2_uniform (b : ι → ℝ) (s : ι → ℕ) (hs : ∀ i, 1 ≤ s i)
    (hb : PivotBudgets b s) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {d : ℕ} (hd : d ≤ 10) {e : ℝ} (he : e ≤ 1 / 2) :
    pivD2 r d e b s ≤ 2 ^ 142 := by
  have hE := pivE_uniform b s hs hb hr hr1 hd
  have hE0 := pivE_nonneg hr d b hs
  have hden : 0 < 1 - e := by linarith
  unfold pivD2
  apply (div_le_iff₀ hden).mpr
  have hm : r * pivE r d b s ≤ (2 : ℝ) ^ 140 := by
    exact (mul_le_mul hr1 hE hE0 zero_le_one).trans_eq (one_mul _)
  have hA := hb.A
  norm_num at hA hm ⊢
  nlinarith

theorem pivK_uniform (b : ι → ℝ) (s : ι → ℕ) (hs : ∀ i, 1 ≤ s i)
    (hb : PivotBudgets b s) {r : ℝ} (hr1 : r ≤ 1)
    {d n : ℕ} (hd : d ≤ 10) (hn0 : 1 ≤ n) (hn : n ≤ 36) {e : ℝ} (he : e ≤ 1 / 2) :
    pivK r d n e b s ≤ 2 ^ 80 := by
  have hdR : (d : ℝ) ≤ 10 := by exact_mod_cast hd
  have hnR : (n : ℝ) ≤ 36 := by exact_mod_cast hn
  have hU := pivU_nonneg b s
  have hV := pivV_nonneg b hs
  have hW := pivW_nonneg b s
  have hX := pivX_nonneg b s
  have hnR0 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hbr0 : 0 ≤ pivX b s + ((d : ℝ) / 2 + n - 1) * pivW b s :=
    add_nonneg hX (mul_nonneg (by linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]) hW)
  have hden : 0 < 1 - e := by linarith
  have hfac : (2 : ℝ) ^ d / (1 - e) ≤ 2 ^ 11 := by
    apply (div_le_iff₀ hden).mpr
    have hpow : (2 : ℝ) ^ d ≤ 2 ^ 10 := pow_le_pow_right₀ (by norm_num) hd
    norm_num at hpow ⊢
    nlinarith
  have hbr : pivV b s + (d : ℝ) / 2 * pivU b s +
      r * (pivX b s + ((d : ℝ) / 2 + n - 1) * pivW b s) ≤ (2 : ℝ) ^ 68 := by
    calc pivV b s + (d : ℝ) / 2 * pivU b s +
        r * (pivX b s + ((d : ℝ) / 2 + n - 1) * pivW b s)
        ≤ 2 ^ 60 + 10 / 2 * 2 ^ 60 +
        1 * (2 ^ 60 + (10 / 2 + 36) * 2 ^ 60) := by
          gcongr <;> first
          | assumption
          | exact hb.V
          | exact hb.U
          | exact hb.X
          | exact hb.W
          | linarith
      _ ≤ 2 ^ 68 := by norm_num
  unfold pivK
  calc _ ≤ ((2 : ℝ) ^ d / (1 - e)) * 2 ^ 68 :=
        mul_le_mul_of_nonneg_left hbr (div_nonneg (by positivity) hden.le)
    _ ≤ (2 : ℝ) ^ 11 * 2 ^ 68 := mul_le_mul_of_nonneg_right hfac (by positivity)
    _ ≤ 2 ^ 80 := by norm_num

end Sarkozy.SecondOrder
