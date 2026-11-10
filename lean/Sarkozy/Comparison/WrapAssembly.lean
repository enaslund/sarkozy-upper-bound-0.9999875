module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The summation step of the expansion-and-wrap lemma

`lem:record:wrap-expansion` (`paper/sections/10_comparison_lemmas.tex`). The signed index
form expands as `J_ν - 2^k Y_ν = ∑_{𝒮≠∅} (-1)^|𝒮| 2^(k-|𝒮|) I_{ν,𝒮}`
(`eq:record:expansion`; proved for the actual inputs in `Sarkozy.Functional` and for the
operators in `Sarkozy.IndexSupport`), and each coupled form splits as
`I_{ν,𝒮} = ∑_{𝒲 ⊆ 𝒮} I_{ν,𝒮,𝒲}` by the set `𝒲` of wrapping active queries. The
non-wrapping terms (`𝒲 ≠ 𝒮`) are cancellation remainders (`lem:record:density-can`),
and each wrapping term is bounded by `(B e^(S+A) x^|𝒮| + o(1)) Y` with
`x = R_I K^(2θ/d - 1)` (index-support lemma (b) and `lem:envelope-energy`). This module
proves the summation: `∑_{j≥1} C(k,j) 2^(k-j) B' x^j = B'[(2 + x)^k - 2^k] = 2^k W`, with the
error terms collected explicitly.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Comparison

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- `∑_{𝒮} 2^(k-|𝒮|) x^|𝒮| = (2 + x)^k`. -/
theorem sum_powerset_two_pow (x : ℝ) :
    ∑ S ∈ (univ : Finset E).powerset, (2 : ℝ) ^ (Fintype.card E - S.card) * x ^ S.card =
      (2 + x) ^ Fintype.card E := by
  have h := Finset.prod_add (fun _ : E => x) (fun _ : E => (2 : ℝ)) (univ : Finset E)
  simp only [prod_const] at h
  rw [← card_univ, add_comm, h]
  refine sum_congr rfl fun S hS => ?_
  rw [card_sdiff_of_subset (mem_powerset.mp hS), mul_comm]

/-- **The wrap summation.** Suppose `J - 2^k Yν = ∑_{𝒮≠∅} (-1)^|𝒮| 2^(k-|𝒮|) ∑_{𝒲⊆𝒮} I 𝒮 𝒲`,
every non-wrapping term has `|I 𝒮 𝒲| ≤ r`, and every wrapping term has
`|I 𝒮 𝒮| ≤ (B' x^|𝒮| + ε) Y + r'`, with `Y, ε, r, r' ≥ 0`. Then
`|J - 2^k Yν| ≤ B' [(2 + x)^k - 2^k] Y + 3^k ε Y + 4^k r + 3^k r'`. -/
theorem wrap_summation {J Yν Y B' x ε r r' : ℝ} (I : Finset E → Finset E → ℝ)
    (hY : 0 ≤ Y) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hexp : J - 2 ^ Fintype.card E * Yν =
      ∑ S ∈ (univ : Finset E).powerset.filter (fun S => S ≠ ∅),
        (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) * ∑ W ∈ S.powerset, I S W)
    (hnon : ∀ S W, W ⊆ S → W ≠ S → |I S W| ≤ r)
    (hwrap : ∀ S, S ≠ ∅ → |I S S| ≤ (B' * x ^ S.card + ε) * Y + r') :
    |J - 2 ^ Fintype.card E * Yν| ≤
      B' * ((2 + x) ^ Fintype.card E - 2 ^ Fintype.card E) * Y +
        3 ^ Fintype.card E * ε * Y + 4 ^ Fintype.card E * r + 3 ^ Fintype.card E * r' := by
  set k := Fintype.card E
  set T := (univ : Finset E).powerset.filter (fun S => S ≠ ∅)
  -- Bound on each coupled form.
  have hcoupled : ∀ S ∈ T, |∑ W ∈ S.powerset, I S W| ≤
      (2 : ℝ) ^ S.card * r + ((B' * x ^ S.card + ε) * Y + r') := by
    intro S hS
    have hSne : S ≠ ∅ := (mem_filter.mp hS).2
    rw [← sum_erase_add _ _ (mem_powerset_self S)]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hwrap S hSne))
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ W ∈ S.powerset.erase S, |I S W| ≤ r := by
      intro W hW
      obtain ⟨hWS, hW'⟩ := mem_erase.mp hW
      exact hnon S W (mem_powerset.mp hW') hWS
    refine (sum_le_sum hle).trans ?_
    rw [sum_const, card_erase_of_mem (mem_powerset_self S), card_powerset, nsmul_eq_mul]
    have h2 : ((2 ^ S.card - 1 : ℕ) : ℝ) ≤ 2 ^ S.card := by
      have : (1 : ℕ) ≤ 2 ^ S.card := Nat.one_le_two_pow
      push_cast [this]
      linarith
    exact mul_le_mul_of_nonneg_right h2 hr
  rw [hexp]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ S ∈ T, |(-1 : ℝ) ^ S.card * 2 ^ (k - S.card) * ∑ W ∈ S.powerset, I S W| ≤
      2 ^ (k - S.card) * ((2 : ℝ) ^ S.card * r + ((B' * x ^ S.card + ε) * Y + r')) := by
    intro S hS
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ (k - S.card))]
    exact mul_le_mul_of_nonneg_left (hcoupled S hS) (by positivity)
  refine (sum_le_sum hterm).trans ?_
  -- Extend the sum over nonempty sets to all sets, and evaluate the three binomial sums.
  have hnn : ∀ S ∈ (univ : Finset E).powerset, 0 ≤
      (2 : ℝ) ^ (k - S.card) * ((2 : ℝ) ^ S.card * r + ε * Y + r') := by
    intro S _
    positivity
  have hsplit : ∑ S ∈ T, (2 : ℝ) ^ (k - S.card) * ((2 : ℝ) ^ S.card * r +
        ((B' * x ^ S.card + ε) * Y + r')) =
      (∑ S ∈ T, B' * Y * ((2 : ℝ) ^ (k - S.card) * x ^ S.card)) +
        ∑ S ∈ T, (2 : ℝ) ^ (k - S.card) * ((2 : ℝ) ^ S.card * r + ε * Y + r') := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun S _ => ?_
    ring
  rw [hsplit]
  have hT : T = (univ : Finset E).powerset.erase ∅ := by
    ext S
    simp [T, and_comm]
  have hfirst : ∑ S ∈ T, B' * Y * ((2 : ℝ) ^ (k - S.card) * x ^ S.card) =
      B' * Y * ((2 + x) ^ k - 2 ^ k) := by
    rw [← mul_sum, hT, sum_erase_eq_sub (empty_mem_powerset _), sum_powerset_two_pow]
    simp [k]
  have hsecond : ∑ S ∈ T, (2 : ℝ) ^ (k - S.card) * ((2 : ℝ) ^ S.card * r + ε * Y + r') ≤
      ∑ S ∈ (univ : Finset E).powerset,
        (2 : ℝ) ^ (k - S.card) * ((2 : ℝ) ^ S.card * r + ε * Y + r') :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun S hS _ => hnn S hS)
  have hfull : ∑ S ∈ (univ : Finset E).powerset,
        (2 : ℝ) ^ (k - S.card) * ((2 : ℝ) ^ S.card * r + ε * Y + r') =
      4 ^ k * r + 3 ^ k * (ε * Y + r') := by
    have h4 : ∑ S ∈ (univ : Finset E).powerset, (2 : ℝ) ^ (k - S.card) * 2 ^ S.card =
        4 ^ k := by
      rw [sum_powerset_two_pow]
      norm_num [k]
    have h3 : ∑ S ∈ (univ : Finset E).powerset, (2 : ℝ) ^ (k - S.card) * 1 ^ S.card =
        3 ^ k := by
      rw [sum_powerset_two_pow]
      norm_num [k]
    simp only [one_pow, mul_one] at h3
    calc ∑ S ∈ (univ : Finset E).powerset,
          (2 : ℝ) ^ (k - S.card) * ((2 : ℝ) ^ S.card * r + ε * Y + r')
        = (∑ S ∈ (univ : Finset E).powerset, (2 : ℝ) ^ (k - S.card) * 2 ^ S.card) * r +
          (∑ S ∈ (univ : Finset E).powerset, (2 : ℝ) ^ (k - S.card)) * (ε * Y + r') := by
          rw [sum_mul, sum_mul, ← sum_add_distrib]
          refine sum_congr rfl fun S _ => ?_
          ring
      _ = 4 ^ k * r + 3 ^ k * (ε * Y + r') := by rw [h4, h3]
  rw [hfirst]
  nlinarith [hsecond, hfull]

end Sarkozy.Comparison
