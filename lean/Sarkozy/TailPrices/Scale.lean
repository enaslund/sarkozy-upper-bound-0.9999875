module

public import Sarkozy.TailPrices.Polynomials

@[expose] public section

/-!
# The tail sums at one scale (`lem:tail-prices`(iv))

`paper/sections/27_tail_index.tex`, `lem:tail-prices`(iv). For any finite family of distinct
integers `p_i ≥ P₄` (the tail primes `P₄ ≤ p ≤ N^{1/20}` at a scale) and per-prime bounds
`f_i ≤ K p_i^{-(c+1)}`, the sum is at most `K Φ` with the paper's `Φ = P₄^{-w} + P₄^{1-w}/(w-1)`,
`w = c + 1` (`sum_le_phi`). No prime counting is needed (BMOR is not used): the primes are distinct
integers `≥ P₄`.

* **`sum_le_tail`**: `w = 3/2 - 2a`, `0 ≤ a ≤ 1/1024`: the sum is at most `K/2^{253}`;
* **`sum_le_tail_weighted`**: `w = 5/4 - 2a` (the sum `∑ η_p p^{1/4}` of (iv)): at most
  `K/2^{124}`;
* `rpow_quarter`: `p^{-(3/2-2a)} p^{1/4} = p^{-(5/4-2a)}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

theorem two_le_P4 : 2 ≤ PartV.P4 := by
  unfold PartV.P4
  exact le_self_pow₀ (by norm_num) (by norm_num)

/-- **A sum over distinct integers `≥ P₄`** of terms `f_i ≤ K p_i^{-(c+1)}`, `0 < c ≤ 1`,
`K ≥ 0`, is at most `K (P₄^{-(c+1)} + P₄^{-c}/c)` (`lem:tail-prices`(iv)). -/
theorem sum_le_phi {ι : Type} (s : Finset ι) (pr : ι → ℕ) (hinj : Set.InjOn pr s)
    (h4 : ∀ i ∈ s, PartV.P4 ≤ pr i) {c K : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hK : 0 ≤ K)
    (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≤ K * (pr i : ℝ) ^ (-(c + 1))) :
    ∑ i ∈ s, f i ≤ K * ((PartV.P4 : ℝ) ^ (-(c + 1)) + (PartV.P4 : ℝ) ^ (-c) / c) := by
  have hs : ∀ n ∈ s.image pr, PartV.P4 ≤ n := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hn
    exact h4 i hi
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, K * (pr i : ℝ) ^ (-(c + 1)) := sum_le_sum hf
    _ = K * ∑ n ∈ s.image pr, (n : ℝ) ^ (-(c + 1)) := by rw [sum_image hinj, mul_sum]
    _ ≤ K * ((PartV.P4 : ℝ) ^ (-(c + 1)) + (PartV.P4 : ℝ) ^ (-c) / c) :=
      mul_le_mul_of_nonneg_left (sum_rpow_le_of_ge hc0 hc1 two_le_P4 _ hs) hK

/-- **`lem:tail-prices`(iv), one scale**: if `f_i ≤ K p_i^{-(3/2-2a)}` at distinct integers
`p_i ≥ P₄`, with `0 ≤ a ≤ 1/1024` and `K ≥ 0`, then `∑ f_i ≤ K/2^{253}`. -/
theorem sum_le_tail {ι : Type} (s : Finset ι) (pr : ι → ℕ) (hinj : Set.InjOn pr s)
    (h4 : ∀ i ∈ s, PartV.P4 ≤ pr i) {a K : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 1024) (hK : 0 ≤ K)
    (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≤ K * (pr i : ℝ) ^ (-((1 / 2 - 2 * a) + 1))) :
    ∑ i ∈ s, f i ≤ K / 2 ^ 253 := by
  have h := sum_le_phi s pr hinj h4 (by linarith) (by linarith) hK f hf
  have h' := mul_le_mul_of_nonneg_left (phi_P4_le ha) hK
  rw [mul_one_div] at h'
  exact h.trans h'

/-- **`lem:tail-prices`(iv), the `p^{1/4}`-weighted sum at one scale**: if
`f_i ≤ K p_i^{-(5/4-2a)}` at distinct integers `p_i ≥ P₄`, with `0 ≤ a ≤ 1/1024` and `K ≥ 0`,
then `∑ f_i ≤ K/2^{124}`. -/
theorem sum_le_tail_weighted {ι : Type} (s : Finset ι) (pr : ι → ℕ) (hinj : Set.InjOn pr s)
    (h4 : ∀ i ∈ s, PartV.P4 ≤ pr i) {a K : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 1024) (hK : 0 ≤ K)
    (f : ι → ℝ) (hf : ∀ i ∈ s, f i ≤ K * (pr i : ℝ) ^ (-((1 / 4 - 2 * a) + 1))) :
    ∑ i ∈ s, f i ≤ K / 2 ^ 124 := by
  have h := sum_le_phi s pr hinj h4 (by linarith) (by linarith) hK f hf
  have h' := mul_le_mul_of_nonneg_left (phi_P4_le' ha) hK
  rw [mul_one_div] at h'
  exact h.trans h'

/-- `p^{-(3/2-2a)} p^{1/4} = p^{-(5/4-2a)}`. -/
theorem rpow_quarter {q : ℕ} (hq : 0 < q) (a : ℝ) :
    (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) * (q : ℝ) ^ (1 / 4 : ℝ) =
      (q : ℝ) ^ (-((1 / 4 - 2 * a) + 1)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← Real.rpow_add hq0]
  congr 1
  ring

end Sarkozy.TailPrices
