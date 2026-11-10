module

public import Sarkozy.CancellationSteps.Paper
public import Mathlib.NumberTheory.Bertrand

/-!
# A premise of `DensityCancellation` at the paper's data: the square class `r = 1`

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, and
`def:nonvanishing-square-class`.

WP-FI's `TheoremC.DensityCancellation` quantifies over the nonvanishing square classes `r`
modulo `M₀`. If there were none, the statement would be vacuous.
* `isNonvanishingSquareClass_one`: `r = 1` is a nonvanishing square class modulo every
  `D ≠ 0` with `v₂(D) ≥ 3`.
* `paperModulus_factorization_two`: `v₂(M₀) = 2m_ext + 1 = 129` for the paper's `M₀`
  (`Paper.lean`), so `three_le_paperModulus_factorization_two` holds.

Non-vacuity of the data: `five_mem_paperFixedPrimes` (the fixed coordinates are nonempty) and
`exists_tail_prime_ge_P5` (some scale has a tail prime `≥ P₅`, by Bertrand's postulate), so the
mixing premise at the tail primes `≥ P₅` is exercised.

Instantiating the first lemma at the paper's `M₀` is not done here. Elaborating the numeral
`1 : ZMod M₀` for the concrete `M₀` makes the elaborator unfold the product over the primes below
`Q₃`, and it reaches the maximum recursion depth.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset

/-- **`r = 1` is a nonvanishing square class** (`def:nonvanishing-square-class`) modulo every
`D ≠ 0` with `v₂(D) ≥ 3`: at each `p ∣ D` its reduction is `1`, of valuation `0`, with unit part
`1` (a nonzero square, and `≡ 1 (mod 8)` at `2`). -/
theorem isNonvanishingSquareClass_one (D : ℕ) (hD : D ≠ 0) (h2 : 3 ≤ D.factorization 2) :
    Functional.IsNonvanishingSquareClass D 1 := by
  have h1D : 1 < D := by
    by_contra hlt
    have h01 : D = 0 ∨ D = 1 := by omega
    rcases h01 with h | h
    · exact hD h
    · rw [h, Nat.factorization_one] at h2
      simp only [Finsupp.coe_zero, Pi.zero_apply] at h2
      omega
  have : Fact (1 < D) := ⟨h1D⟩
  refine ⟨h2, fun p hp => ?_⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hk : D.factorization p ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd hpp hD (Nat.dvd_of_mem_primeFactors hp)).ne'
  have hrep : Functional.coordinateRep D p 1 = 1 := by
    unfold Functional.coordinateRep
    rw [ZMod.val_one]
    exact Nat.mod_eq_of_lt (Nat.one_lt_pow hk hpp.one_lt)
  rw [hrep, padicValNat_one_right]
  refine ⟨one_ne_zero, ⟨0, rfl⟩, ?_⟩
  split_ifs with hp2
  · subst hp2
    rw [hrep, padicValNat_one_right]
    exact ⟨by omega, by norm_num⟩
  · have : Fact (1 < p) := ⟨hpp.one_lt⟩
    refine ⟨?_, ?_⟩
    · simp only [pow_zero, Nat.div_one, Nat.cast_one]
      exact IsSquare.one
    · simp only [pow_zero, Nat.div_one, Nat.cast_one]
      exact one_ne_zero

/-- The paper's `M₀` is nonzero. -/
theorem paperModulus_ne_zero : IndexSupport.modulus paperPr paperH ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ _ => NeZero.ne _

/-- **`v₂(M₀) = 2m_ext + 1`** for the paper's `M₀` (`def:record:parameters`(c)). -/
theorem paperModulus_factorization_two :
    (IndexSupport.modulus paperPr paperH).factorization 2 = 2 * PartV.mExt + 1 := by
  have h := TheoremC.modulus_factorization paperPr paperH paperPr_prime Subtype.val_injective
    (⟨2, mem_insert_self _ _⟩ : PaperP)
  have h2 : paperH (⟨2, mem_insert_self _ _⟩ : PaperP) = 2 * PartV.mExt + 1 := by
    unfold paperH
    simp only [↓reduceIte]
  exact h.trans h2

/-- `v₂(M₀) ≥ 3`, the condition of `def:nonvanishing-square-class` on `M₀`; with
`isNonvanishingSquareClass_one`, `r = 1` is a nonvanishing square class modulo `M₀`. -/
theorem three_le_paperModulus_factorization_two :
    3 ≤ (IndexSupport.modulus paperPr paperH).factorization 2 := by
  rw [paperModulus_factorization_two]
  unfold PartV.mExt
  norm_num

/-! ## Non-vacuity of the data -/

/-- `P₄ ≤ P₅`. -/
theorem P4_le_P5 : PartV.P4 ≤ PartV.P5 := by
  decide +kernel

/-- `5 ∈ 𝒫₁`: the fixed coordinates are nonempty. -/
theorem five_mem_paperFixedPrimes : 5 ∈ paperFixedPrimes :=
  mem_paperFixedPrimes.mpr (Or.inl ⟨Nat.prime_five, rfl, by decide +kernel⟩)

/-- **Large tail primes occur**: for every `n ≥ P₄`, at the scale `L = (2n)^{20}` the tail
`𝒯_N` contains a prime `q > n` (Bertrand's postulate, `N^β ≥ 2n`). -/
theorem exists_tail_prime_ge (n : ℕ) (hn : PartV.P4 ≤ n) :
    ∃ L : ℕ, ∃ q ∈ paperTailPrimes L, n ≤ q := by
  have hP : PartV.P3 < PartV.P4 := PartV.P3_lt_P4
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  refine ⟨(2 * n) ^ 20, q, mem_paperTailPrimes.mpr ⟨hq, hn.trans hlt.le, ?_⟩, hlt.le⟩
  have hK : 0 < blockScale := by
    unfold blockScale
    norm_num
  have hx : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hroot : (((2 * n : ℕ) : ℝ) ^ 20) ^ (1 / 20 : ℝ) = ((2 * n : ℕ) : ℝ) := by
    rw [one_div]
    exact_mod_cast Real.pow_rpow_inv_natCast hx (by norm_num : (20 : ℕ) ≠ 0)
  unfold Functional.paperCutoff Functional.liftExponent
  calc (q : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hle
    _ = (((2 * n : ℕ) : ℝ) ^ 20) ^ (1 / 20 : ℝ) := hroot.symm
    _ ≤ ((blockScale * (2 * n) ^ 20 : ℕ) : ℝ) ^ (1 / 20 : ℝ) := by
      apply Real.rpow_le_rpow (pow_nonneg hx 20) _ (by norm_num)
      exact_mod_cast Nat.le_mul_of_pos_left ((2 * n) ^ 20) hK

/-- **The tail primes `≥ P₅` occur**, so the mixing premise of `DensityCancellation` is not
vacuous for the paper's data. -/
theorem exists_tail_prime_ge_P5 : ∃ L : ℕ, ∃ q ∈ paperTailPrimes L, PartV.P5 ≤ q :=
  exists_tail_prime_ge PartV.P5 P4_le_P5

end Sarkozy.CancellationSteps
