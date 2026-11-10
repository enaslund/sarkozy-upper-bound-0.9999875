module

public import Sarkozy.Peyre.Weights
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Peyre's tensorization in finite form, IX: the Neumann series of `lem:peyre:weights`

`lem:peyre:weights` exactly as stated in the paper: for a nonnegative matrix `K` and
`λ > ‖K‖`, the series `α = ∑_{m ≥ 0} λ^{-m-1} K^m 1` converges (in `ℝ^ι`, equivalently
entrywise), `α_i ≥ λ^{-1} > 0`, and `K α ≤ λ α` entrywise; in fact `K α = λ α - 1`.
The hypothesis `λ > ‖K‖` is expressed as `‖K x‖₂ ≤ κ ‖x‖₂` for all `x` with `κ < λ`.
(The proof of the theorem uses the truncated version `exists_weights` instead.)
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

/-- `lem:peyre:weights`, series form. -/
theorem neumann_weights {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    {κ lam : ℝ} (hκ : 0 ≤ κ) (hκlam : κ < lam)
    (hnorm : ∀ x : ι → ℝ, ∑ i, (∑ j, K i j * x j) ^ 2 ≤ κ ^ 2 * ∑ i, x i ^ 2) :
    Summable (fun m : ℕ => fun i => lam⁻¹ ^ (m + 1) * neumannIter K m i) ∧
      0 < lam⁻¹ ∧
      (∀ i, lam⁻¹ ≤ ∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m i) ∧
      (∀ i, ∑ j, K i j * (∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m j) =
        lam * (∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m i) - 1) ∧
      ∀ i, ∑ j, K i j * (∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m j) ≤
        lam * ∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m i := by
  have hlam : 0 < lam := lt_of_le_of_lt hκ hκlam
  have hli : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam.le
  set q := κ / lam with hq
  have hq0 : 0 ≤ q := div_nonneg hκ hlam.le
  have hq1 : q < 1 := (div_lt_one hlam).mpr hκlam
  set s := √(Fintype.card ι : ℝ) with hs
  set t : ℕ → ι → ℝ := fun m i => lam⁻¹ ^ (m + 1) * neumannIter K m i with ht
  have ht0 : ∀ m i, 0 ≤ t m i :=
    fun m i => mul_nonneg (pow_nonneg hli _) (neumannIter_nonneg K hK m i)
  have hsum : ∀ i, Summable (fun m : ℕ => t m i) := by
    intro i
    refine Summable.of_nonneg_of_le (fun m => ht0 m i) (fun m => ?_)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left (lam⁻¹ * s))
    have h1 := neumannIter_le K hκ hnorm m i
    calc t m i ≤ lam⁻¹ ^ (m + 1) * (κ ^ m * s) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg hli _)
      _ = lam⁻¹ * s * q ^ m := by
          rw [hq, div_pow, pow_succ, div_eq_mul_inv, inv_pow]
          ring
  have hKt : ∀ m i, ∑ j, K i j * t m j = lam * t (m + 1) i := by
    intro m i
    have hv : neumannIter K (m + 1) i = ∑ j, K i j * neumannIter K m j := rfl
    have hpow : lam * lam⁻¹ ^ (m + 1 + 1) = lam⁻¹ ^ (m + 1) := by
      rw [pow_succ]
      field_simp
    simp only [ht]
    rw [hv, ← mul_assoc, hpow, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hKα : ∀ i, ∑ j, K i j * (∑' m : ℕ, t m j) = lam * (∑' m : ℕ, t m i) - 1 := by
    intro i
    have e1 : ∑ j, K i j * (∑' m : ℕ, t m j) = ∑' m : ℕ, ∑ j, K i j * t m j := by
      rw [Summable.tsum_finsetSum (fun j _ => (hsum j).mul_left (K i j))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [tsum_mul_left]
    rw [e1]
    simp_rw [hKt]
    rw [tsum_mul_left, (hsum i).tsum_eq_zero_add]
    have h0 : t 0 i = lam⁻¹ := by simp [ht, neumannIter]
    rw [h0, mul_add, mul_inv_cancel₀ hlam.ne']
    ring
  refine ⟨Pi.summable.mpr hsum, inv_pos.mpr hlam, fun i => ?_, hKα, fun i => ?_⟩
  · have h := (hsum i).le_tsum 0 (fun m _ => ht0 m i)
    have h0 : t 0 i = lam⁻¹ := by simp [ht, neumannIter]
    rw [h0] at h
    exact h
  · rw [hKα i]
    linarith

open scoped Matrix.Norms.L2Operator in
/-- `lem:peyre:weights`, series form, with `λ > ‖K‖` for mathlib's `ℓ²` operator norm. -/
theorem neumann_weights_l2 {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ)
    (hK : ∀ i j, 0 ≤ K i j) {lam : ℝ} (hlam : ‖K‖ < lam) :
    Summable (fun m : ℕ => fun i => lam⁻¹ ^ (m + 1) * neumannIter K m i) ∧
      0 < lam⁻¹ ∧
      (∀ i, lam⁻¹ ≤ ∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m i) ∧
      (∀ i, ∑ j, K i j * (∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m j) =
        lam * (∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m i) - 1) ∧
      ∀ i, ∑ j, K i j * (∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m j) ≤
        lam * ∑' m : ℕ, lam⁻¹ ^ (m + 1) * neumannIter K m i :=
  neumann_weights K hK (norm_nonneg K) hlam (fun x => opBound_of_l2 K x)

end Sarkozy.Peyre
