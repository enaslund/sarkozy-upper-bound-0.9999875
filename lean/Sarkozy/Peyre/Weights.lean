module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Peyre's tensorization in finite form, IV: positive weights and the potential

* `exists_weights`: `lem:peyre:weights` (positive weights from a Neumann series), in
  existence form.  The paper sums the full series `∑_{m ≥ 0} λ^{-m-1} K^m 1`; here the
  witness is a *truncated* Neumann series `∑_{m < n} λ^{-m-1} K^m 1`, with `n` chosen so
  that `λ^{-n} K^n 1 ≤ 1` entrywise.  It has the two properties that the proof of
  `thm:peyre-finite` uses: `α_i ≥ λ^{-1}` and `K α ≤ λ α` entrywise.  The operator-norm
  hypothesis `λ > ‖K‖` is expressed as: `‖K x‖₂ ≤ κ ‖x‖₂` for all `x`, with `κ < λ`.
* `potential`: `lem:peyre:potential` (a monotone potential for nonnegative losses).

Matrices are plain functions `ι → ι → ℝ`, and `K x` is `fun i => ∑ j, K i j * x j`.
`opBound_of_l2` connects the bound `‖K x‖₂ ≤ κ ‖x‖₂` to mathlib's `ℓ²` operator norm
(`Matrix.Norms.L2Operator`), and `exists_weights_l2` states the lemma with `λ > ‖K‖`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

/-- Iterates `K^m 1` of a matrix applied to the all-ones vector. -/
def neumannIter {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => 1
  | m + 1 => fun i => ∑ j, K i j * neumannIter K m j

theorem neumannIter_nonneg {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) :
    ∀ m i, 0 ≤ neumannIter K m i := by
  intro m
  induction m with
  | zero => intro i; simp [neumannIter]
  | succ m ih =>
    intro i
    simp only [neumannIter]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hK i j) (ih j))

theorem neumannIter_sq_sum_le {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) {κ : ℝ}
    (hnorm : ∀ x : ι → ℝ, ∑ i, (∑ j, K i j * x j) ^ 2 ≤ κ ^ 2 * ∑ i, x i ^ 2) :
    ∀ m, ∑ i, neumannIter K m i ^ 2 ≤ (κ ^ 2) ^ m * (Fintype.card ι : ℝ) := by
  intro m
  induction m with
  | zero => simp [neumannIter]
  | succ m ih =>
    calc ∑ i, neumannIter K (m + 1) i ^ 2 = ∑ i, (∑ j, K i j * neumannIter K m j) ^ 2 := rfl
      _ ≤ κ ^ 2 * ∑ i, neumannIter K m i ^ 2 := hnorm _
      _ ≤ κ ^ 2 * ((κ ^ 2) ^ m * (Fintype.card ι : ℝ)) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg κ)
      _ = _ := by ring

theorem neumannIter_le {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hnorm : ∀ x : ι → ℝ, ∑ i, (∑ j, K i j * x j) ^ 2 ≤ κ ^ 2 * ∑ i, x i ^ 2) (m : ℕ)
    (i : ι) : neumannIter K m i ≤ κ ^ m * √(Fintype.card ι : ℝ) := by
  have h1 : neumannIter K m i ^ 2 ≤ (κ ^ 2) ^ m * (Fintype.card ι : ℝ) := by
    refine le_trans ?_ (neumannIter_sq_sum_le K hnorm m)
    exact Finset.single_le_sum (f := fun j => neumannIter K m j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : (κ ^ 2) ^ m * (Fintype.card ι : ℝ) = (κ ^ m * √(Fintype.card ι : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← pow_mul, ← pow_mul, mul_comm 2 m]
  rw [h2] at h1
  have h3 : 0 ≤ κ ^ m * √(Fintype.card ι : ℝ) :=
    mul_nonneg (pow_nonneg hκ m) (Real.sqrt_nonneg _)
  exact (abs_le_of_sq_le_sq' h1 h3).2

/-- `lem:peyre:weights` (existence form, truncated Neumann series): if `K ≥ 0` entrywise and
`‖K x‖₂ ≤ κ ‖x‖₂` for all `x` with `0 ≤ κ < λ`, then some `α` has `α_i ≥ λ⁻¹ > 0` and
`K α ≤ λ α` entrywise. -/
theorem exists_weights {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) (hK : ∀ i j, 0 ≤ K i j)
    {κ lam : ℝ} (hκ : 0 ≤ κ) (hκlam : κ < lam)
    (hnorm : ∀ x : ι → ℝ, ∑ i, (∑ j, K i j * x j) ^ 2 ≤ κ ^ 2 * ∑ i, x i ^ 2) :
    ∃ a : ι → ℝ, (∀ i, lam⁻¹ ≤ a i) ∧ ∀ i, ∑ j, K i j * a j ≤ lam * a i := by
  have hlam : 0 < lam := lt_of_le_of_lt hκ hκlam
  set q := κ / lam with hq
  have hq0 : 0 ≤ q := div_nonneg hκ hlam.le
  have hq1 : q < 1 := (div_lt_one hlam).mpr hκlam
  set s := √(Fintype.card ι : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (s + 1) by positivity) hq1
  set n := n₀ + 1 with hn
  have hqn : q ^ n * s ≤ 1 := by
    have h1 : q ^ n ≤ q ^ n₀ := pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ n₀)
    have h2 : q ^ n * s ≤ 1 / (s + 1) * s :=
      mul_le_mul_of_nonneg_right (h1.trans hn₀.le) hs0
    have h3 : 1 / (s + 1) * s ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    exact h2.trans h3
  set v := neumannIter K with hv
  have hv0 := neumannIter_nonneg K hK
  refine ⟨fun i => ∑ m ∈ Finset.range n, lam⁻¹ ^ (m + 1) * v m i, ?_, ?_⟩
  · intro i
    have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (Nat.succ_pos n₀)
    have := Finset.single_le_sum (f := fun m => lam⁻¹ ^ (m + 1) * v m i)
      (fun m _ => mul_nonneg (pow_nonneg (inv_nonneg.mpr hlam.le) _) (hv0 m i)) h0
    simpa [hv, neumannIter] using this
  · intro i
    have hK' : ∑ j, K i j * ∑ m ∈ Finset.range n, lam⁻¹ ^ (m + 1) * v m j =
        ∑ m ∈ Finset.range n, lam⁻¹ ^ (m + 1) * v (m + 1) i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hv, neumannIter, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hK']
    have htel : lam * ∑ m ∈ Finset.range n, lam⁻¹ ^ (m + 1) * v m i -
        ∑ m ∈ Finset.range n, lam⁻¹ ^ (m + 1) * v (m + 1) i =
        ∑ m ∈ Finset.range n, (lam⁻¹ ^ m * v m i - lam⁻¹ ^ (m + 1) * v (m + 1) i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [pow_succ]
      field_simp
    rw [Finset.sum_range_sub' (fun m => lam⁻¹ ^ m * v m i)] at htel
    have hvn : lam⁻¹ ^ n * v n i ≤ 1 := by
      have h1 := neumannIter_le K hκ hnorm n i
      have h2 : lam⁻¹ ^ n * v n i ≤ lam⁻¹ ^ n * (κ ^ n * s) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (inv_nonneg.mpr hlam.le) _)
      have h3 : lam⁻¹ ^ n * (κ ^ n * s) = q ^ n * s := by
        rw [hq, div_pow, ← mul_assoc, inv_pow, inv_mul_eq_div]
      linarith
    have hv00 : v 0 i = 1 := rfl
    rw [pow_zero, one_mul, hv00] at htel
    linarith

open scoped Matrix.Norms.L2Operator in
/-- `‖E x‖₂² ≤ ‖E‖² ‖x‖₂²` for mathlib's `ℓ²` operator norm of a real matrix. -/
theorem opBound_of_l2 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (E : Matrix m n ℝ) (x : n → ℝ) :
    ∑ i, (∑ j, E i j * x j) ^ 2 ≤ ‖E‖ ^ 2 * ∑ j, x j ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec E ((EuclideanSpace.equiv n ℝ).symm x)
  have h1 : ‖(EuclideanSpace.equiv m ℝ).symm
      (E.mulVec ((EuclideanSpace.equiv n ℝ).symm x).ofLp)‖ ^ 2 =
      ∑ i, (∑ j, E i j * x j) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
  have h2 : ‖(EuclideanSpace.equiv n ℝ).symm x‖ ^ 2 = ∑ j, x j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

open scoped Matrix.Norms.L2Operator in
/-- `lem:peyre:weights` (existence form) with `λ > ‖K‖`, mathlib's `ℓ²` operator norm. -/
theorem exists_weights_l2 {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ)
    (hK : ∀ i j, 0 ≤ K i j) {lam : ℝ} (hlam : ‖K‖ < lam) :
    ∃ a : ι → ℝ, (∀ i, lam⁻¹ ≤ a i) ∧ ∀ i, ∑ j, K i j * a j ≤ lam * a i :=
  exists_weights K hK (norm_nonneg K) hlam (fun x => opBound_of_l2 K x)

/-- `lem:peyre:potential`: let `w^0, …, w^M ∈ [0,∞)^ι` and nonnegative matrices
`T_0, …, T_{M-1}` with `w^{l+1} ≥ w^l - T_l w^l` entrywise.  If the column sums
`c^{(l)}_k = ∑_i (T_l)_{ik}` satisfy `∑_l c^{(l)}_k ≤ λ < 1` for every `k`, then
`∑_k w^M_k ≥ (1 - λ) ∑_k w^0_k`.  (`0`-based: the paper's `T_l` is `T (l-1)`.) -/
theorem potential {ι : Type*} [Fintype ι] {M : ℕ} (w : ℕ → ι → ℝ)
    (T : Fin M → ι → ι → ℝ) (hw : ∀ l, l ≤ M → ∀ k, 0 ≤ w l k) (hT : ∀ l i k, 0 ≤ T l i k)
    (hrec : ∀ (l : Fin M) i, w l i - ∑ k, T l i k * w l k ≤ w ((l : ℕ) + 1) i)
    {lam : ℝ} (hlam : lam < 1) (hcol : ∀ k, ∑ l, ∑ i, T l i k ≤ lam) :
    (1 - lam) * ∑ k, w 0 k ≤ ∑ k, w M k := by
  classical
  set c : Fin M → ι → ℝ := fun l k => ∑ i, T l i k with hc
  have hc0 : ∀ l k, 0 ≤ c l k := fun l k => Finset.sum_nonneg (fun i _ => hT l i k)
  -- the column sums still to come
  set C : ℕ → ι → ℝ := fun j k => ∑ l : Fin M, if j ≤ (l : ℕ) then c l k else 0 with hC
  have hC0 : ∀ j k, 0 ≤ C j k := fun j k => Finset.sum_nonneg (fun l _ => by
    split_ifs
    · exact hc0 l k
    · exact le_refl 0)
  have hCle : ∀ j k, C j k ≤ lam := by
    intro j k
    refine le_trans (Finset.sum_le_sum (fun l _ => ?_)) (hcol k)
    split_ifs
    · exact le_refl _
    · exact hc0 l k
  have hCM : ∀ k, C M k = 0 := by
    intro k
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [ite_eq_right (by have := l.isLt; omega)]
  have hCstep : ∀ j (hj : j < M) k, C j k = c ⟨j, hj⟩ k + C (j + 1) k := by
    intro j hj k
    have hpt : ∀ l : Fin M, (if j ≤ (l : ℕ) then c l k else 0) =
        (if l = ⟨j, hj⟩ then c l k else 0) + (if j + 1 ≤ (l : ℕ) then c l k else 0) := by
      intro l
      by_cases h1 : (l : ℕ) = j
      · have hl : l = ⟨j, hj⟩ := Fin.ext h1
        rw [ite_eq_left (le_of_eq h1.symm), ite_eq_left hl, ite_eq_right (by omega), add_zero]
      · have h4 : l ≠ ⟨j, hj⟩ := fun h => h1 (by rw [h])
        rw [ite_eq_right h4, zero_add]
        by_cases h2 : j ≤ (l : ℕ)
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
    simp only [hC]
    rw [Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (⟨j, hj⟩ : Fin M), ite_eq_left (Finset.mem_univ _)]
  -- the potential
  set Φ : ℕ → ℝ := fun j => ∑ k, (1 - C j k) * w j k with hΦ
  have hmono : ∀ j, j < M → Φ j ≤ Φ (j + 1) := by
    intro j hj
    set l : Fin M := ⟨j, hj⟩ with hl
    have hlv : (l : ℕ) = j := rfl
    have hwj := hw j hj.le
    have hTw : ∀ k, 0 ≤ ∑ i, T l k i * w j i :=
      fun k => Finset.sum_nonneg (fun i _ => mul_nonneg (hT l k i) (hwj i))
    have h1 : ∀ k, (1 - C (j + 1) k) * (w j k - ∑ i, T l k i * w j i) ≤
        (1 - C (j + 1) k) * w (j + 1) k := by
      intro k
      have := hrec l k
      rw [hlv] at this
      exact mul_le_mul_of_nonneg_left this (by linarith [hCle (j + 1) k])
    have h2 : ∀ k, (1 - C (j + 1) k) * w j k - ∑ i, T l k i * w j i ≤
        (1 - C (j + 1) k) * (w j k - ∑ i, T l k i * w j i) := by
      intro k
      have := mul_nonneg (hC0 (j + 1) k) (hTw k)
      nlinarith
    have h3 : ∑ k, ∑ i, T l k i * w j i = ∑ i, c l i * w j i := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hc, Finset.sum_mul]
    have h4 : Φ j = ∑ k, ((1 - C (j + 1) k) * w j k) - ∑ k, c l k * w j k := by
      rw [hΦ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hCstep j hj k]
      ring
    calc Φ j = ∑ k, ((1 - C (j + 1) k) * w j k) - ∑ k, ∑ i, T l k i * w j i := by rw [h4, h3]
      _ = ∑ k, ((1 - C (j + 1) k) * w j k - ∑ i, T l k i * w j i) := by
          rw [Finset.sum_sub_distrib]
      _ ≤ ∑ k, (1 - C (j + 1) k) * w (j + 1) k :=
          Finset.sum_le_sum (fun k _ => (h2 k).trans (h1 k))
      _ = Φ (j + 1) := rfl
  have hchain : ∀ j, j ≤ M → Φ 0 ≤ Φ j := by
    intro j
    induction j with
    | zero => intro _; exact le_refl _
    | succ j ih => intro hj; exact (ih (by omega)).trans (hmono j (by omega))
  have hΦM : Φ M = ∑ k, w M k := by
    simp only [hΦ, hCM, sub_zero, one_mul]
  have hΦ0 : (1 - lam) * ∑ k, w 0 k ≤ Φ 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact mul_le_mul_of_nonneg_right (by linarith [hCle 0 k]) (hw 0 (Nat.zero_le _) k)
  rw [← hΦM]
  exact hΦ0.trans (hchain M le_rfl)

end Sarkozy.Peyre
