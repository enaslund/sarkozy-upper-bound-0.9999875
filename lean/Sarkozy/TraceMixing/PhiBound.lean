module

public import Sarkozy.TraceMixing.PairCount

/-!
# The bounds for `φ_y` (`lem:trace-mixing`(c), "Bounds")

`paper/sections/12_labellings.tex`, proof of `lem:trace-mixing`(c). Pure inequalities: from
the counts of `PairCount.lean` for one row,

* `|Φ| ≥ q² 2^{-(t+1)} (1 - e)²`,
* `c_y ≤ q 2^{-s} (1 + e)` for every `y`,
* `q 2^{-t}(1 - e) ≤ c_y ≤ q 2^{-t}(1 + e)` for generic `y`,
* at most `n_×` non-generic `y`, and `|Φ| = ∑_{y ∈ Q} c_y`,

`phi_row_bound` gives `2/(q-1) ∑_{y ∈ Q} φ_y² ≤ φ_gen² + (2 n_×/(q-1)) φ_exc²` with
`φ_y = |Q| c_y/|Φ| - 1`, `η = n_× 2^{t-s+1}/(q-1)`, `φ_gen = 3e/(1-e)² + (1+e)η`,
`φ_exc = 2^{t-s}(1+e)/(1-e)²`. Also the error-term comparisons used to reduce the hypotheses
of (c) to the paper's (`coarseErr_mono`, `softError_div_le_lowerErr`).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

/-- `h_t = t/2 - 1 + 2^{-t}` is nondecreasing (`it:et:mono`). -/
theorem coarseH_succ (t : ℕ) :
    (t : ℝ) / 2 - 1 + (1 / 2) ^ t ≤ ((t + 1 : ℕ) : ℝ) / 2 - 1 + (1 / 2) ^ (t + 1) := by
  have h : ((1 : ℝ) / 2) ^ (t + 1) = (1 / 2) ^ t * (1 / 2) := pow_succ _ _
  have h1 : ((1 : ℝ) / 2) ^ t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  push_cast
  rw [h]
  nlinarith

theorem coarseH_mono {t t' : ℕ} (h : t ≤ t') :
    (t : ℝ) / 2 - 1 + (1 / 2) ^ t ≤ (t' : ℝ) / 2 - 1 + (1 / 2) ^ t' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (coarseH_succ _)

theorem coarseH_nonneg (t : ℕ) : 0 ≤ (t : ℝ) / 2 - 1 + (1 / 2) ^ t := by
  have := coarseH_mono (Nat.zero_le t)
  simpa using this

/-- `e_t(q, n)` is nondecreasing in `t` and `n` (`it:et:poly`). -/
theorem coarseErr_mono {q : ℝ} (hq : 0 < q) {t t' n n' : ℕ} (ht : t ≤ t') (hn : n ≤ n') :
    coarseErr q t n ≤ coarseErr q t' n' := by
  unfold coarseErr
  have hr : 0 < (Real.sqrt q)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hq)
  have hH := coarseH_mono ht
  have hH0 := coarseH_nonneg t
  have hnR : (n : ℝ) ≤ n' := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ t ≤ 2 ^ t' := pow_le_pow_right₀ (by norm_num) ht
  have hin : ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹ + n / q ≤
      ((t' : ℝ) / 2 - 1 + (1 / 2) ^ t') * (Real.sqrt q)⁻¹ + n' / q := by
    have h1 := mul_le_mul_of_nonneg_right hH hr.le
    have h2 : (n : ℝ) / q ≤ n' / q := div_le_div_of_nonneg_right hnR hq.le
    linarith
  have hin0 : 0 ≤ ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹ + n / q :=
    add_nonneg (mul_nonneg hH0 hr.le) (div_nonneg (Nat.cast_nonneg _) hq.le)
  calc 2 ^ t * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹ + n / q)
      ≤ 2 ^ t' * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹ + n / q) :=
        mul_le_mul_of_nonneg_right hpow hin0
    _ ≤ 2 ^ t' * (((t' : ℝ) / 2 - 1 + (1 / 2) ^ t') * (Real.sqrt q)⁻¹ + n' / q) :=
        mul_le_mul_of_nonneg_left hin (by positivity)

/-- `e^+_t = 𝔈_t/q ≤ e^-_t(z)`. -/
theorem softError_div_le_lowerErr {q : ℝ} (hq : 0 < q) (t z : ℕ) :
    softError q t / q ≤ lowerErr q t z := by
  unfold lowerErr
  apply div_le_div_of_nonneg_right _ hq.le
  have : (0 : ℝ) ≤ 2 ^ t * z := by positivity
  linarith

/-- The bound for a generic `y`: `|φ_y| ≤ φ_gen`. -/
theorem phi_gen_bound {q e P nQ c : ℝ} {t s nx : ℕ} (hq : 3 ≤ q) (hnQ : nQ = (q - 1) / 2)
    (he0 : 0 ≤ e) (he1 : e < 1) (hst : s ≤ t)
    (hlo : q / 2 ^ t * (1 - e) ≤ c) (hhi : c ≤ q / 2 ^ t * (1 + e))
    (hPlo : q ^ 2 / 2 ^ (t + 1) * (1 - e) ^ 2 ≤ P)
    (hPhi : P ≤ nQ * (q / 2 ^ t * (1 + e)) + nx * (q / 2 ^ s * (1 + e))) :
    (nQ * c / P - 1) ^ 2 ≤
      (3 * e / (1 - e) ^ 2 + (1 + e) * (nx * 2 ^ (t - s + 1) / (q - 1))) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hnQ0 : 0 < nQ := by rw [hnQ]; linarith
  have he1' : 0 < 1 - e := by linarith
  have he2 : 0 < 1 + e := by linarith
  have hpt : (0 : ℝ) < 2 ^ t := pow_pos two_pos t
  have hps : (0 : ℝ) < 2 ^ s := pow_pos two_pos s
  have hD : 0 < q ^ 2 / 2 ^ (t + 1) * (1 - e) ^ 2 :=
    mul_pos (div_pos (pow_pos hq0 2) (pow_pos two_pos _)) (pow_pos he1' 2)
  have hP0 : 0 < P := lt_of_lt_of_le hD hPlo
  have hc0 : 0 ≤ c := le_trans (mul_nonneg (div_nonneg hq0.le hpt.le) he1'.le) hlo
  set A : ℝ := 2 ^ s with hA
  set B : ℝ := 2 ^ (t - s) with hB
  have hA0 : 0 < A := hps
  have hB0 : 0 < B := pow_pos two_pos _
  have hts : (2 : ℝ) ^ t = B * A := by rw [hA, hB, ← pow_add, Nat.sub_add_cancel hst]
  have h2t : (2 : ℝ) ^ (t + 1) = 2 * B * A := by rw [pow_succ, hts]; ring
  have hB1 : (2 : ℝ) ^ (t - s + 1) = 2 * B := by rw [pow_succ, hB]; ring
  set η : ℝ := nx * 2 ^ (t - s + 1) / (q - 1) with hη
  have hη0 : 0 ≤ η := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_pos two_pos _).le) hq1.le
  rw [hts] at hlo hhi
  rw [h2t] at hPlo
  -- upper
  have hup : nQ * c / P - 1 ≤ 3 * e / (1 - e) ^ 2 := by
    have h1 : nQ * c / P ≤ nQ * (q / (B * A) * (1 + e)) / (q ^ 2 / (2 * B * A) * (1 - e) ^ 2) :=
      div_le_div₀ (mul_nonneg hnQ0.le (mul_nonneg (div_nonneg hq0.le (by positivity)) he2.le))
        (mul_le_mul_of_nonneg_left hhi hnQ0.le) (by rw [← h2t]; exact hD) hPlo
    have h2 : nQ * (q / (B * A) * (1 + e)) / (q ^ 2 / (2 * B * A) * (1 - e) ^ 2) =
        (q - 1) * (1 + e) / (q * (1 - e) ^ 2) := by
      rw [hnQ]
      field_simp
    have h3 : (q - 1) * (1 + e) / (q * (1 - e) ^ 2) - 1 ≤ 3 * e / (1 - e) ^ 2 := by
      rw [div_sub_one (mul_pos hq0 (pow_pos he1' 2)).ne',
        div_le_div_iff₀ (mul_pos hq0 (pow_pos he1' 2)) (pow_pos he1' 2)]
      nlinarith [sq_nonneg e, mul_nonneg hq0.le (sq_nonneg e), pow_pos he1' 2]
    linarith
  -- lower
  have hlow : -(2 * e + (1 + e) * η) ≤ nQ * c / P - 1 := by
    have hPmax : P ≤ nQ * (q / (B * A) * (1 + e)) * (1 + η) := by
      have : nQ * (q / (B * A) * (1 + e)) * (1 + η) =
          nQ * (q / 2 ^ t * (1 + e)) + nx * (q / A * (1 + e)) := by
        rw [hts, hη, hB1, hnQ]
        field_simp
      rw [this]
      exact hPhi
    have h1 : nQ * (q / (B * A) * (1 - e)) / (nQ * (q / (B * A) * (1 + e)) * (1 + η)) ≤
        nQ * c / P :=
      div_le_div₀ (mul_nonneg hnQ0.le hc0) (mul_le_mul_of_nonneg_left hlo hnQ0.le) hP0 hPmax
    have h2 : nQ * (q / (B * A) * (1 - e)) / (nQ * (q / (B * A) * (1 + e)) * (1 + η)) =
        (1 - e) / ((1 + e) * (1 + η)) := by
      have : (1 + η) ≠ 0 := by linarith
      field_simp
    rw [h2] at h1
    have h3 : -(2 * e + (1 + e) * η) ≤ (1 - e) / ((1 + e) * (1 + η)) - 1 := by
      have hpos : 0 < (1 + e) * (1 + η) := mul_pos he2 (by linarith)
      rw [div_sub_one hpos.ne', le_div_iff₀ hpos]
      nlinarith [mul_nonneg he0 hη0, mul_nonneg (mul_nonneg he0 hη0) hη0,
        mul_nonneg hη0 hη0, mul_nonneg (mul_nonneg he0 he0) hη0]
    linarith
  have hφ1 : 3 * e / (1 - e) ^ 2 ≤ 3 * e / (1 - e) ^ 2 + (1 + e) * η := by
    have : 0 ≤ (1 + e) * η := mul_nonneg he2.le hη0
    linarith
  have hφ2 : 2 * e + (1 + e) * η ≤ 3 * e / (1 - e) ^ 2 + (1 + e) * η := by
    have : 2 * e ≤ 3 * e / (1 - e) ^ 2 := by
      rw [le_div_iff₀ (pow_pos he1' 2)]
      have h1 : (1 - e) ^ 2 ≤ 1 := by nlinarith
      have h2 : 2 * e * (1 - e) ^ 2 ≤ 2 * e * 1 := mul_le_mul_of_nonneg_left h1 (by linarith)
      linarith
    linarith
  have habs : |nQ * c / P - 1| ≤ 3 * e / (1 - e) ^ 2 + (1 + e) * η :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc (nQ * c / P - 1) ^ 2 = |nQ * c / P - 1| ^ 2 := (sq_abs _).symm
    _ ≤ (3 * e / (1 - e) ^ 2 + (1 + e) * η) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- The bound for any `y`: `|φ_y| ≤ φ_exc`. -/
theorem phi_exc_bound {q e P nQ c : ℝ} {t s : ℕ} (hq : 3 ≤ q) (hnQ : nQ = (q - 1) / 2)
    (he0 : 0 ≤ e) (he1 : e < 1) (hst : s ≤ t) (hc0 : 0 ≤ c)
    (hU : c ≤ q / 2 ^ s * (1 + e)) (hPlo : q ^ 2 / 2 ^ (t + 1) * (1 - e) ^ 2 ≤ P) :
    (nQ * c / P - 1) ^ 2 ≤ (2 ^ (t - s) * (1 + e) / (1 - e) ^ 2) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hnQ0 : 0 < nQ := by rw [hnQ]; linarith
  have he1' : 0 < 1 - e := by linarith
  have he2 : 0 < 1 + e := by linarith
  have hD : 0 < q ^ 2 / 2 ^ (t + 1) * (1 - e) ^ 2 :=
    mul_pos (div_pos (pow_pos hq0 2) (pow_pos two_pos _)) (pow_pos he1' 2)
  have hP0 : 0 < P := lt_of_lt_of_le hD hPlo
  set A : ℝ := 2 ^ s with hA
  set B : ℝ := 2 ^ (t - s) with hB
  have hA0 : 0 < A := pow_pos two_pos s
  have hB0 : 0 < B := pow_pos two_pos _
  have hts : (2 : ℝ) ^ t = B * A := by rw [hA, hB, ← pow_add, Nat.sub_add_cancel hst]
  have h2t : (2 : ℝ) ^ (t + 1) = 2 * B * A := by rw [pow_succ, hts]; ring
  rw [h2t] at hPlo hD
  set φx : ℝ := B * (1 + e) / (1 - e) ^ 2 with hφx
  have hφx1 : 1 ≤ φx := by
    rw [hφx, le_div_iff₀ (pow_pos he1' 2)]
    have h1 : (1 : ℝ) ≤ B := one_le_pow₀ (by norm_num)
    nlinarith
  have hlo : -1 ≤ nQ * c / P - 1 := by
    have : 0 ≤ nQ * c / P := div_nonneg (mul_nonneg hnQ0.le hc0) hP0.le
    linarith
  have hup : nQ * c / P - 1 ≤ φx := by
    have h1 : nQ * c / P ≤ nQ * (q / A * (1 + e)) / (q ^ 2 / (2 * B * A) * (1 - e) ^ 2) :=
      div_le_div₀ (mul_nonneg hnQ0.le (mul_nonneg (div_nonneg hq0.le hA0.le) he2.le))
        (mul_le_mul_of_nonneg_left hU hnQ0.le) hD hPlo
    have h2 : nQ * (q / A * (1 + e)) / (q ^ 2 / (2 * B * A) * (1 - e) ^ 2) =
        (q - 1) / q * φx := by
      rw [hnQ, hφx]
      field_simp
    have h3 : (q - 1) / q * φx ≤ φx := by
      have : (q - 1) / q ≤ 1 := by rw [div_le_one hq0]; linarith
      nlinarith
    linarith
  have habs : |nQ * c / P - 1| ≤ φx := abs_le.mpr ⟨by linarith, hup⟩
  calc (nQ * c / P - 1) ^ 2 = |nQ * c / P - 1| ^ 2 := (sq_abs _).symm
    _ ≤ φx ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- **The row bound for `φ_y`.** -/
theorem phi_row_bound {ι : Type*} (Q : Finset ι) (gen : ι → Prop) [DecidablePred gen]
    {q e P nQ : ℝ} {t s nx : ℕ} (hq : 3 ≤ q) (hnQ : nQ = (q - 1) / 2) (hQ : (Q.card : ℝ) = nQ)
    (he0 : 0 ≤ e) (he1 : e < 1) (hst : s ≤ t)
    (c : ι → ℝ) (hc0 : ∀ y ∈ Q, 0 ≤ c y)
    (hPsum : P = ∑ y ∈ Q, c y)
    (hPlo : q ^ 2 / 2 ^ (t + 1) * (1 - e) ^ 2 ≤ P)
    (hU : ∀ y ∈ Q, c y ≤ q / 2 ^ s * (1 + e))
    (hG : ∀ y ∈ Q, gen y → q / 2 ^ t * (1 - e) ≤ c y ∧ c y ≤ q / 2 ^ t * (1 + e))
    (hN : ((Q.filter fun y => ¬ gen y).card : ℝ) ≤ nx) :
    2 / (q - 1) * ∑ y ∈ Q, (nQ * c y / P - 1) ^ 2 ≤
      (3 * e / (1 - e) ^ 2 + (1 + e) * (nx * 2 ^ (t - s + 1) / (q - 1))) ^ 2 +
        2 * nx / (q - 1) * (2 ^ (t - s) * (1 + e) / (1 - e) ^ 2) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hnQ0 : 0 < nQ := by rw [hnQ]; linarith
  have he2 : 0 < 1 + e := by linarith
  have hUt0 : 0 ≤ q / 2 ^ t * (1 + e) := mul_nonneg (div_nonneg hq0.le (by positivity)) he2.le
  have hUs0 : 0 ≤ q / 2 ^ s * (1 + e) := mul_nonneg (div_nonneg hq0.le (by positivity)) he2.le
  -- the upper bound on `|Φ|`
  have hPhi : P ≤ nQ * (q / 2 ^ t * (1 + e)) + nx * (q / 2 ^ s * (1 + e)) := by
    rw [hPsum, ← Finset.sum_filter_add_sum_filter_not Q gen]
    have h1 : ∑ y ∈ Q.filter gen, c y ≤ nQ * (q / 2 ^ t * (1 + e)) := by
      calc ∑ y ∈ Q.filter gen, c y ≤ ∑ _y ∈ Q.filter gen, q / 2 ^ t * (1 + e) :=
            Finset.sum_le_sum (fun y hy => (hG y (mem_filter.mp hy).1 (mem_filter.mp hy).2).2)
        _ = ((Q.filter gen).card : ℝ) * (q / 2 ^ t * (1 + e)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ nQ * (q / 2 ^ t * (1 + e)) := by
            apply mul_le_mul_of_nonneg_right _ hUt0
            rw [← hQ]
            exact_mod_cast card_filter_le Q gen
    have h2 : ∑ y ∈ Q.filter (fun y => ¬ gen y), c y ≤ nx * (q / 2 ^ s * (1 + e)) := by
      calc ∑ y ∈ Q.filter (fun y => ¬ gen y), c y
          ≤ ∑ _y ∈ Q.filter (fun y => ¬ gen y), q / 2 ^ s * (1 + e) :=
            Finset.sum_le_sum (fun y hy => hU y (mem_filter.mp hy).1)
        _ = ((Q.filter fun y => ¬ gen y).card : ℝ) * (q / 2 ^ s * (1 + e)) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ nx * (q / 2 ^ s * (1 + e)) := mul_le_mul_of_nonneg_right hN hUs0
    linarith
  set φg : ℝ := 3 * e / (1 - e) ^ 2 + (1 + e) * (nx * 2 ^ (t - s + 1) / (q - 1)) with hφg
  set φx : ℝ := 2 ^ (t - s) * (1 + e) / (1 - e) ^ 2 with hφx
  have hsum : ∑ y ∈ Q, (nQ * c y / P - 1) ^ 2 ≤ nQ * φg ^ 2 + nx * φx ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Q gen]
    have h1 : ∑ y ∈ Q.filter gen, (nQ * c y / P - 1) ^ 2 ≤ nQ * φg ^ 2 := by
      calc ∑ y ∈ Q.filter gen, (nQ * c y / P - 1) ^ 2 ≤ ∑ _y ∈ Q.filter gen, φg ^ 2 :=
            Finset.sum_le_sum (fun y hy => by
              obtain ⟨hlo, hhi⟩ := hG y (mem_filter.mp hy).1 (mem_filter.mp hy).2
              exact phi_gen_bound hq hnQ he0 he1 hst hlo hhi hPlo hPhi)
        _ = ((Q.filter gen).card : ℝ) * φg ^ 2 := by rw [sum_const, nsmul_eq_mul]
        _ ≤ nQ * φg ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            rw [← hQ]
            exact_mod_cast card_filter_le Q gen
    have h2 : ∑ y ∈ Q.filter (fun y => ¬ gen y), (nQ * c y / P - 1) ^ 2 ≤ nx * φx ^ 2 := by
      calc ∑ y ∈ Q.filter (fun y => ¬ gen y), (nQ * c y / P - 1) ^ 2
          ≤ ∑ _y ∈ Q.filter (fun y => ¬ gen y), φx ^ 2 :=
            Finset.sum_le_sum (fun y hy => phi_exc_bound hq hnQ he0 he1 hst
              (hc0 y (mem_filter.mp hy).1) (hU y (mem_filter.mp hy).1) hPlo)
        _ = ((Q.filter fun y => ¬ gen y).card : ℝ) * φx ^ 2 := by rw [sum_const, nsmul_eq_mul]
        _ ≤ nx * φx ^ 2 := mul_le_mul_of_nonneg_right hN (sq_nonneg _)
    linarith
  have hcoef : 2 / (q - 1) = 1 / nQ := by rw [hnQ]; field_simp
  rw [hcoef]
  calc 1 / nQ * ∑ y ∈ Q, (nQ * c y / P - 1) ^ 2 ≤ 1 / nQ * (nQ * φg ^ 2 + nx * φx ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hnQ0.le)
    _ = φg ^ 2 + 2 * nx / (q - 1) * φx ^ 2 := by
        rw [hnQ]
        field_simp

end Sarkozy.TraceMixing
