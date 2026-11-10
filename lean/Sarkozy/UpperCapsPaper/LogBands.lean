module

public import Sarkozy.UpperCapsPaper.Tables
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Lower bounds for the band logarithms, without large powers

`log_ge_of_logCert`: if `X b = 2^m a` with `0 < b ≤ a`, put `u = (a - b)/(a + b) ∈ [0, 1)`, so
that `X = 2^m (1 + u)/(1 - u)`. The series `log(1 + u) - log(1 - u) = ∑ 2u^{2i+1}/(2i+1)`
(Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one`) has nonnegative terms, so each partial sum is
a lower bound, and Mathlib's `log 2 > 0.6931471803` gives
`log X ≥ m · 0.6931471803 + ∑_{i<K} 2u^{2i+1}/(2i+1)`. The finite hypothesis `LogCert` is this
inequality against `E · 0.6931471803 / J`, multiplied out over the common denominator
`10^10 J · 1·3⋯(2K-1) · (a+b)^{2K}`: a natural-number inequality between numbers of a few hundred
bits (`K = 12`, `a + b < 300`), checked by the kernel with `Nat.mul`, `Nat.add`, `Nat.pow` and
`Nat.ble` only.

`logBandCert_all`: the check holds on all 310 bands with `X_k = (bandOf k).1`, `E = E_k`,
`J = 200000` and `X_k = 2^m a/b` from `bandFrac` (in `bandsA`, `bandsB`, `bandsC` the band starts
are `167 · 2^40 = 2^47 · 167/128`, `(84 + i) 2^41 = 2^47 (84 + i)/64`,
`2^{42+c}(64 + j) = 2^{48+c}(64 + j)/64`; in `bandsD` they are powers of two). It is split into
31 kernel checks of ten bands each.
-/

@[expose] public section

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.PartV

/-- `1 · 3 · 5 ⋯ (2K - 1)`. -/
def oddProd : ℕ → ℕ
  | 0 => 1
  | K + 1 => oddProd K * (2 * K + 1)

/-- The numerator of `∑_{i<K} 2 (p/q)^{2i+1}/(2i+1)` over `oddProd K · q^{2K-1}`
(`atanhNum_mul`). -/
def atanhNum (p q : ℕ) : ℕ → ℕ
  | 0 => 0
  | K + 1 => (2 * K + 1) * q ^ 2 * atanhNum p q K + 2 * oddProd K * p ^ (2 * K + 1)

theorem oddProd_pos (K : ℕ) : 0 < oddProd K := by
  induction K with
  | zero => simp [oddProd]
  | succ K ih => simp only [oddProd]; positivity

/-- `atanhNum p q K · q = oddProd K · q^{2K} · ∑_{i<K} 2 (p/q)^{2i+1}/(2i+1)`. -/
theorem atanhNum_mul (p q K : ℕ) (hq : 0 < q) :
    (atanhNum p q K : ℝ) * q = oddProd K * (q : ℝ) ^ (2 * K) *
      ∑ i ∈ Finset.range K, (2 : ℝ) * (1 / (2 * i + 1)) * ((p : ℝ) / q) ^ (2 * i + 1) := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  induction K with
  | zero => simp [atanhNum, oddProd]
  | succ K ih =>
    have h1 : (2 * (K : ℝ) + 1) ≠ 0 := by positivity
    have e : (atanhNum p q (K + 1) : ℝ) * q = (2 * (K : ℝ) + 1) * (q : ℝ) ^ 2 *
        ((atanhNum p q K : ℝ) * q) + 2 * (oddProd K : ℝ) * (p : ℝ) ^ (2 * K + 1) * q := by
      simp only [atanhNum]
      push_cast
      ring
    have e2 : (oddProd (K + 1) : ℝ) = oddProd K * (2 * (K : ℝ) + 1) := by
      simp only [oddProd]
      push_cast
      ring
    rw [Finset.sum_range_succ, e, ih, e2, div_pow]
    field_simp
    ring

/-- **The finite certificate** for `log X ≥ E · 0.6931471803 / J`, with `X = 2^m a/b`,
`u = (a - b)/(a + b)` and `K` terms of the series of `log((1+u)/(1-u))`. -/
def LogCert (X E J m a b K : ℕ) : Prop :=
  X * b = 2 ^ m * a ∧ 0 < b ∧ b ≤ a ∧
    E * 6931471803 * (oddProd K * (a + b) ^ (2 * K)) ≤
      m * 6931471803 * J * (oddProd K * (a + b) ^ (2 * K)) +
        10 ^ 10 * J * (atanhNum (a - b) (a + b) K * (a + b))

instance (X E J m a b K : ℕ) : Decidable (LogCert X E J m a b K) := by
  unfold LogCert
  infer_instance

/-- **`LogCert` gives `E · 0.6931471803 / J ≤ log X`**. -/
theorem log_ge_of_logCert {X E J m a b K : ℕ} (hJ : 0 < J) (h : LogCert X E J m a b K) :
    (E : ℝ) * 0.6931471803 / J ≤ Real.log X := by
  obtain ⟨hX, hb, hba, hN⟩ := h
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have ha' : (0 : ℝ) < a := by exact_mod_cast hb.trans_le hba
  have hq : 0 < a + b := by omega
  have hq' : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast hq
  have hpq : a - b < a + b := by omega
  have hp : (((a - b : ℕ) : ℝ)) = a - b := by push_cast [Nat.cast_sub hba]; ring
  set u : ℝ := ((a - b : ℕ) : ℝ) / ((a + b : ℕ) : ℝ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hq']
    exact_mod_cast hpq
  -- the partial sum is a lower bound for `log a - log b`
  set S := ∑ i ∈ Finset.range K, (2 : ℝ) * (1 / (2 * i + 1)) * u ^ (2 * i + 1) with hS
  have hsum := Real.hasSum_log_sub_log_of_abs_lt_one (x := u) (by rwa [abs_of_nonneg hu0])
  have hSle : S ≤ Real.log (1 + u) - Real.log (1 - u) :=
    sum_le_hasSum (Finset.range K) (fun i _ => by positivity) hsum
  have h1u : 1 + u = 2 * a / ((a + b : ℕ) : ℝ) := by
    rw [hu, hp]
    field_simp
    push_cast
    ring
  have h1u' : 1 - u = 2 * b / ((a + b : ℕ) : ℝ) := by
    rw [hu, hp]
    field_simp
    push_cast
    ring
  have hlogr : Real.log (1 + u) - Real.log (1 - u) = Real.log a - Real.log b := by
    rw [h1u, h1u', Real.log_div (by positivity) hq'.ne', Real.log_div (by positivity) hq'.ne',
      Real.log_mul (by norm_num) ha'.ne', Real.log_mul (by norm_num) hb'.ne']
    ring
  -- `log X = m log 2 + log a - log b`
  have hXr : (X : ℝ) = 2 ^ m * a / b := by
    rw [eq_div_iff hb'.ne']
    exact_mod_cast hX
  have hlogX : Real.log X = m * Real.log 2 + (Real.log a - Real.log b) := by
    rw [hXr, Real.log_div (by positivity) hb'.ne', Real.log_mul (by positivity) ha'.ne',
      Real.log_pow]
    ring
  -- the natural-number inequality, over the reals
  have hR : (E : ℝ) * 6931471803 * (oddProd K * ((a + b : ℕ) : ℝ) ^ (2 * K)) ≤
      m * 6931471803 * J * (oddProd K * ((a + b : ℕ) : ℝ) ^ (2 * K)) +
        10 ^ 10 * J * ((atanhNum (a - b) (a + b) K : ℝ) * ((a + b : ℕ) : ℝ)) := by
    exact_mod_cast hN
  rw [atanhNum_mul _ _ _ hq] at hR
  have hD : (0 : ℝ) < oddProd K * ((a + b : ℕ) : ℝ) ^ (2 * K) := by
    have := oddProd_pos K
    positivity
  have key : (E : ℝ) * 6931471803 ≤ m * 6931471803 * J + 10 ^ 10 * J * S := by
    refine le_of_mul_le_mul_right ?_ hD
    calc (E : ℝ) * 6931471803 * (oddProd K * ((a + b : ℕ) : ℝ) ^ (2 * K)) ≤ _ := hR
      _ = _ := by rw [hS]; ring
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have h2 : (0.6931471803 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have t1 : (m : ℝ) * J * 0.6931471803 ≤ m * J * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have t2 : (J : ℝ) * S ≤ J * (Real.log a - Real.log b) :=
    mul_le_mul_of_nonneg_left (hSle.trans hlogr.le) hJ'.le
  rw [hlogX, div_le_iff₀ hJ']
  nlinarith

/-- `(m, a, b)` with `X_k = 2^m a/b` and `b ≤ a < 2b`, band by band (`upperBands`). -/
def bandFracs : List (ℕ × ℕ × ℕ) :=
  [(47, 167, 128)] ++ (List.range 44).map (fun i => (47, 84 + i, 64)) ++
    (List.range 4).flatMap (fun c => (List.range 64).map fun j => (48 + c, 64 + j, 64)) ++
      [52, 53, 54, 55, 56, 57, 58, 60, 64].map fun e => (e, 1, 1)

/-- The triple `(m, a, b)` of band `k`. -/
def bandFrac (k : Fin 310) : ℕ × ℕ × ℕ := bandFracs.getD k.val (0, 1, 1)

/-- The certificate of band `k`: `LogCert` at `X_k`, `E_k`, `J = 200000` and `K = 12`. -/
def LogBandCert (k : Fin 310) : Prop :=
  LogCert (bandOf k).1 (logE.getD k.val 0) logJ (bandFrac k).1 (bandFrac k).2.1 (bandFrac k).2.2 12

instance (k : Fin 310) : Decidable (LogBandCert k) := by
  unfold LogBandCert
  infer_instance

/-- The band certificates `0 ≤ k < 10` (kernel). -/
theorem logBandCert_0 : ∀ k : Fin 310, 0 ≤ k.val → k.val < 10 → LogBandCert k := by
  decide +kernel

/-- The band certificates `10 ≤ k < 20` (kernel). -/
theorem logBandCert_1 : ∀ k : Fin 310, 10 ≤ k.val → k.val < 20 → LogBandCert k := by
  decide +kernel

/-- The band certificates `20 ≤ k < 30` (kernel). -/
theorem logBandCert_2 : ∀ k : Fin 310, 20 ≤ k.val → k.val < 30 → LogBandCert k := by
  decide +kernel

/-- The band certificates `30 ≤ k < 40` (kernel). -/
theorem logBandCert_3 : ∀ k : Fin 310, 30 ≤ k.val → k.val < 40 → LogBandCert k := by
  decide +kernel

/-- The band certificates `40 ≤ k < 50` (kernel). -/
theorem logBandCert_4 : ∀ k : Fin 310, 40 ≤ k.val → k.val < 50 → LogBandCert k := by
  decide +kernel

/-- The band certificates `50 ≤ k < 60` (kernel). -/
theorem logBandCert_5 : ∀ k : Fin 310, 50 ≤ k.val → k.val < 60 → LogBandCert k := by
  decide +kernel

/-- The band certificates `60 ≤ k < 70` (kernel). -/
theorem logBandCert_6 : ∀ k : Fin 310, 60 ≤ k.val → k.val < 70 → LogBandCert k := by
  decide +kernel

/-- The band certificates `70 ≤ k < 80` (kernel). -/
theorem logBandCert_7 : ∀ k : Fin 310, 70 ≤ k.val → k.val < 80 → LogBandCert k := by
  decide +kernel

/-- The band certificates `80 ≤ k < 90` (kernel). -/
theorem logBandCert_8 : ∀ k : Fin 310, 80 ≤ k.val → k.val < 90 → LogBandCert k := by
  decide +kernel

/-- The band certificates `90 ≤ k < 100` (kernel). -/
theorem logBandCert_9 : ∀ k : Fin 310, 90 ≤ k.val → k.val < 100 → LogBandCert k := by
  decide +kernel

/-- The band certificates `100 ≤ k < 110` (kernel). -/
theorem logBandCert_10 : ∀ k : Fin 310, 100 ≤ k.val → k.val < 110 → LogBandCert k := by
  decide +kernel

/-- The band certificates `110 ≤ k < 120` (kernel). -/
theorem logBandCert_11 : ∀ k : Fin 310, 110 ≤ k.val → k.val < 120 → LogBandCert k := by
  decide +kernel

/-- The band certificates `120 ≤ k < 130` (kernel). -/
theorem logBandCert_12 : ∀ k : Fin 310, 120 ≤ k.val → k.val < 130 → LogBandCert k := by
  decide +kernel

/-- The band certificates `130 ≤ k < 140` (kernel). -/
theorem logBandCert_13 : ∀ k : Fin 310, 130 ≤ k.val → k.val < 140 → LogBandCert k := by
  decide +kernel

/-- The band certificates `140 ≤ k < 150` (kernel). -/
theorem logBandCert_14 : ∀ k : Fin 310, 140 ≤ k.val → k.val < 150 → LogBandCert k := by
  decide +kernel

/-- The band certificates `150 ≤ k < 160` (kernel). -/
theorem logBandCert_15 : ∀ k : Fin 310, 150 ≤ k.val → k.val < 160 → LogBandCert k := by
  decide +kernel

/-- The band certificates `160 ≤ k < 170` (kernel). -/
theorem logBandCert_16 : ∀ k : Fin 310, 160 ≤ k.val → k.val < 170 → LogBandCert k := by
  decide +kernel

/-- The band certificates `170 ≤ k < 180` (kernel). -/
theorem logBandCert_17 : ∀ k : Fin 310, 170 ≤ k.val → k.val < 180 → LogBandCert k := by
  decide +kernel

/-- The band certificates `180 ≤ k < 190` (kernel). -/
theorem logBandCert_18 : ∀ k : Fin 310, 180 ≤ k.val → k.val < 190 → LogBandCert k := by
  decide +kernel

/-- The band certificates `190 ≤ k < 200` (kernel). -/
theorem logBandCert_19 : ∀ k : Fin 310, 190 ≤ k.val → k.val < 200 → LogBandCert k := by
  decide +kernel

/-- The band certificates `200 ≤ k < 210` (kernel). -/
theorem logBandCert_20 : ∀ k : Fin 310, 200 ≤ k.val → k.val < 210 → LogBandCert k := by
  decide +kernel

/-- The band certificates `210 ≤ k < 220` (kernel). -/
theorem logBandCert_21 : ∀ k : Fin 310, 210 ≤ k.val → k.val < 220 → LogBandCert k := by
  decide +kernel

/-- The band certificates `220 ≤ k < 230` (kernel). -/
theorem logBandCert_22 : ∀ k : Fin 310, 220 ≤ k.val → k.val < 230 → LogBandCert k := by
  decide +kernel

/-- The band certificates `230 ≤ k < 240` (kernel). -/
theorem logBandCert_23 : ∀ k : Fin 310, 230 ≤ k.val → k.val < 240 → LogBandCert k := by
  decide +kernel

/-- The band certificates `240 ≤ k < 250` (kernel). -/
theorem logBandCert_24 : ∀ k : Fin 310, 240 ≤ k.val → k.val < 250 → LogBandCert k := by
  decide +kernel

/-- The band certificates `250 ≤ k < 260` (kernel). -/
theorem logBandCert_25 : ∀ k : Fin 310, 250 ≤ k.val → k.val < 260 → LogBandCert k := by
  decide +kernel

/-- The band certificates `260 ≤ k < 270` (kernel). -/
theorem logBandCert_26 : ∀ k : Fin 310, 260 ≤ k.val → k.val < 270 → LogBandCert k := by
  decide +kernel

/-- The band certificates `270 ≤ k < 280` (kernel). -/
theorem logBandCert_27 : ∀ k : Fin 310, 270 ≤ k.val → k.val < 280 → LogBandCert k := by
  decide +kernel

/-- The band certificates `280 ≤ k < 290` (kernel). -/
theorem logBandCert_28 : ∀ k : Fin 310, 280 ≤ k.val → k.val < 290 → LogBandCert k := by
  decide +kernel

/-- The band certificates `290 ≤ k < 300` (kernel). -/
theorem logBandCert_29 : ∀ k : Fin 310, 290 ≤ k.val → k.val < 300 → LogBandCert k := by
  decide +kernel

/-- The band certificates `300 ≤ k < 310` (kernel). -/
theorem logBandCert_30 : ∀ k : Fin 310, 300 ≤ k.val → k.val < 310 → LogBandCert k := by
  decide +kernel

/-- **The band certificates on all 310 bands.** -/
theorem logBandCert_all (k : Fin 310) : LogBandCert k := by
  have hk := k.isLt
  by_cases h0 : k.val < 10
  · exact logBandCert_0 k (by omega) h0
  by_cases h1 : k.val < 20
  · exact logBandCert_1 k (by omega) h1
  by_cases h2 : k.val < 30
  · exact logBandCert_2 k (by omega) h2
  by_cases h3 : k.val < 40
  · exact logBandCert_3 k (by omega) h3
  by_cases h4 : k.val < 50
  · exact logBandCert_4 k (by omega) h4
  by_cases h5 : k.val < 60
  · exact logBandCert_5 k (by omega) h5
  by_cases h6 : k.val < 70
  · exact logBandCert_6 k (by omega) h6
  by_cases h7 : k.val < 80
  · exact logBandCert_7 k (by omega) h7
  by_cases h8 : k.val < 90
  · exact logBandCert_8 k (by omega) h8
  by_cases h9 : k.val < 100
  · exact logBandCert_9 k (by omega) h9
  by_cases h10 : k.val < 110
  · exact logBandCert_10 k (by omega) h10
  by_cases h11 : k.val < 120
  · exact logBandCert_11 k (by omega) h11
  by_cases h12 : k.val < 130
  · exact logBandCert_12 k (by omega) h12
  by_cases h13 : k.val < 140
  · exact logBandCert_13 k (by omega) h13
  by_cases h14 : k.val < 150
  · exact logBandCert_14 k (by omega) h14
  by_cases h15 : k.val < 160
  · exact logBandCert_15 k (by omega) h15
  by_cases h16 : k.val < 170
  · exact logBandCert_16 k (by omega) h16
  by_cases h17 : k.val < 180
  · exact logBandCert_17 k (by omega) h17
  by_cases h18 : k.val < 190
  · exact logBandCert_18 k (by omega) h18
  by_cases h19 : k.val < 200
  · exact logBandCert_19 k (by omega) h19
  by_cases h20 : k.val < 210
  · exact logBandCert_20 k (by omega) h20
  by_cases h21 : k.val < 220
  · exact logBandCert_21 k (by omega) h21
  by_cases h22 : k.val < 230
  · exact logBandCert_22 k (by omega) h22
  by_cases h23 : k.val < 240
  · exact logBandCert_23 k (by omega) h23
  by_cases h24 : k.val < 250
  · exact logBandCert_24 k (by omega) h24
  by_cases h25 : k.val < 260
  · exact logBandCert_25 k (by omega) h25
  by_cases h26 : k.val < 270
  · exact logBandCert_26 k (by omega) h26
  by_cases h27 : k.val < 280
  · exact logBandCert_27 k (by omega) h27
  by_cases h28 : k.val < 290
  · exact logBandCert_28 k (by omega) h28
  by_cases h29 : k.val < 300
  · exact logBandCert_29 k (by omega) h29
  exact logBandCert_30 k (by omega) (by omega)

/-- **`log X_k ≥ E_k · 0.6931471803 / J`** on every band. -/
theorem log_band_ge_logE (k : Fin 310) :
    (logE.getD k.val 0 : ℝ) * 0.6931471803 / logJ ≤ Real.log ((bandOf k).1 : ℝ) :=
  log_ge_of_logCert (by norm_num [logJ]) (logBandCert_all k)

end Sarkozy.UpperCapsPaper
