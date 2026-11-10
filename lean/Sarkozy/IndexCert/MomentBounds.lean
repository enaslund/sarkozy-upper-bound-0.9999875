module

public import Sarkozy.IndexCert.MomentCompute
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The analytic inequalities of the index-moment certificate (`cert:index-moment` at `a₀`)

`paper/sections/27_tail_index.tex`, `prop:imp:padic-price` and `cert:index-moment`. With
`b = a₀/18`, `a₀ = 8896611739/10¹³`, and `z_t = t^b`:
* `log_lt_of_pow_lt`, `le_log_of_two_pow_le`: logarithms from bit lengths and Mathlib's
  `0.6931471803 < log 2 < 0.6931471808`;
* `zpow_bounds`: for `1 ≤ t ≤ 2^{25}`, `1 ≤ z_t ≤ Ẑ = 1.000857` and
  `z_t − 1 ≤ bK · log t`, `bK = b · 1.000429`;
* `Lodd_sub_one_le`: `L_{p,64}(z) − 1 ≤ (z − 1)√p/(p − z) + 10^{-29}` for `p ≥ 3`, `1 ≤ z ≤ Ẑ`
  (V2-A's `PartVLaws.Lodd`); `Ltwo_sub_one_le`: the factor at `2`;
* `sqrt_div_le` (`√t/(t − Z)` is nonincreasing) and `sqrt_le_amgm` (`√p ≤ (p + q²)/(2q)`).

The per-prime terms and the summation by parts are in `MomentTerms.lean`.
-/

namespace Sarkozy.IndexCert

open Finset Real

/-- `a₀/18`, the exponent of `z_p = p^{a₀/18}`. -/
noncomputable def bExp : ℝ := 8896611739 / 10 ^ 13 / 18

/-- `bK = (a₀/18) · 1.000429`: `z_t − 1 ≤ bK log t` below `2^{25}`. -/
noncomputable def bK : ℝ := bExp * (1000429 / 10 ^ 6)

/-- `Ẑ = 1.000857`. -/
noncomputable def Zhat : ℝ := 1000857 / 10 ^ 6

theorem Zhat_eq : Zhat = (Zn : ℝ) / Zd := by
  unfold Zhat Zn Zd
  norm_num

/-! ## Logarithms and exponentials -/

/-- `n^k < 2^N` gives `log n < N · 0.6931471808 / k`. -/
theorem log_lt_of_pow_lt {n k N : ℕ} (hn : 0 < n) (hk : 0 < k) (h : n ^ k < 2 ^ N) :
    Real.log n < N * 0.6931471808 / k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (k : ℝ) * Real.log n < N * Real.log 2 := by
    rw [← Real.log_pow, ← Real.log_pow]
    apply Real.log_lt_log (by positivity)
    exact_mod_cast h
  have h2 := Real.log_two_lt_d9
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [lt_div_iff₀ hk']
  nlinarith

/-- `2^N ≤ n^k` gives `N · 0.6931471803 / k ≤ log n`. -/
theorem le_log_of_two_pow_le {n k N : ℕ} (hk : 0 < k) (h : 2 ^ N ≤ n ^ k) :
    N * 0.6931471803 / k ≤ Real.log n := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [zero_pow hk.ne'] at h
      exact absurd h (Nat.not_le.mpr (Nat.two_pow_pos N))
    · exact hn
  have h1 : (N : ℝ) * Real.log 2 ≤ k * Real.log n := by
    rw [← Real.log_pow, ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h
  have h2 := Real.log_two_gt_d9
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [div_le_iff₀ hk']
  nlinarith

/-- `e^y − 1 ≤ y + y²/2 + y³/4` for `0 ≤ y ≤ 1`. -/
theorem exp_sub_one_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp y - 1 ≤ y + y ^ 2 / 2 + y ^ 3 / 4 := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  nlinarith [pow_nonneg h0 3]

/-- **`z_t = t^{a₀/18}` below `2^{25}`**: `1 ≤ z_t ≤ Ẑ` and `z_t − 1 ≤ bK log t`. -/
theorem zpow_bounds {t : ℝ} (ht1 : 1 ≤ t) (ht : t ≤ 2 ^ 25) :
    1 ≤ t ^ bExp ∧ t ^ bExp ≤ Zhat ∧ t ^ bExp - 1 ≤ bK * Real.log t := by
  have ht0 : 0 < t := by linarith
  have hb0 : 0 ≤ bExp := by unfold bExp; norm_num
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlog : Real.log t ≤ 25 * 0.6931471808 := by
    have h1 : Real.log t ≤ Real.log (2 ^ 25) := Real.log_le_log ht0 ht
    rw [Real.log_pow] at h1
    have := Real.log_two_lt_d9
    push_cast at h1
    linarith
  set y := bExp * Real.log t with hy
  have hy0 : 0 ≤ y := mul_nonneg hb0 hlog0
  have hyY : y ≤ bExp * (25 * 0.6931471808) := mul_le_mul_of_nonneg_left hlog hb0
  have hY : bExp * (25 * 0.6931471808) ≤ 1 := by unfold bExp; norm_num
  have hz : t ^ bExp = Real.exp y := by
    rw [Real.rpow_def_of_pos ht0, hy, mul_comm]
  have hexp := exp_sub_one_le hy0 (hyY.trans hY)
  have hk : y + y ^ 2 / 2 + y ^ 3 / 4 ≤ y * (1000429 / 10 ^ 6) := by
    have hfac : 1 + y / 2 + y ^ 2 / 4 ≤ 1000429 / 10 ^ 6 := by
      have hY' : bExp * (25 * 0.6931471808) ≤ 857 / 10 ^ 6 := by unfold bExp; norm_num
      have hy' : y ≤ 857 / 10 ^ 6 := hyY.trans hY'
      nlinarith
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hz]
    exact Real.one_le_exp hy0
  · rw [hz]
    have hY' : bExp * (25 * 0.6931471808) * (1000429 / 10 ^ 6) ≤ 856999 / 10 ^ 9 := by
      unfold bExp; norm_num
    have : y * (1000429 / 10 ^ 6) ≤ bExp * (25 * 0.6931471808) * (1000429 / 10 ^ 6) :=
      mul_le_mul_of_nonneg_right hyY (by norm_num)
    unfold Zhat
    linarith
  · rw [hz]
    have : y * (1000429 / 10 ^ 6) = bK * Real.log t := by
      rw [hy]; unfold bK; ring
    linarith

/-! ## The factors `L_{p,64}` and `L_{2,64}` -/

/-- `√t/(t − Z)` is nonincreasing: for `s² ≤ t` and `Z < s²`, `√t/(t − Z) ≤ s/(s² − Z)`. -/
theorem sqrt_div_le {s t Z : ℝ} (hs : 0 ≤ s) (hZ : 0 ≤ Z) (hZs : Z < s ^ 2) (hst : s ^ 2 ≤ t) :
    Real.sqrt t / (t - Z) ≤ s / (s ^ 2 - Z) := by
  have hβ : s ≤ Real.sqrt t := Real.le_sqrt_of_sq_le hst
  have ht0 : 0 ≤ t := le_trans (sq_nonneg s) hst
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  have h1 : 0 < s ^ 2 - Z := by linarith
  have h2 : 0 < t - Z := by linarith
  rw [div_le_div_iff₀ h2 h1]
  set β := Real.sqrt t
  rw [← hsq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (add_nonneg (mul_nonneg hs (le_trans hs hβ)) hZ)]

/-- **AM-GM for the square root**: `√p ≤ (p + q²)/(2q)` for `q > 0`. -/
theorem sqrt_le_amgm {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.sqrt p ≤ (p + q ^ 2) / (2 * q) := by
  rw [le_div_iff₀ (by linarith)]
  have := Real.sq_sqrt hp
  nlinarith [sq_nonneg (Real.sqrt p - q)]

/-- **`L_{p,64}(z) − 1 ≤ (z − 1)√p/(p − z) + 10^{-29}`** for `p ≥ 3` and `1 ≤ z ≤ Ẑ`
(`prop:imp:padic-price`; the conditioning error `e_p = p^{-64}` is absorbed in `10^{-29}`). -/
theorem Lodd_sub_one_le {p : ℕ} (hp : 3 ≤ p) {z : ℝ} (hz1 : 1 ≤ z) (hz : z ≤ Zhat) :
    PartVLaws.Lodd p 64 z - 1 ≤ (z - 1) * Real.sqrt p / (p - z) + 1 / 10 ^ 29 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hZ : Zhat ≤ 2 := by unfold Zhat; norm_num
  have hpz : 0 < (p : ℝ) - z := by linarith
  set e := PartVLaws.topErr p 64 with he
  have he0 : 0 < e := PartVLaws.topErr_pos (by omega) 64
  have he3 : e ≤ 1 / 3 ^ 64 := by
    rw [he]
    unfold PartVLaws.topErr
    rw [one_div]
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by norm_num) hp' 64
  have he1 : e < 1 := lt_of_le_of_lt he3 (by norm_num)
  set A := (z - 1) * Real.sqrt p / (p - z) with hA
  have hA0 : 0 ≤ A := div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) hpz.le
  have hA1 : A ≤ 1 := by
    rw [hA, div_le_one hpz]
    have hs : Real.sqrt p ≤ p := by
      rw [Real.sqrt_le_left hp0.le]
      nlinarith
    have : z - 1 ≤ 1 / 1000 := by unfold Zhat at hz; linarith
    nlinarith [Real.sqrt_nonneg p]
  have hq0 : 0 < z / p := div_pos (by linarith) hp0
  have hq1 : z / p < 1 := (div_lt_one hp0).mpr (by linarith)
  have hgeo : (1 - (z / p) ^ 64) / (1 - z / p) ≤ p / (p - z) := by
    rw [div_le_div_iff₀ (by linarith) hpz]
    have h1 : (1 - (z / p) ^ 64) ≤ 1 := by
      have := pow_pos hq0 64
      linarith
    have h2 : (p : ℝ) / (p - z) * (1 - z / p) = 1 := by
      field_simp
    have h3 : (1 - z / p) * p = p - z := by field_simp
    nlinarith
  have hfirst : (z - 1) * (p : ℝ) ^ (-(1 : ℝ) / 2) * ((1 - (z / p) ^ 64) / (1 - z / p)) ≤ A := by
    have hrp : (p : ℝ) ^ (-(1 : ℝ) / 2) * p = Real.sqrt p := by
      rw [PartVLaws.sqrt_eq_mul_rpow hp0, mul_comm]
    have hr0 : 0 ≤ (p : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hp0.le _
    calc (z - 1) * (p : ℝ) ^ (-(1 : ℝ) / 2) * ((1 - (z / p) ^ 64) / (1 - z / p))
        ≤ (z - 1) * (p : ℝ) ^ (-(1 : ℝ) / 2) * (p / (p - z)) :=
          mul_le_mul_of_nonneg_left hgeo (mul_nonneg (by linarith) hr0)
      _ = A := by
          rw [hA, ← hrp]
          ring
  have hzm : z ^ 64 ≤ 2 := by
    calc z ^ 64 ≤ Zhat ^ 64 := pow_le_pow_left₀ (by linarith) hz 64
      _ ≤ 2 := by unfold Zhat; norm_num
  have hsecond : e * (z ^ 64 - 1) ≤ 2 * e := by nlinarith
  unfold PartVLaws.Lodd
  rw [← he]
  have hden : 0 < 1 - e := by linarith
  have key : ((z - 1) * (p : ℝ) ^ (-(1 : ℝ) / 2) * ((1 - (z / p) ^ 64) / (1 - z / p)) +
      e * (z ^ 64 - 1)) / (1 - e) ≤ (A + 2 * e) / (1 - e) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have key2 : (A + 2 * e) / (1 - e) ≤ A + 1 / 10 ^ 29 := by
    rw [div_le_iff₀ hden]
    have : 4 * e ≤ 1 / 10 ^ 29 := by
      have : (4 : ℝ) * (1 / 3 ^ 64) ≤ 1 / 10 ^ 29 := by norm_num
      linarith
    nlinarith
  linarith

/-- `ε₂ = bK · 0.6931471808`, the bound for `z₂ − 1`. -/
noncomputable def eps2 : ℝ := bK * 0.6931471808

/-- **`L_{2,64}(z) − 1`** for `1 ≤ z ≤ 1 + ε₂` (`prop:imp:padic-price`, the factor at `2`). -/
theorem Ltwo_sub_one_le {z : ℝ} (hz1 : 1 ≤ z) (hz : z ≤ 1 + eps2) :
    PartVLaws.Ltwo 64 z - 1 ≤ (eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) +
      2 / 2 ^ 64) / (1 - 1 / 2 ^ 64) := by
  have he2 : eps2 ≤ 1 / 10000 := by unfold eps2 bK bExp; norm_num
  have he20 : 0 ≤ eps2 := by unfold eps2 bK bExp; norm_num
  have e : PartVLaws.topErr 2 64 = 1 / 2 ^ 64 := by unfold PartVLaws.topErr; norm_num
  have h2z : 0 < 2 - z := by linarith
  have hc : (2 : ℝ) ^ (-(1 : ℝ) / 2) ≤ 70710679 / 10 ^ 8 :=
    PartVLaws.rpow_neg_half_le (by norm_num) (by norm_num)
  have hc0 : 0 ≤ (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hq : 0 ≤ (z / 2) ^ (64 - 1) := pow_nonneg (by linarith) _
  have hterm : z * (1 - (z / 2) ^ (64 - 1)) / (2 - z) ≤ (1 + eps2) / (1 - eps2) := by
    have h1 : z * (1 - (z / 2) ^ (64 - 1)) ≤ z := by nlinarith
    calc z * (1 - (z / 2) ^ (64 - 1)) / (2 - z) ≤ z / (2 - z) :=
          div_le_div_of_nonneg_right h1 h2z.le
      _ ≤ (1 + eps2) / (1 - eps2) := by
          rw [div_le_div_iff₀ h2z (by linarith)]
          nlinarith
  have hzm : z ^ (64 + 1) ≤ 2 := by
    calc z ^ (64 + 1) ≤ (1 + 1 / 10000 : ℝ) ^ (64 + 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ 2 := by norm_num
  have hden : (0 : ℝ) < 1 - 1 / 2 ^ 64 := by norm_num
  have h1 : (z - 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2) + z * (1 - (z / 2) ^ (64 - 1)) / (2 - z)) ≤
      eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) := by
    have hz0 : 0 ≤ z - 1 := by linarith
    have hin : 0 ≤ (2 : ℝ) ^ (-(1 : ℝ) / 2) + z * (1 - (z / 2) ^ (64 - 1)) / (2 - z) := by
      have : 0 ≤ z * (1 - (z / 2) ^ (64 - 1)) / (2 - z) := by
        apply div_nonneg _ h2z.le
        have : (z / 2) ^ (64 - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
        nlinarith
      linarith
    calc (z - 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2) + z * (1 - (z / 2) ^ (64 - 1)) / (2 - z))
        ≤ eps2 * ((2 : ℝ) ^ (-(1 : ℝ) / 2) + z * (1 - (z / 2) ^ (64 - 1)) / (2 - z)) :=
          mul_le_mul_of_nonneg_right (by linarith) hin
      _ ≤ eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) :=
          mul_le_mul_of_nonneg_left (by linarith) he20
  have h2 : 1 / 2 ^ 64 * (z ^ (64 + 1) - 1) ≤ (2 : ℝ) / 2 ^ 64 := by
    have : z ^ (64 + 1) - 1 ≤ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 / 2 ^ 64 := by norm_num
    calc 1 / 2 ^ 64 * (z ^ (64 + 1) - 1) ≤ 1 / 2 ^ 64 * 2 := mul_le_mul_of_nonneg_left this h0
      _ = 2 / 2 ^ 64 := by ring
  have key : (z - 1) * ((2 : ℝ) ^ (-(1 : ℝ) / 2) + z * (1 - (z / 2) ^ (64 - 1)) / (2 - z)) +
      1 / 2 ^ 64 * (z ^ (64 + 1) - 1) ≤
      eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64 := by linarith
  have key2 := div_le_div_of_nonneg_right key hden.le
  unfold PartVLaws.Ltwo
  rw [e]
  linarith

end Sarkozy.IndexCert
