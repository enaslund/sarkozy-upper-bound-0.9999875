module

public import Sarkozy.IndexCert.MomentBounds
public import Sarkozy.Target

@[expose] public section



namespace Sarkozy.IndexCert

open Finset Real

/-! ## The per-prime terms -/

/-- The term `A(t) = (z_t − 1)√t/(t − z_t)`, `z_t = t^{a₀/18}`. -/
noncomputable def termA (t : ℝ) : ℝ := (t ^ bExp - 1) * Real.sqrt t / (t - t ^ bExp)

theorem termA_nonneg {t : ℝ} (ht : 3 ≤ t) (ht' : t ≤ 2 ^ 25) : 0 ≤ termA t := by
  obtain ⟨h1, h2, -⟩ := zpow_bounds (by linarith) ht'
  have hZ : Zhat ≤ 2 := by unfold Zhat; norm_num
  unfold termA
  exact div_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) (by linarith)

/-- **The small-prime term**: `A(p) ≤ bK · (0.6931471808/256) · tS(p)/2^{64}` for
`3 ≤ p ≤ 2^{25}`. -/
theorem small_term_le {p : ℕ} (hp : 3 ≤ p) (hp' : (p : ℝ) ≤ 2 ^ 25) :
    termA p ≤ bK * (0.6931471808 / kL) * ((tS p : ℝ) / FP) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  obtain ⟨hz1, hz, hzlog⟩ := zpow_bounds (t := (p : ℝ)) (by linarith) hp'
  set z := (p : ℝ) ^ bExp
  have hbK : 0 ≤ bK := by unfold bK bExp; norm_num
  have hZ : Zhat ≤ 2 := by unfold Zhat; norm_num
  -- the logarithm
  have hlog : Real.log p < (nB p + 1 : ℕ) * 0.6931471808 / kL :=
    log_lt_of_pow_lt (by omega) (by unfold kL; norm_num) (nB_spec (by omega)).2
  have hz1' : z - 1 ≤ bK * (0.6931471808 / kL) * ((nB p : ℝ) + 1) := by
    have : bK * Real.log p ≤ bK * ((nB p + 1 : ℕ) * 0.6931471808 / kL) :=
      mul_le_mul_of_nonneg_left hlog.le hbK
    push_cast at this
    calc z - 1 ≤ bK * Real.log p := hzlog
      _ ≤ bK * (((nB p : ℝ) + 1) * 0.6931471808 / kL) := this
      _ = bK * (0.6931471808 / kL) * ((nB p : ℝ) + 1) := by ring
  -- the square root
  have hR0 : (0 : ℝ) < (rS p : ℝ) := by exact_mod_cast rS_pos p
  have hD0 : (0 : ℝ) < (DS : ℝ) := by
    have : 0 < DS := Nat.two_pow_pos 20
    exact_mod_cast this
  set R : ℝ := (rS p : ℝ)
  set D : ℝ := (DS : ℝ)
  have hR : 0 < R := hR0
  have hD : 0 < D := hD0
  have hsq : Real.sqrt p ≤ ((p : ℝ) + (R / D) ^ 2) / (2 * (R / D)) :=
    sqrt_le_amgm (by linarith) (div_pos hR hD)
  -- the denominator
  have hZd : (0 : ℝ) < Zd := by unfold Zd; norm_num
  have hZle : Zn ≤ p * Zd := by unfold Zn Zd; omega
  have hpZ : 0 < (p : ℝ) * Zd - Zn := by
    have : (Zn : ℝ) < p * Zd := by
      have h : Zn < p * Zd := by unfold Zn Zd; omega
      exact_mod_cast h
    linarith
  have hpz : (p : ℝ) - Zhat ≤ p - z := by linarith
  have hpZh : 0 < (p : ℝ) - Zhat := by linarith
  -- the ceiling
  have hDn : 0 < 2 * rS p * DS * (p * Zd - Zn) := by
    have h1 := rS_pos p
    have h2 : 0 < p * Zd - Zn := by unfold Zn Zd; omega
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) h1) (Nat.two_pow_pos 20)) h2
  have hceil := le_ceilDiv_mul ((nB p + 1) * (p * DS * DS + rS p * rS p) * Zd * FP)
    (2 * rS p * DS * (p * Zd - Zn)) hDn
  have hceilR : ((nB p : ℝ) + 1) * ((p : ℝ) * D * D + R * R) * Zd * FP ≤
      (tS p : ℝ) * (2 * R * D * ((p : ℝ) * Zd - Zn)) := by
    have := hceil
    unfold tS at this ⊢
    have hc : (((nB p + 1) * (p * DS * DS + rS p * rS p) * Zd * FP : ℕ) : ℝ) ≤
        ((ceilDiv ((nB p + 1) * (p * DS * DS + rS p * rS p) * Zd * FP)
          (2 * rS p * DS * (p * Zd - Zn)) * (2 * rS p * DS * (p * Zd - Zn)) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast [Nat.cast_sub hZle] at hc
    exact hc
  have hF : (0 : ℝ) < FP := by unfold FP; norm_num
  -- the quotient
  have hq : ((nB p : ℝ) + 1) * (((p : ℝ) + (R / D) ^ 2) / (2 * (R / D))) / ((p : ℝ) - Zhat) ≤
      (tS p : ℝ) / FP := by
    have e1 : ((nB p : ℝ) + 1) * (((p : ℝ) + (R / D) ^ 2) / (2 * (R / D))) / ((p : ℝ) - Zhat) =
        ((nB p : ℝ) + 1) * ((p : ℝ) * D * D + R * R) * Zd / (2 * R * D * ((p : ℝ) * Zd - Zn)) := by
      rw [Zhat_eq]
      have hR' : R ≠ 0 := hR.ne'
      have hD' : D ≠ 0 := hD.ne'
      have hZd' : (Zd : ℝ) ≠ 0 := hZd.ne'
      have hpZ' : (p : ℝ) * Zd - Zn ≠ 0 := hpZ.ne'
      have hpZ'' : (p : ℝ) - Zn / Zd ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        apply hpZ'
        rw [h]
        field_simp
        ring
      field_simp
    have hden : 0 < 2 * R * D * ((p : ℝ) * Zd - Zn) :=
      mul_pos (mul_pos (mul_pos (by norm_num) hR) hD) hpZ
    rw [e1, div_le_div_iff₀ hden hF]
    linarith
  -- assemble
  unfold termA
  have hnum0 : 0 ≤ z - 1 := by linarith
  have hfrac : Real.sqrt p / ((p : ℝ) - z) ≤
      (((p : ℝ) + (R / D) ^ 2) / (2 * (R / D))) / ((p : ℝ) - Zhat) := by
    calc Real.sqrt p / ((p : ℝ) - z) ≤ Real.sqrt p / ((p : ℝ) - Zhat) :=
          div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hpZh hpz
      _ ≤ (((p : ℝ) + (R / D) ^ 2) / (2 * (R / D))) / ((p : ℝ) - Zhat) :=
          div_le_div_of_nonneg_right hsq hpZh.le
  have hfrac0 : 0 ≤ Real.sqrt p / ((p : ℝ) - z) :=
    div_nonneg (Real.sqrt_nonneg _) (by linarith)
  calc (z - 1) * Real.sqrt p / (p - z) = (z - 1) * (Real.sqrt p / ((p : ℝ) - z)) := by ring
    _ ≤ (bK * (0.6931471808 / kL) * ((nB p : ℝ) + 1)) *
          ((((p : ℝ) + (R / D) ^ 2) / (2 * (R / D))) / ((p : ℝ) - Zhat)) :=
        mul_le_mul hz1' hfrac hfrac0 (mul_nonneg (mul_nonneg hbK (div_nonneg (by norm_num)
          (Nat.cast_nonneg _))) (by linarith [(Nat.cast_nonneg (nB p) : (0 : ℝ) ≤ nB p)]))
    _ = bK * (0.6931471808 / kL) * (((nB p : ℝ) + 1) *
          (((p : ℝ) + (R / D) ^ 2) / (2 * (R / D))) / ((p : ℝ) - Zhat)) := by ring
    _ ≤ bK * (0.6931471808 / kL) * ((tS p : ℝ) / FP) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg hbK (div_nonneg (by norm_num)
          (Nat.cast_nonneg _)))

/-- **The large-prime term**: for `2 ≤ s`, `s² ≤ t ≤ 2^{25}`,
`A(t) ≤ bK · (gW s/2^{64}) · log t`. -/
theorem large_term_le {s : ℕ} (hs : 2 ≤ s) {t : ℝ} (hst : (s : ℝ) ^ 2 ≤ t) (ht : t ≤ 2 ^ 25) :
    termA t ≤ bK * ((gW s : ℝ) / FP) * Real.log t := by
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have ht1 : 1 ≤ t := by nlinarith
  obtain ⟨hz1, hz, hzlog⟩ := zpow_bounds ht1 ht
  set z := t ^ bExp
  have hZ : Zhat ≤ 2 := by unfold Zhat; norm_num
  have hZ0 : 0 ≤ Zhat := by unfold Zhat; norm_num
  have hZs : Zhat < (s : ℝ) ^ 2 := by nlinarith
  have htZ : 0 < t - Zhat := by linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  -- `√t/(t − z) ≤ s/(s² − Ẑ) ≤ gW s/2^{64}`
  have h1 : Real.sqrt t / (t - z) ≤ Real.sqrt t / (t - Zhat) :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) htZ (by linarith)
  have h2 := sqrt_div_le (by linarith) hZ0 hZs hst
  have hF : (0 : ℝ) < FP := by unfold FP; norm_num
  have hZd : (0 : ℝ) < Zd := by unfold Zd; norm_num
  have hpos : 0 < s * s * Zd - Zn := by
    have : 4 ≤ s * s := Nat.mul_le_mul hs hs
    unfold Zn Zd
    omega
  have hceil := le_ceilDiv_mul (s * FP * Zd) (s * s * Zd - Zn) hpos
  have hceilR : (s : ℝ) * FP * Zd ≤ (gW s : ℝ) * ((s : ℝ) * s * Zd - Zn) := by
    have hc : ((s * FP * Zd : ℕ) : ℝ) ≤ ((ceilDiv (s * FP * Zd) (s * s * Zd - Zn) *
        (s * s * Zd - Zn) : ℕ) : ℝ) := by exact_mod_cast hceil
    have hle' : Zn ≤ s * s * Zd := by
      have : 4 ≤ s * s := Nat.mul_le_mul hs hs
      unfold Zn Zd
      omega
    push_cast [Nat.cast_sub hle'] at hc
    unfold gW
    exact hc
  have hsZ : 0 < (s : ℝ) * s * Zd - Zn := by
    have : (Zn : ℝ) < s * s * Zd := by
      have h : Zn < s * s * Zd := by
        have : 4 ≤ s * s := Nat.mul_le_mul hs hs
        unfold Zn Zd
        omega
      exact_mod_cast h
    linarith
  have h3 : (s : ℝ) / ((s : ℝ) ^ 2 - Zhat) ≤ (gW s : ℝ) / FP := by
    rw [Zhat_eq]
    have e1 : (s : ℝ) / ((s : ℝ) ^ 2 - Zn / Zd) = (s : ℝ) * Zd / ((s : ℝ) * s * Zd - Zn) := by
      have hZd' : (Zd : ℝ) ≠ 0 := hZd.ne'
      have hne : (s : ℝ) ^ 2 - Zn / Zd ≠ 0 := by
        intro h
        have : (s : ℝ) * s * Zd - Zn = ((s : ℝ) ^ 2 - Zn / Zd) * Zd := by field_simp
        rw [h, zero_mul] at this
        linarith
      field_simp
    rw [e1, div_le_div_iff₀ hsZ hF]
    linarith
  have hfrac : Real.sqrt t / (t - z) ≤ (gW s : ℝ) / FP := h1.trans (h2.trans h3)
  have hfrac0 : 0 ≤ Real.sqrt t / (t - z) := div_nonneg (Real.sqrt_nonneg _) (by linarith)
  unfold termA
  calc (z - 1) * Real.sqrt t / (t - z) = (z - 1) * (Real.sqrt t / (t - z)) := by ring
    _ ≤ (bK * Real.log t) * ((gW s : ℝ) / FP) :=
        mul_le_mul hzlog hfrac hfrac0 (mul_nonneg (by unfold bK bExp; norm_num) hlog0)
    _ = bK * ((gW s : ℝ) / FP) * Real.log t := by ring

/-! ## The prime sums `θ(x; 4, 3)` -/

/-- `Θ(t) = ∑_{p < t, p prime, p ≡ 3 (mod 4)} log p`. -/
noncomputable def Theta (t : ℕ) : ℝ := ∑ p ∈ PartVLaws.indexPrimes t, Real.log p

/-- **The one-sided prime-count input**: `θ(x; 4, 3) ≤ x/2 + c√x` for `1 ≤ x ≤ 10¹⁰`. -/
def ThetaUpper (c : ℝ) : Prop :=
  ∀ x : ℝ, 1 ≤ x → x ≤ 10 ^ 10 → Target.theta4 x 3 ≤ x / 2 + c * Real.sqrt x

/-- `Target.ThetaSmall` (H2″, Ramaré–Rumely Thm 2 / BMOR Thm 1.9) gives `ThetaUpper 2.072`. -/
theorem thetaUpper_of_thetaSmall (h : Target.ThetaSmall) : ThetaUpper (2072 / 1000) := by
  intro x h1 h2
  have := (abs_le.mp (h x h1 h2)).2
  linarith

/-- `Target.ThetaSmallTable` (H2′, the table entry) gives `ThetaUpper 1.034832`. -/
theorem thetaUpper_of_thetaSmallTable (h : Target.ThetaSmallTable) :
    ThetaUpper (1034832 / 1000000) := by
  intro x h1 h2
  have := (abs_le.mp (h x h1 h2)).2
  linarith

theorem Theta_le_theta4 (t : ℕ) : Theta t ≤ Target.theta4 t 3 := by
  unfold Theta Target.theta4
  rw [Nat.floor_natCast]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    unfold PartVLaws.indexPrimes at hp
    rw [mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p _ _
    exact Real.log_natCast_nonneg p

/-- **`Θ(t) ≤ t/2 + c√t`** for `1 ≤ t ≤ 10¹⁰`, from `ThetaUpper c`. -/
theorem Theta_le {c : ℝ} (h : ThetaUpper c) {t : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ 10 ^ 10) :
    Theta t ≤ t / 2 + c * Real.sqrt t :=
  (Theta_le_theta4 t).trans (h t (by exact_mod_cast ht1) (by exact_mod_cast ht))

/-- **The exact small-prime count**: `Θ(2^{14}) ≥ 3024061 · 0.6931471803/256`. -/
theorem Theta_ge_small : (3024061 : ℝ) * 0.6931471803 / kL ≤ Theta (4 * 4096) := by
  unfold Theta
  have h : ∀ p ∈ PartVLaws.indexPrimes (4 * 4096),
      (nB p : ℝ) * 0.6931471803 / kL ≤ Real.log p := by
    intro p hp
    have hp3 := PartVLaws.three_le_of_mem_indexPrimes hp
    exact le_log_of_two_pow_le (by unfold kL; norm_num) (nB_spec (by omega)).1
  have hsum := sum_le_sum h
  rw [← sum_div, ← sum_mul] at hsum
  have hN : (∑ p ∈ PartVLaws.indexPrimes (4 * 4096), (nB p : ℝ)) = 3024061 := by
    rw [← Nat.cast_sum, sum_indexPrimes_eq, smallN_eq]
    norm_num
  rw [hN] at hsum
  exact hsum

/-! ## Summation by parts -/

/-- **Summation by parts on a grid** `x 0 ≤ x 1 ≤ ⋯`: if on each cell the increment of `F` is at
most `g k` times that of `Θ`, `g` is nonnegative and nonincreasing, `Θ(x (k+1)) ≤ U (k+1)` at the
inner points and `L₀ ≤ Θ(x 0)`, then
`F(x (m+1)) − F(x 0) ≤ g m Θ(x (m+1)) − g 0 L₀ + ∑_{k < m} (g k − g (k+1)) U (k+1)`. -/
theorem abel_bound (F Θ : ℕ → ℝ) (x : ℕ → ℕ) (g U : ℕ → ℝ) (L₀ : ℝ) :
    ∀ m : ℕ, (∀ k ≤ m, F (x (k + 1)) - F (x k) ≤ g k * (Θ (x (k + 1)) - Θ (x k))) →
      (∀ k < m, g (k + 1) ≤ g k) → 0 ≤ g 0 →
      (∀ k < m, Θ (x (k + 1)) ≤ U (k + 1)) → L₀ ≤ Θ (x 0) →
      F (x (m + 1)) - F (x 0) ≤
        g m * Θ (x (m + 1)) - g 0 * L₀ + ∑ k ∈ range m, (g k - g (k + 1)) * U (k + 1) := by
  intro m
  induction m with
  | zero =>
    intro hstep _ hg0 _ hL
    have h0 := hstep 0 le_rfl
    simp only [range_zero, sum_empty, add_zero, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hL hg0]
  | succ m ih =>
    intro hstep hanti hg0 hU hL
    have ih' := ih (fun k hk => hstep k (by omega)) (fun k hk => hanti k (by omega)) hg0
      (fun k hk => hU k (by omega)) hL
    have hs := hstep (m + 1) le_rfl
    have hgm : 0 ≤ g m - g (m + 1) := sub_nonneg.mpr (hanti m (by omega))
    have hUm := mul_le_mul_of_nonneg_left (hU m (by omega)) hgm
    rw [sum_range_succ]
    nlinarith

end Sarkozy.IndexCert
