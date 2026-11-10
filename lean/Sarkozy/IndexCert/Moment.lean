module

public import Sarkozy.IndexCert.MomentTerms
public import Sarkozy.PaperData.IndexLaw
public import Sarkozy.LedgerAnchor.Sanity

@[expose] public section






namespace Sarkozy.IndexCert

open Finset Real

/-- The sum of `A(p)` over the primes `p ≡ 3 (mod 4)` below `t`. -/
noncomputable def Fsum (t : ℕ) : ℝ := ∑ p ∈ PartVLaws.indexPrimes t, termA p

theorem indexPrimes_mono {t t' : ℕ} (h : t ≤ t') :
    PartVLaws.indexPrimes t ⊆ PartVLaws.indexPrimes t' := by
  intro p hp
  unfold PartVLaws.indexPrimes at hp ⊢
  rw [mem_filter, mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- **One cell of the grid**: if `A(p) ≤ G log p` for the primes of `[t, t')`, then
`F(t') − F(t) ≤ G (Θ(t') − Θ(t))`. -/
theorem cell_bound {t t' : ℕ} (htt : t ≤ t') (G : ℝ)
    (hG : ∀ p ∈ PartVLaws.indexPrimes t', t ≤ p → termA p ≤ G * Real.log p) :
    Fsum t' - Fsum t ≤ G * (Theta t' - Theta t) := by
  have hsub := indexPrimes_mono htt
  unfold Fsum Theta
  rw [← sum_sdiff hsub, ← sum_sdiff hsub (f := fun p : ℕ => Real.log p)]
  simp only [add_sub_cancel_right]
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  rw [mem_sdiff] at hp
  apply hG p hp.1
  by_contra hlt
  apply hp.2
  unfold PartVLaws.indexPrimes at hp ⊢
  rw [mem_filter, mem_range] at hp ⊢
  exact ⟨by omega, hp.1.2⟩

/-- The grid: `x k = (128 + k)²` for `k ≤ 4338`, then `Q₃`. -/
def grid (k : ℕ) : ℕ := if k ≤ 4338 then (128 + k) ^ 2 else PartV.Q3

/-- **The bound on `log M_pad(K)`**, explicit in the constant `c` of `ThetaUpper c`: the
`K`-factor, the factor at `2`, the small primes, the Abel sum, and the conditioning errors. -/
noncomputable def Tbound (c : ℝ) : ℝ :=
  5049 * 0.6931471808 / 256 * (8896611739 / 10 ^ 13 / 36) +
  (eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) / (1 - 1 / 2 ^ 64) +
  bK * (0.6931471808 / 256) * (861202739404713745892444 / 2 ^ 64) +
  bK / 2 ^ 64 * (4130484773707033 * (19951586 / 2 + 4467 * c) -
    144123992244954158 * (3024061 * 0.6931471803 / 256) +
    80087994762344705953805 / 2 + c * 65598638960976287003) +
  19951586 * (1 / 10 ^ 29)

/-- **The sum of the terms `A(p)` over all `p < Q₃`**, from `ThetaUpper c`. -/
theorem Fsum_Q3_le {c : ℝ} (hc : 0 ≤ c) (h : ThetaUpper c) :
    Fsum PartV.Q3 ≤ bK * (0.6931471808 / 256) * (861202739404713745892444 / 2 ^ 64) +
      bK / 2 ^ 64 * (4130484773707033 * (19951586 / 2 + 4467 * c) -
        144123992244954158 * (3024061 * 0.6931471803 / 256) +
        80087994762344705953805 / 2 + c * 65598638960976287003) := by
  have hQ : PartV.Q3 = 19951586 := rfl
  have hbK : 0 ≤ bK := by unfold bK bExp; norm_num
  have hF : (FP : ℝ) = 2 ^ 64 := by unfold FP; norm_num
  have hkL : (kL : ℝ) = 256 := by unfold kL; norm_num
  -- the small primes
  have hsmall : Fsum (4 * 4096) ≤ bK * (0.6931471808 / 256) * (861202739404713745892444 / 2 ^ 64) := by
    unfold Fsum
    have h1 : ∀ p ∈ PartVLaws.indexPrimes (4 * 4096),
        termA p ≤ bK * (0.6931471808 / kL) * ((tS p : ℝ) / FP) := by
      intro p hp
      have hp3 := PartVLaws.three_le_of_mem_indexPrimes hp
      have hlt : p < 4 * 4096 := mem_range.mp (mem_filter.mp hp).1
      exact small_term_le hp3 (by
        have : (p : ℝ) ≤ 4 * 4096 := by exact_mod_cast hlt.le
        linarith)
    refine (sum_le_sum h1).trans (le_of_eq ?_)
    rw [← mul_sum, ← sum_div, ← Nat.cast_sum, sum_indexPrimes_eq, smallT_eq, hF, hkL]
    norm_num
  -- the Abel sum
  set g : ℕ → ℝ := fun k => bK * ((gW (128 + k) : ℝ) / FP) with hg
  set U : ℕ → ℝ := fun j => ((128 + j : ℕ) : ℝ) ^ 2 / 2 + c * (128 + j : ℕ) with hU
  set L₀ : ℝ := (3024061 : ℝ) * 0.6931471803 / kL with hL₀
  have hanti := gW_anti_of viol_eq
  have habel := abel_bound Fsum Theta grid g U L₀ 4338
    (by
      intro k hk
      apply cell_bound
      · unfold grid
        by_cases h1 : k + 1 ≤ 4338
        · simp only [hk, h1, ↓reduceIte]
          exact Nat.pow_le_pow_left (by omega) 2
        · have hk' : k = 4338 := by omega
          subst hk'
          simp only [h1, ↓reduceIte, le_refl]
          rw [hQ]
          norm_num
      · intro p hp hle
        have hpQ : p < PartV.Q3 := by
          have := indexPrimes_mono (t' := PartV.Q3) (show grid (k + 1) ≤ PartV.Q3 by
            unfold grid
            by_cases h1 : k + 1 ≤ 4338
            · simp only [h1, ↓reduceIte]
              rw [hQ]
              have : (128 + (k + 1)) ^ 2 ≤ 4466 ^ 2 := Nat.pow_le_pow_left (by omega) 2
              omega
            · simp only [h1, ↓reduceIte, le_refl]) hp
          exact mem_range.mp (mem_filter.mp this).1
        have hxk : grid k = (128 + k) ^ 2 := by unfold grid; simp only [hk, ↓reduceIte]
        rw [hxk] at hle
        have hle' : ((128 + k : ℕ) : ℝ) ^ 2 ≤ (p : ℝ) := by exact_mod_cast hle
        have hpQ' : (p : ℝ) ≤ 2 ^ 25 := by
          have : (p : ℝ) ≤ 19951586 := by
            have := hpQ
            rw [hQ] at this
            exact_mod_cast this.le
          linarith
        exact large_term_le (by omega) hle' hpQ')
    (by
      intro k hk
      have := hanti k hk
      simp only [hg, show 128 + (k + 1) = 129 + k by ring]
      have h1 : (gW (129 + k) : ℝ) ≤ gW (128 + k) := by exact_mod_cast this
      have h2 : (0 : ℝ) < FP := by rw [hF]; norm_num
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 h2.le) hbK)
    (mul_nonneg hbK (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    (by
      intro k hk
      have hx : grid (k + 1) = (128 + (k + 1)) ^ 2 := by
        have h1 : k + 1 ≤ 4338 := by omega
        unfold grid; simp only [h1, ↓reduceIte]
      rw [hx]
      have := Theta_le h (t := (128 + (k + 1)) ^ 2) (Nat.one_le_pow _ _ (by omega)) (by
        have : (128 + (k + 1)) ^ 2 ≤ 4466 ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega)
      simp only [hU]
      push_cast at this ⊢
      rw [Real.sqrt_sq (by positivity)] at this
      exact this)
    (by
      have hx : grid 0 = 4 * 4096 := by unfold grid; norm_num
      rw [hx]
      exact Theta_ge_small)
  -- the last cell and the inner sum
  have hx0 : grid 0 = 4 * 4096 := by unfold grid; norm_num
  have hxn : grid (4338 + 1) = PartV.Q3 := by unfold grid; norm_num
  rw [hx0, hxn] at habel
  have hQ3 : Theta PartV.Q3 ≤ 19951586 / 2 + c * 4467 := by
    have h1 := Theta_le h (t := PartV.Q3) (by rw [hQ]; norm_num) (by rw [hQ]; norm_num)
    have hQr : ((PartV.Q3 : ℕ) : ℝ) = 19951586 := by rw [hQ]; norm_num
    rw [hQr] at h1
    have hs : Real.sqrt (19951586 : ℝ) ≤ 4467 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have := mul_le_mul_of_nonneg_left hs hc
    linarith
  have hgn : g 4338 = bK * (4130484773707033 / 2 ^ 64) := by
    show bK * ((gW (128 + 4338) : ℝ) / FP) = _
    rw [show (128 + 4338 : ℕ) = 4466 from rfl, gW_4466, hF]
    norm_num
  have hg0 : g 0 = bK * (144123992244954158 / 2 ^ 64) := by
    show bK * ((gW (128 + 0) : ℝ) / FP) = _
    rw [show (128 + 0 : ℕ) = 128 from rfl, gW_128, hF]
    norm_num
  have hcast : ∀ (w : ℕ → ℕ) (k : ℕ), k < 4338 →
      (g k - g (k + 1)) * (w (129 + k) : ℝ) = bK / 2 ^ 64 * (abelTerm w k : ℝ) := by
    intro w k hk
    have := hanti k hk
    simp only [hg, abelTerm, show 128 + (k + 1) = 129 + k by ring, hF]
    push_cast [Nat.cast_sub this]
    ring
  have hinner : ∑ k ∈ range 4338, (g k - g (k + 1)) * U (k + 1) =
      bK / 2 ^ 64 * (80087994762344705953805 / 2 + c * 65598638960976287003) := by
    have e1 : ∀ k ∈ range 4338, (g k - g (k + 1)) * U (k + 1) =
        (bK / 2 ^ 64 * (abelTerm (fun s => s * s) k : ℝ)) / 2 +
          c * (bK / 2 ^ 64 * (abelTerm (fun s => s) k : ℝ)) := by
      intro k hk
      have hk' := mem_range.mp hk
      rw [← hcast (fun s => s * s) k hk', ← hcast (fun s => s) k hk']
      simp only [hU, show 128 + (k + 1) = 129 + k by ring]
      push_cast
      ring
    rw [sum_congr rfl e1, sum_add_distrib, ← sum_div, ← mul_sum, ← mul_sum, ← mul_sum,
      ← Nat.cast_sum, ← Nat.cast_sum, ← gridSum_eq, ← gridSum_eq, abel2_eq, abel1_eq]
    push_cast
    ring
  rw [hinner, hgn, hg0] at habel
  have hL : L₀ = 3024061 * 0.6931471803 / 256 := by rw [hL₀, hkL]
  rw [hL] at habel
  have hgn0 : 0 ≤ bK * (4130484773707033 / 2 ^ 64 : ℝ) := mul_nonneg hbK (by norm_num)
  have hlast := mul_le_mul_of_nonneg_left hQ3 hgn0
  have hsplit : Fsum PartV.Q3 = Fsum (4 * 4096) + (Fsum PartV.Q3 - Fsum (4 * 4096)) := by ring
  rw [hsplit]
  nlinarith

/-- **`log M_pad(K) ≤ Tbound c`**, i.e. `M_pad(K) ≤ e^{Tbound c}`, from `ThetaUpper c`
(`cert:index-moment` at `a₀`). -/
theorem paperRI_le_exp {c : ℝ} (hc : 0 ≤ c) (h : ThetaUpper c) :
    Sarkozy.PaperData.paperRI ≤ Real.exp (Tbound c) := by
  have hb : Param.Params.anchorDecay / 18 = bExp := by
    unfold Param.Params.anchorDecay bExp; norm_num
  have hQ : PartV.Q3 = 19951586 := rfl
  have ha0 : 0 ≤ Param.Params.anchorDecay := by unfold Param.Params.anchorDecay; norm_num
  have ha18 : Param.Params.anchorDecay < 18 := by unfold Param.Params.anchorDecay; norm_num
  set S := PartVLaws.indexPrimes PartV.Q3 with hS
  -- the `K`-factor
  have hK : ((blockScale : ℕ) : ℝ) ^ (Param.Params.anchorDecay / 36) ≤
      Real.exp (5049 * 0.6931471808 / 256 * (8896611739 / 10 ^ 13 / 36)) := by
    have hK0 : (0 : ℝ) < (blockScale : ℕ) := by unfold blockScale; norm_num
    rw [Real.rpow_def_of_pos hK0]
    apply Real.exp_le_exp.mpr
    have hlog := log_lt_of_pow_lt (n := blockScale) (k := 256) (N := 5049) (by unfold blockScale; norm_num)
      (by norm_num) (by unfold blockScale; decide +kernel)
    have hw : Param.Params.anchorDecay / 36 = 8896611739 / 10 ^ 13 / 36 := by
      unfold Param.Params.anchorDecay; norm_num
    rw [hw]
    push_cast at hlog
    have : (0 : ℝ) ≤ 8896611739 / 10 ^ 13 / 36 := by norm_num
    nlinarith
  -- the factor at `2`
  have htwo : PartVLaws.Ltwo 64 ((2 : ℝ) ^ (Param.Params.anchorDecay / 18)) ≤
      Real.exp ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) /
        (1 - 1 / 2 ^ 64)) := by
    rw [hb]
    obtain ⟨h1, -, h3⟩ := zpow_bounds (t := 2) (by norm_num) (by norm_num)
    have hl := Real.log_two_lt_d9
    have hbK : 0 ≤ bK := by unfold bK bExp; norm_num
    have hz : (2 : ℝ) ^ bExp ≤ 1 + eps2 := by
      unfold eps2
      nlinarith [mul_le_mul_of_nonneg_left hl.le hbK]
    have := Ltwo_sub_one_le h1 hz
    have := Real.add_one_le_exp ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) +
      2 / 2 ^ 64) / (1 - 1 / 2 ^ 64))
    linarith
  -- the odd factors
  have hodd : ∀ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (Param.Params.anchorDecay / 18)) ≤
      Real.exp (termA p + 1 / 10 ^ 29) := by
    intro p hp
    have hp3 := PartVLaws.three_le_of_mem_indexPrimes hp
    have hpQ : p < PartV.Q3 := mem_range.mp (mem_filter.mp hp).1
    have hpR : (p : ℝ) ≤ 2 ^ 25 := by
      have : (p : ℝ) ≤ 19951586 := by rw [hQ] at hpQ; exact_mod_cast hpQ.le
      linarith
    rw [hb]
    obtain ⟨h1, h2, -⟩ := zpow_bounds (t := (p : ℝ)) (by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith) hpR
    have := Lodd_sub_one_le hp3 h1 h2
    have := Real.add_one_le_exp (termA p + 1 / 10 ^ 29)
    unfold termA at *
    linarith
  have hodd0 : ∀ p ∈ S, 0 ≤ PartVLaws.Lodd p 64 ((p : ℝ) ^ (Param.Params.anchorDecay / 18)) :=
    fun p hp => le_trans zero_le_one
      (PartVLaws.one_le_Lodd (PartVLaws.three_le_of_mem_indexPrimes hp) (by norm_num) ha0 ha18)
  have hprod : ∏ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (Param.Params.anchorDecay / 18)) ≤
      Real.exp (∑ p ∈ S, (termA p + 1 / 10 ^ 29)) := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ hodd0 hodd
  -- the sum
  have hcard : (S.card : ℝ) ≤ 19951586 := by
    have : S.card ≤ 19951586 := by
      rw [hS]
      unfold PartVLaws.indexPrimes
      exact (card_filter_le _ _).trans (by rw [card_range, hQ])
    exact_mod_cast this
  have hsum : ∑ p ∈ S, (termA p + 1 / 10 ^ 29) ≤ Fsum PartV.Q3 + 19951586 * (1 / 10 ^ 29) := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    unfold Fsum
    rw [← hS]
    have : (S.card : ℝ) * (1 / 10 ^ 29) ≤ 19951586 * (1 / 10 ^ 29) :=
      mul_le_mul_of_nonneg_right hcard (by norm_num)
    linarith
  have hF := Fsum_Q3_le hc h
  -- assemble
  unfold Sarkozy.PaperData.paperRI PartVLaws.Mpad
  rw [← hS]
  have hL2 : 0 ≤ PartVLaws.Ltwo 64 ((2 : ℝ) ^ (Param.Params.anchorDecay / 18)) :=
    le_trans zero_le_one (PartVLaws.one_le_Ltwo (by norm_num) ha0 ha18)
  have hP0 : 0 ≤ ∏ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (Param.Params.anchorDecay / 18)) :=
    prod_nonneg hodd0
  calc ((blockScale : ℕ) : ℝ) ^ (Param.Params.anchorDecay / 36) *
        (PartVLaws.Ltwo 64 ((2 : ℝ) ^ (Param.Params.anchorDecay / 18)) *
          ∏ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (Param.Params.anchorDecay / 18)))
      ≤ Real.exp (5049 * 0.6931471808 / 256 * (8896611739 / 10 ^ 13 / 36)) *
        (Real.exp ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) /
          (1 - 1 / 2 ^ 64)) * Real.exp (∑ p ∈ S, (termA p + 1 / 10 ^ 29))) := by
        apply mul_le_mul hK (mul_le_mul htwo hprod hP0 (Real.exp_pos _).le)
          (mul_nonneg hL2 hP0) (Real.exp_pos _).le
    _ = Real.exp (5049 * 0.6931471808 / 256 * (8896611739 / 10 ^ 13 / 36) +
        ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) /
          (1 - 1 / 2 ^ 64) + ∑ p ∈ S, (termA p + 1 / 10 ^ 29))) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (Tbound c) := by
        apply Real.exp_le_exp.mpr
        unfold Tbound
        linarith

/-- `e^{0.22175} < 1.248260`. -/
theorem exp_22175_le : Real.exp (22175 / 100000) ≤ 1248260 / 1000000 := by
  have h := Real.exp_bound' (x := 22175 / 100000) (by norm_num) (by norm_num) (n := 10)
    (by norm_num)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `e^{0.22155} < 1.248010`. -/
theorem exp_22155_le : Real.exp (22155 / 100000) ≤ 1248010 / 1000000 := by
  have h := Real.exp_bound' (x := 22155 / 100000) (by norm_num) (by norm_num) (n := 10)
    (by norm_num)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- **`cert:index-moment` at `a₀` under H2″** (`Target.ThetaSmall`, Ramaré–Rumely Thm 2 /
BMOR Thm 1.9): `M_pad(K) ≤ 1.248260`. -/
theorem paperRI_le_of_thetaSmall (h : Target.ThetaSmall) :
    Sarkozy.PaperData.paperRI ≤ 1248260 / 1000000 := by
  refine (paperRI_le_exp (by norm_num) (thetaUpper_of_thetaSmall h)).trans ?_
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_22175_le
  unfold Tbound eps2 bK bExp
  norm_num

/-- **`cert:index-moment` at `a₀` under H2′** (`Target.ThetaSmallTable`, the table entry):
`M_pad(K) ≤ 1.248010`. -/
theorem paperRI_le_of_thetaSmallTable (h : Target.ThetaSmallTable) :
    Sarkozy.PaperData.paperRI ≤ 1248010 / 1000000 := by
  refine (paperRI_le_exp (by norm_num) (thetaUpper_of_thetaSmallTable h)).trans ?_
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_22155_le
  unfold Tbound eps2 bK bExp
  norm_num

/-- **The field `hR` of `MainAnchor.PaperObligations`** (`cert:index-moment`, family F2), from
`Target.ThetaSmall` (H2″) alone: `paperRI ≤ anchorLedger.R_I = 1.248422835484`. -/
theorem paperRI_le_anchorLedger (h : Target.ThetaSmall) :
    Sarkozy.PaperData.paperRI ≤ LedgerAnchor.anchorLedger.R_I := by
  refine (paperRI_le_of_thetaSmall h).trans ?_
  show (1248260 / 1000000 : ℝ) ≤ 1.248422835484
  norm_num

/-- **The field `hR` from H2′ instead** (`Target.ThetaSmallTable`, the table entry):
`paperRI ≤ 1.248010 ≤ anchorLedger.R_I`. -/
theorem paperRI_le_anchorLedger_of_table (h : Target.ThetaSmallTable) :
    Sarkozy.PaperData.paperRI ≤ LedgerAnchor.anchorLedger.R_I := by
  refine (paperRI_le_of_thetaSmallTable h).trans ?_
  show (1248010 / 1000000 : ℝ) ≤ 1.248422835484
  norm_num

end Sarkozy.IndexCert
