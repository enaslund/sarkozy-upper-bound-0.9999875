module

public import Sarkozy.IndexCert.Moment
public import Sarkozy.MainTarget.IndexLaw
public import Sarkozy.TargetLedger.Numerics
public import Sarkozy.TargetLedger.Exponent

@[expose] public section

/-!
# `cert:index-moment` at the ledger's exponent: the conductor moment is below the ledger's `R_I`

`paper/sections/27_tail_index.tex`, `cert:index-moment` and `prop:imp:padic-price`, at the
ledger's exponent, since RG's rebase (7 November 2026) `a_G = 71/10⁵` (`TargetLedger.targetDecay`;
the names `bExpT`, `termAT`, `TboundT` keep the subscript `T`; it was
`a_T = 212956239/250000000000`),
`K = 863660`, `Q₃ = 19951586`, `m = 64`. The
headline is **`paperRIAt_le_targetLedger`**: H2″ in Ramaré–Rumely's Theorem 5.2.1 form
(`Target.ThetaSmallRR`, constant `1.174`) gives
`M_pad(K) at a_G ≤ TargetLedger.targetLedger.R_I = 1.193909842518`.

**The route: CERT1's certificate at `a₀`, rescaled.** CERT1 (`Sarkozy.IndexCert.Moment`) bounds
`log M_pad(K)` at `a₀` by `K`-factor + factor at `2` + `∑_{p<Q₃} A(p)` + `Q₃·10⁻²⁹`, with
`A(t) = (t^{b₀} − 1)√t/(t − t^{b₀})`, `b₀ = a₀/18`, and bounds `∑ A(p) = Fsum Q₃` by a
kernel-checked computation (`Fsum_Q3_le`, explicit in the constant `c` of `ThetaUpper c`). At
`a_G` the same decomposition holds with `b_T = a_G/18` (`paperRIAt_le_exp`), and:
* `A_T(t) ≤ λ A(t)` with `λ = a_G/a₀ = b_T/b₀` for `3 ≤ t ≤ 2^{25}` (`termAT_le`): by convexity
  of `exp`, `t^{λb₀} − 1 ≤ λ(t^{b₀} − 1)` (`rpow_mul_sub_one_le`), and `t − t^{b_T} ≥ t − t^{b₀}`;
  so CERT1's kernel computation is reused unchanged, at no kernel cost;
* the factor at `2` is bounded as at `a₀` (`2^{b_T} ≤ 2^{b₀} ≤ 1 + ε₂`), a loss of about `2·10⁻⁶`;
* the `K`-factor is `K^{a_G/36}`.

With `c = 1.174` the bound is `log M_pad(K) ≤ 0.1768110 < 0.17682` at `a_G` (`λ = a_G/a₀`), and
`e^{0.17682} ≤ 1.1935 ≤ 1.193909842518`: a margin of about `4.1·10⁻⁴` in `log R_I`. (At `a_T`
it was `0.2121179`, with margin `3.8·10⁻⁴`. The ledger's `R_I` is R4's F2 estimate with `1.174`,
`P₀ = 2¹⁶`, ratio-1.01 grid; CERT1's finer grid loses less.)
-/

namespace Sarkozy.MainTarget

open Finset Real
open Sarkozy.IndexCert (termA Fsum Fsum_Q3_le bExp bK Zhat eps2 ThetaUpper zpow_bounds
  Lodd_sub_one_le Ltwo_sub_one_le log_lt_of_pow_lt)
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-! ## The scaling of the terms -/

/-- **Convexity of `exp`**: for `t ≥ 1` and `0 ≤ λ ≤ 1`, `t^{λb} − 1 ≤ λ (t^b − 1)`. -/
theorem rpow_mul_sub_one_le {t b lam : ℝ} (ht : 1 ≤ t) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) : t ^ (lam * b) - 1 ≤ lam * (t ^ b - 1) := by
  have ht0 : 0 < t := by linarith
  rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0]
  have h := convexOn_exp.2 (Set.mem_univ (Real.log t * b)) (Set.mem_univ 0) hl0
    (by linarith : 0 ≤ 1 - lam) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have e1 : Real.log t * (lam * b) = lam * (Real.log t * b) := by ring
  rw [e1]
  linarith

/-- `b_T = a_G/18`. -/
noncomputable def bExpT : ℝ := targetDecay / 18

/-- `λ = a_G/a₀ = b_T/b₀ ≈ 0.79806` (the ledger's exponent `a_G = 71/10⁵`; it was `a_T`). -/
noncomputable def lamT : ℝ := (71 / 100000) / (8896611739 / 10 ^ 13)

theorem bExpT_eq : bExpT = lamT * bExp := by
  unfold bExpT lamT bExp targetDecay
  norm_num

theorem lamT_nonneg : 0 ≤ lamT := by unfold lamT; norm_num

theorem lamT_le_one : lamT ≤ 1 := by unfold lamT; norm_num

/-- The term `A_T(t) = (t^{b_T} − 1)√t/(t − t^{b_T})` at `a_G`. -/
noncomputable def termAT (t : ℝ) : ℝ := (t ^ bExpT - 1) * Real.sqrt t / (t - t ^ bExpT)

/-- `1 ≤ t^{b_T} ≤ t^{b₀} ≤ Ẑ` for `1 ≤ t ≤ 2^{25}`. -/
theorem zpowT_bounds {t : ℝ} (ht1 : 1 ≤ t) (ht : t ≤ 2 ^ 25) :
    1 ≤ t ^ bExpT ∧ t ^ bExpT ≤ t ^ bExp ∧ t ^ bExp ≤ Zhat := by
  have hb0 : 0 ≤ bExp := by unfold bExp; norm_num
  have hbT0 : 0 ≤ bExpT := by unfold bExpT targetDecay; norm_num
  have hle : bExpT ≤ bExp := by
    rw [bExpT_eq]
    have := mul_le_mul_of_nonneg_right lamT_le_one hb0
    linarith
  exact ⟨Real.one_le_rpow ht1 hbT0, Real.rpow_le_rpow_of_exponent_le ht1 hle,
    (zpow_bounds ht1 ht).2.1⟩

/-- **`A_T(t) ≤ λ A(t)`** for `3 ≤ t ≤ 2^{25}`: the terms at `a_G` are the terms at `a₀` scaled
by at most `λ = a_G/a₀`. -/
theorem termAT_le {t : ℝ} (ht3 : 3 ≤ t) (ht : t ≤ 2 ^ 25) : termAT t ≤ lamT * termA t := by
  obtain ⟨h1, h2, h3⟩ := zpowT_bounds (by linarith) ht
  have hZ : Zhat ≤ 2 := by unfold Zhat; norm_num
  have hb0 : 0 ≤ bExp := by unfold bExp; norm_num
  have hnum : t ^ bExpT - 1 ≤ lamT * (t ^ bExp - 1) := by
    rw [bExpT_eq]
    exact rpow_mul_sub_one_le (by linarith) lamT_nonneg lamT_le_one
  have hnum0 : 0 ≤ t ^ bExpT - 1 := by linarith
  have hden : t - t ^ bExp ≤ t - t ^ bExpT := by linarith
  have hden0 : 0 < t - t ^ bExp := by linarith
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  unfold termAT termA
  calc (t ^ bExpT - 1) * Real.sqrt t / (t - t ^ bExpT)
      ≤ (t ^ bExpT - 1) * Real.sqrt t / (t - t ^ bExp) :=
        div_le_div_of_nonneg_left (mul_nonneg hnum0 hs) hden0 hden
    _ ≤ lamT * (t ^ bExp - 1) * Real.sqrt t / (t - t ^ bExp) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum hs) hden0.le
    _ = lamT * ((t ^ bExp - 1) * Real.sqrt t / (t - t ^ bExp)) := by ring

/-! ## The bound on `log M_pad(K)` at `a_G` -/

/-- **The bound on `log M_pad(K)` at `a_G`**, explicit in the constant `c` of `ThetaUpper c`: the
`K`-factor at `a_G`, CERT1's factor at `2`, `λ` times CERT1's bound on `∑ A(p)`, and the
conditioning errors. -/
noncomputable def TboundT (c : ℝ) : ℝ :=
  5049 * 0.6931471808 / 256 * (71 / 100000 / 36) +
  (eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) / (1 - 1 / 2 ^ 64) +
  lamT * (bK * (0.6931471808 / 256) * (861202739404713745892444 / 2 ^ 64) +
    bK / 2 ^ 64 * (4130484773707033 * (19951586 / 2 + 4467 * c) -
      144123992244954158 * (3024061 * 0.6931471803 / 256) +
      80087994762344705953805 / 2 + c * 65598638960976287003)) +
  19951586 * (1 / 10 ^ 29)

/-- **`log M_pad(K) ≤ TboundT c` at `a_G`**, i.e. `M_pad(K) ≤ e^{TboundT c}`, from
`ThetaUpper c` (`cert:index-moment` at `a_G`). CERT1's `paperRI_le_exp` with the exponent
`a_G` and the terms rescaled by `termAT_le`. -/
theorem paperRIAt_le_exp {c : ℝ} (hc : 0 ≤ c) (h : ThetaUpper c) :
    paperRIAt targetDecay ≤ Real.exp (TboundT c) := by
  have hb : targetDecay / 18 = bExpT := rfl
  have hQ : PartV.Q3 = 19951586 := rfl
  have ha0 : 0 ≤ targetDecay := by unfold targetDecay; norm_num
  have ha18 : targetDecay < 18 := by unfold targetDecay; norm_num
  set S := PartVLaws.indexPrimes PartV.Q3 with hS
  -- the `K`-factor
  have hK : ((blockScale : ℕ) : ℝ) ^ (targetDecay / 36) ≤
      Real.exp (5049 * 0.6931471808 / 256 * (71 / 100000 / 36)) := by
    have hK0 : (0 : ℝ) < (blockScale : ℕ) := by unfold blockScale; norm_num
    rw [Real.rpow_def_of_pos hK0]
    apply Real.exp_le_exp.mpr
    have hlog := log_lt_of_pow_lt (n := blockScale) (k := 256) (N := 5049)
      (by unfold blockScale; norm_num) (by norm_num) (by unfold blockScale; decide +kernel)
    have hw : targetDecay / 36 = 71 / 100000 / 36 := by
      unfold targetDecay; norm_num
    rw [hw]
    push_cast at hlog
    have : (0 : ℝ) ≤ 71 / 100000 / 36 := by norm_num
    nlinarith
  -- the factor at `2`
  have htwo : PartVLaws.Ltwo 64 ((2 : ℝ) ^ (targetDecay / 18)) ≤
      Real.exp ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) /
        (1 - 1 / 2 ^ 64)) := by
    rw [hb]
    obtain ⟨h1, h2, -⟩ := zpowT_bounds (t := 2) (by norm_num) (by norm_num)
    obtain ⟨-, -, h3⟩ := zpow_bounds (t := 2) (by norm_num) (by norm_num)
    have hl := Real.log_two_lt_d9
    have hbK : 0 ≤ bK := by unfold bK bExp; norm_num
    have hz : (2 : ℝ) ^ bExp ≤ 1 + eps2 := by
      unfold eps2
      nlinarith [mul_le_mul_of_nonneg_left hl.le hbK]
    have := Ltwo_sub_one_le h1 (h2.trans hz)
    have := Real.add_one_le_exp ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) +
      2 / 2 ^ 64) / (1 - 1 / 2 ^ 64))
    linarith
  -- the odd factors
  have hodd : ∀ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (targetDecay / 18)) ≤
      Real.exp (termAT p + 1 / 10 ^ 29) := by
    intro p hp
    have hp3 := PartVLaws.three_le_of_mem_indexPrimes hp
    have hpQ : p < PartV.Q3 := mem_range.mp (mem_filter.mp hp).1
    have hpR : (p : ℝ) ≤ 2 ^ 25 := by
      have : (p : ℝ) ≤ 19951586 := by rw [hQ] at hpQ; exact_mod_cast hpQ.le
      linarith
    rw [hb]
    obtain ⟨h1, h2, h3⟩ := zpowT_bounds (t := (p : ℝ)) (by
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith) hpR
    have := Lodd_sub_one_le hp3 h1 (h2.trans h3)
    have := Real.add_one_le_exp (termAT p + 1 / 10 ^ 29)
    unfold termAT at *
    linarith
  have hodd0 : ∀ p ∈ S, 0 ≤ PartVLaws.Lodd p 64 ((p : ℝ) ^ (targetDecay / 18)) :=
    fun p hp => le_trans zero_le_one
      (PartVLaws.one_le_Lodd (PartVLaws.three_le_of_mem_indexPrimes hp) (by norm_num) ha0 ha18)
  have hprod : ∏ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (targetDecay / 18)) ≤
      Real.exp (∑ p ∈ S, (termAT p + 1 / 10 ^ 29)) := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ hodd0 hodd
  -- the sum, rescaled
  have hcard : (S.card : ℝ) ≤ 19951586 := by
    have : S.card ≤ 19951586 := by
      rw [hS]
      unfold PartVLaws.indexPrimes
      exact (card_filter_le _ _).trans (by rw [card_range, hQ])
    exact_mod_cast this
  have hscale : ∑ p ∈ S, termAT p ≤ lamT * Fsum PartV.Q3 := by
    unfold Fsum
    rw [← hS, mul_sum]
    apply sum_le_sum
    intro p hp
    have hp3 := PartVLaws.three_le_of_mem_indexPrimes hp
    have hpQ : p < PartV.Q3 := mem_range.mp (mem_filter.mp hp).1
    have hpR : (p : ℝ) ≤ 2 ^ 25 := by
      have : (p : ℝ) ≤ 19951586 := by rw [hQ] at hpQ; exact_mod_cast hpQ.le
      linarith
    exact termAT_le (by exact_mod_cast hp3) hpR
  have hsum : ∑ p ∈ S, (termAT p + 1 / 10 ^ 29) ≤
      lamT * Fsum PartV.Q3 + 19951586 * (1 / 10 ^ 29) := by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    have : (S.card : ℝ) * (1 / 10 ^ 29) ≤ 19951586 * (1 / 10 ^ 29) :=
      mul_le_mul_of_nonneg_right hcard (by norm_num)
    linarith
  have hF := mul_le_mul_of_nonneg_left (Fsum_Q3_le hc h) lamT_nonneg
  -- assemble
  unfold paperRIAt PartVLaws.Mpad
  rw [← hS]
  have hL2 : 0 ≤ PartVLaws.Ltwo 64 ((2 : ℝ) ^ (targetDecay / 18)) :=
    le_trans zero_le_one (PartVLaws.one_le_Ltwo (by norm_num) ha0 ha18)
  have hP0 : 0 ≤ ∏ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (targetDecay / 18)) :=
    prod_nonneg hodd0
  calc ((blockScale : ℕ) : ℝ) ^ (targetDecay / 36) *
        (PartVLaws.Ltwo 64 ((2 : ℝ) ^ (targetDecay / 18)) *
          ∏ p ∈ S, PartVLaws.Lodd p 64 ((p : ℝ) ^ (targetDecay / 18)))
      ≤ Real.exp (5049 * 0.6931471808 / 256 * (71 / 100000 / 36)) *
        (Real.exp ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) /
          (1 - 1 / 2 ^ 64)) * Real.exp (∑ p ∈ S, (termAT p + 1 / 10 ^ 29))) := by
        apply mul_le_mul hK (mul_le_mul htwo hprod hP0 (Real.exp_pos _).le)
          (mul_nonneg hL2 hP0) (Real.exp_pos _).le
    _ = Real.exp (5049 * 0.6931471808 / 256 * (71 / 100000 / 36) +
        ((eps2 * (70710679 / 10 ^ 8 + (1 + eps2) / (1 - eps2)) + 2 / 2 ^ 64) /
          (1 - 1 / 2 ^ 64) + ∑ p ∈ S, (termAT p + 1 / 10 ^ 29))) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (TboundT c) := by
        apply Real.exp_le_exp.mpr
        unfold TboundT
        linarith

/-! ## The certificate under H2″ -/

/-- **H2″ in Theorem 5.2.1's form** (`Target.ThetaSmallRR`, constant `1.174`) gives
`ThetaUpper 1.174`. -/
theorem thetaUpper_of_thetaSmallRR (h : Target.ThetaSmallRR) : ThetaUpper (1174 / 1000) := by
  intro x h1 h2
  have := (abs_le.mp (h x h1 h2)).2
  linarith

/-- `e^{0.17682} < 1.1935`. -/
theorem exp_21212_le : Real.exp (17682 / 100000) ≤ 11935 / 10000 := by
  have h := Real.exp_bound' (x := 17682 / 100000) (by norm_num) (by norm_num) (n := 10)
    (by norm_num)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- **`cert:index-moment` at `a_G` under H2″** (`Target.ThetaSmallRR`, Ramaré–Rumely
Thm 5.2.1): `M_pad(K) ≤ 1.1935` at `a_G`. -/
theorem paperRIAt_le_of_thetaSmallRR (h : Target.ThetaSmallRR) :
    paperRIAt targetDecay ≤ 11935 / 10000 := by
  refine (paperRIAt_le_exp (by norm_num) (thetaUpper_of_thetaSmallRR h)).trans ?_
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_21212_le
  unfold TboundT lamT eps2 bK bExp
  norm_num

/-- **The index moment of the target ledger** (`cert:index-moment` at `a_G`, family F2), from
`Target.ThetaSmallRR` (H2″) alone: `M_pad(K) ≤ targetLedger.R_I = 1.193909842518` at `a_G`. This
is the `hR` of `MainTarget.main_target_paper_block_final_of_hR`. -/
theorem paperRIAt_le_targetLedger (h : Target.ThetaSmallRR) :
    paperRIAt targetDecay ≤ targetLedger.R_I := by
  refine (paperRIAt_le_of_thetaSmallRR h).trans ?_
  show (11935 / 10000 : ℝ) ≤ 1.193909842518
  norm_num

end Sarkozy.MainTarget
