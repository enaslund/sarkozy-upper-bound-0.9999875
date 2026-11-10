module

public import Sarkozy.Functional.FibreScale

@[expose] public section

/-!
# Scale conditions (`lem:scale-conditions`)

`lem:scale-conditions` of `paper/sections/08_scale_comparison.tex`, in two parts.

* The consequences (`scaleConsequences` and its components). For a selection
  `E` with `q_E ≤ N^τ`, a divisor `D₀ ∣ M₀` and an interval `I ∈ 𝓘_L`, with `R`,
  `n`, `λ` as in `lem:record:fibre-scale`(b), the conditions (ii)–(iv) give
  `R ≤ M₀² Q_cl N^{2τ}`, `H D_E ≤ Q`, `n₀ ≤ n ≤ N`, `n^β ≥ H`,
  `n ≥ 10 n^{6β}`, `1 ≤ λ ≤ 2` and `λ^{72} ≤ 1 + u_L`, and `u_L → 0`.
  These are proved for arbitrary exponents `β ≥ 0`, `τ` and arbitrary real
  `Q`, `H ≥ 0` (the paper takes `Q = N^β`, `H = N^{β/2}`); the full order of the
  selection is written `D_E = q_E c_E`, with `q_E` squarefree (the product of
  the selected primes with `e_p = 1`) and `c_E` a perfect square with
  `c_E ≤ Q_cl` (the product of the selected clique powers `p^{e_p}`, `e_p`
  even), `D₀` coprime to `D_E` and `q_E` coprime to `c_E`.
* The existence of the starting scale `L_*` (`exists_scaleThreshold`): for
  the paper's exact exponents `β = 1/20`, `τ = 1/201`, `t_an = 1/60`
  (`def:record:analytic-stage`) and any fixed `K ≥ 1`, `M₀ ≥ 1`, `Q_cl ≥ 1`,
  `Q_pre`, and thresholds `N₀`, `N₀'` (those of `prop:record:kernel20`, which
  are parameters here), conditions (i)–(vii) hold for all `L ≥ L_*`;
  `ScaleConditionsAt.consequences` and `scaleConditions_assembled` combine
  this with the consequences at `Q = N^β`, `H = N^{β/2}`.

`n` and `λ` are the objects of `FibreScale`: `n = K · stepScale K M R`,
`λ = R n / M`, with `M = |I|`.
-/

open Filter Topology

namespace Sarkozy.Functional

/-! ### The consequences -/

section Consequences

/-- The paper's `n₀ = N^{1−2τ}/(K M₀² Q_cl)` (`lem:scale-conditions`(iii)). -/
noncomputable def scaleN0 (K M0 Qcl : ℕ) (τ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 - 2 * τ) / ((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ))

/-- The paper's `u_L = (1 + K² M₀² Q_cl N^{2τ−1})^{72} − 1`, `N = KL`. -/
noncomputable def scaleU (K M0 Qcl : ℕ) (τ : ℝ) (L : ℕ) : ℝ :=
  (1 + (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) * ((K * L : ℕ) : ℝ) ^ (2 * τ - 1)) ^ 72 - 1

/-- `R = sq(D₀ q_E c_E) = sq(D₀) q_E² c_E` (second form of `eq:square-step`). -/
theorem leastSquare_selection {D0 qE cE : ℕ} (hqE : Squarefree qE) (hcE : IsSquare cE)
    (hcE0 : cE ≠ 0) (hcop0 : D0.Coprime (qE * cE)) (hcopE : qE.Coprime cE) :
    leastSquare (D0 * (qE * cE)) = leastSquare D0 * qE ^ 2 * cE := by
  rw [leastSquare_mul hcop0, leastSquare_mul hcopE, leastSquare_of_squarefree hqE,
    leastSquare_of_isSquare hcE0 hcE, mul_assoc]

/-- `lem:scale-conditions`, consequences: `R ≤ M₀² Q_cl N^{2τ}`. -/
theorem leastSquare_selection_le {N D0 M0 qE cE Qcl : ℕ} {τ : ℝ} (hD0 : D0 ∣ M0) (hM0 : 1 ≤ M0)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcop0 : D0.Coprime (qE * cE)) (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ (N : ℝ) ^ τ) :
    (leastSquare (D0 * (qE * cE)) : ℝ) ≤ (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ) := by
  rw [leastSquare_selection hqE hcE hcE0 hcop0 hcopE]
  have hD0pos : D0 ≠ 0 := by
    rintro rfl
    exact absurd (Nat.eq_zero_of_zero_dvd hD0) (by omega)
  have h1 : leastSquare D0 ≤ M0 ^ 2 :=
    (leastSquare_le_sq hD0pos).trans (Nat.pow_le_pow_left (Nat.le_of_dvd (by omega) hD0) 2)
  have h1' : (leastSquare D0 : ℝ) ≤ (M0 : ℝ) ^ 2 := by exact_mod_cast h1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h2 : ((qE : ℝ)) ^ 2 ≤ (N : ℝ) ^ (2 * τ) := by
    have hsq : ((N : ℝ) ^ τ) ^ 2 = (N : ℝ) ^ (2 * τ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
      congr 1
      push_cast
      ring
    rw [← hsq]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hqN 2
  have h3 : (cE : ℝ) ≤ Qcl := by exact_mod_cast hcQ
  push_cast
  calc (leastSquare D0 : ℝ) * (qE : ℝ) ^ 2 * cE
      ≤ (M0 : ℝ) ^ 2 * (N : ℝ) ^ (2 * τ) * Qcl := by
        apply mul_le_mul (mul_le_mul h1' h2 (by positivity) (by positivity)) h3
          (by positivity) (by positivity)
    _ = _ := by ring

/-- `lem:scale-conditions`, consequences: `H D_E ≤ Q`, from (ii) `H Q_cl N^τ ≤ Q`. -/
theorem selection_order_le {N qE cE Qcl : ℕ} {τ Q H : ℝ} (hH : 0 ≤ H) (hcQ : cE ≤ Qcl)
    (hqN : (qE : ℝ) ≤ (N : ℝ) ^ τ) (hii : H * Qcl * (N : ℝ) ^ τ ≤ Q) :
    H * ((qE * cE : ℕ) : ℝ) ≤ Q := by
  have h3 : (cE : ℝ) ≤ Qcl := by exact_mod_cast hcQ
  have hD : ((qE * cE : ℕ) : ℝ) ≤ Qcl * (N : ℝ) ^ τ := by
    push_cast
    calc (qE : ℝ) * cE ≤ (N : ℝ) ^ τ * Qcl :=
          mul_le_mul hqN h3 (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by ring
  calc H * ((qE * cE : ℕ) : ℝ) ≤ H * (Qcl * (N : ℝ) ^ τ) := mul_le_mul_of_nonneg_left hD hH
    _ = H * Qcl * (N : ℝ) ^ τ := by ring
    _ ≤ Q := hii

/-- `n = K⌈M/(KR)⌉ ≤ N` when `M ≤ N = KL` and `R ≥ 1`. -/
theorem stepScale_mul_le {K L M R : ℕ} (hK : 1 ≤ K) (hR : 1 ≤ R) (hM : M ≤ K * L) :
    K * stepScale K M R ≤ K * L := by
  apply Nat.mul_le_mul_left
  unfold stepScale
  have hP : 0 < K * R := Nat.mul_pos (by omega) (by omega)
  apply Nat.lt_succ_iff.mp
  apply (Nat.div_lt_iff_lt_mul hP).mpr
  have h1 : K * L ≤ K * R * L := by
    calc K * L = K * 1 * L := by ring
      _ ≤ K * R * L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left K hR)
  have h2 : (L + 1) * (K * R) = K * R * L + K * R := by ring
  rw [Nat.succ_eq_add_one, h2]
  omega

/-- `n₀ = L / (M₀² Q_cl N^{2τ})` for `N = KL`. -/
theorem scaleN0_eq {K L N M0 Qcl : ℕ} {τ : ℝ} (hK : 1 ≤ K) (hM0 : 1 ≤ M0) (hQ : 1 ≤ Qcl)
    (hN : N = K * L) (hNpos : 0 < N) :
    scaleN0 K M0 Qcl τ N = (L : ℝ) / ((M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hM0' : (M0 : ℝ) ≠ 0 := by exact_mod_cast (show M0 ≠ 0 by omega)
  have hQ' : (Qcl : ℝ) ≠ 0 := by exact_mod_cast (show Qcl ≠ 0 by omega)
  have hpos : (N : ℝ) ^ (2 * τ) ≠ 0 := (Real.rpow_pos_of_pos hN' _).ne'
  have hNKL : (N : ℝ) = K * L := by rw [hN]; push_cast; ring
  unfold scaleN0
  rw [Real.rpow_sub hN', Real.rpow_one]
  generalize (N : ℝ) ^ (2 * τ) = P at hpos ⊢
  rw [hNKL]
  field_simp

/-- `lem:scale-conditions`, consequences. Let `N = KL`, `|I| = M ∈ {N, L}`,
`D₀ ∣ M₀`, `D_E = q_E c_E` as in the module docstring with `q_E ≤ N^τ`,
`R = sq(D₀ D_E)`, `n = K⌈M/(KR)⌉` and `λ = Rn/M`. Under (ii)
`H Q_cl N^τ ≤ Q`, (iii) `n₀^β ≥ H`, `n₀ ≥ 10 N^{6β}` and (iv)
`K² M₀² Q_cl N^{2τ−1} ≤ 1`:
`R ≤ M₀² Q_cl N^{2τ}`, `H D_E ≤ Q`, `n₀ ≤ n ≤ N`, `n^β ≥ H`, `n ≥ 10 n^{6β}`,
`1 ≤ λ ≤ 2` and `λ^{72} ≤ 1 + u_L`. -/
theorem scaleConsequences {K L N M D0 M0 qE cE Qcl : ℕ} {β τ Q H : ℝ}
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hN : N = K * L) (hM : M = N ∨ M = L)
    (hD0 : D0 ∣ M0) (hM0 : 1 ≤ M0)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcop0 : D0.Coprime (qE * cE)) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ (N : ℝ) ^ τ) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hii : H * Qcl * (N : ℝ) ^ τ ≤ Q)
    (hiii : H ≤ scaleN0 K M0 Qcl τ N ^ β ∧ 10 * (N : ℝ) ^ (6 * β) ≤ scaleN0 K M0 Qcl τ N)
    (hiv : (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ - 1) ≤ 1) :
    let R := leastSquare (D0 * (qE * cE))
    let n := K * stepScale K M R
    (R : ℝ) ≤ (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ) ∧
      H * ((qE * cE : ℕ) : ℝ) ≤ Q ∧
      (scaleN0 K M0 Qcl τ N ≤ n ∧ n ≤ N) ∧
      H ≤ (n : ℝ) ^ β ∧
      10 * (n : ℝ) ^ (6 * β) ≤ n ∧
      (1 ≤ (R * n : ℝ) / M ∧ (R * n : ℝ) / M ≤ 2) ∧
      ((R * n : ℝ) / M) ^ 72 ≤ 1 + scaleU K M0 Qcl τ L := by
  intro R n
  have hNpos : 0 < N := by rw [hN]; exact Nat.mul_pos (by omega) (by omega)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hLN : L ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left L (by omega)
  have hMN : M ≤ N := by rcases hM with h | h <;> omega
  have hLM : L ≤ M := by rcases hM with h | h <;> omega
  have hM1 : 1 ≤ M := le_trans hL hLM
  have hQ1 : 1 ≤ Qcl := le_trans (Nat.one_le_iff_ne_zero.mpr hcE0) hcQ
  have hR1 : 1 ≤ R := leastSquare_pos _
  -- (c1) and (c2)
  have hc1 : (R : ℝ) ≤ (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ) :=
    leastSquare_selection_le hD0 hM0 hqE hcE hcE0 hcQ hcop0 hcopE hqN
  have hc2 : H * ((qE * cE : ℕ) : ℝ) ≤ Q := selection_order_le hH hcQ hqN hii
  -- the bounds `M ≤ R n < M + K R`
  obtain ⟨hb1, hb2⟩ := stepScale_bounds (M := M) hK hR1
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hRn : (M : ℝ) ≤ R * n := by exact_mod_cast hb1
  -- (c3)
  have hn0 : scaleN0 K M0 Qcl τ N ≤ n := by
    rw [scaleN0_eq hK hM0 hQ1 hN hNpos]
    have hden : (0 : ℝ) < (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ) := lt_of_lt_of_le hRpos hc1
    calc (L : ℝ) / ((M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ)) ≤ (L : ℝ) / R :=
          div_le_div_of_nonneg_left hLpos.le hRpos hc1
      _ ≤ (M : ℝ) / R := div_le_div_of_nonneg_right (by exact_mod_cast hLM) hRpos.le
      _ ≤ n := by rw [div_le_iff₀ hRpos]; linarith
  have hnN : n ≤ N := by
    have := stepScale_mul_le (L := L) hK hR1 (show M ≤ K * L by omega)
    rw [hN]; exact this
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hn0nonneg : 0 ≤ scaleN0 K M0 Qcl τ N := by
    unfold scaleN0
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  -- (c4) and (c5)
  have hc4 : H ≤ (n : ℝ) ^ β := hiii.1.trans (Real.rpow_le_rpow hn0nonneg hn0 hβ)
  have hc5 : 10 * (n : ℝ) ^ (6 * β) ≤ n := by
    have h6 : (n : ℝ) ^ (6 * β) ≤ (N : ℝ) ^ (6 * β) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hnN' (by linarith)
    linarith [hiii.2]
  -- (c6) and (c7)
  have hlam := stepScale_lambda (M := M) hK hR1 hM1
  have hlam1 : 1 ≤ (R * n : ℝ) / M := by
    have := hlam.1
    simp only [n]
    push_cast at this ⊢
    exact this
  have hlam2 : (R * n : ℝ) / M < 1 + (K * R : ℝ) / M := by
    have := hlam.2.1
    simp only [n]
    push_cast at this ⊢
    exact this
  set x : ℝ := (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ - 1) with hx
  have hKRM : (K * R : ℝ) / M ≤ x := by
    have hNKL : (N : ℝ) = K * L := by rw [hN]; push_cast; ring
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    calc (K * R : ℝ) / M ≤ (K * R : ℝ) / L :=
          div_le_div_of_nonneg_left (by positivity) hLpos (by exact_mod_cast hLM)
      _ = (K : ℝ) ^ 2 * R / N := by rw [hNKL]; field_simp
      _ ≤ (K : ℝ) ^ 2 * ((M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * τ)) / N := by
          apply div_le_div_of_nonneg_right _ hN'.le
          exact mul_le_mul_of_nonneg_left hc1 (by positivity)
      _ = x := by
          rw [hx, Real.rpow_sub_one hN'.ne']
          ring
  have hlam_le : (R * n : ℝ) / M ≤ 1 + x := by linarith
  have hc7 : ((R * n : ℝ) / M) ^ 72 ≤ 1 + scaleU K M0 Qcl τ L := by
    have h1 : 1 + scaleU K M0 Qcl τ L = (1 + x) ^ 72 := by
      unfold scaleU
      rw [hx, ← hN]
      ring
    rw [h1]
    exact pow_le_pow_left₀ (by linarith) hlam_le 72
  exact ⟨hc1, hc2, ⟨hn0, hnN⟩, hc4, hc5, ⟨hlam1, by linarith⟩, hc7⟩

/-- `lem:scale-conditions`: `u_L → 0` as `L → ∞`, since `2τ − 1 < 0`. -/
theorem tendsto_scaleU {K M0 Qcl : ℕ} {τ : ℝ} (hK : 1 ≤ K) (hτ : τ < 1 / 2) :
    Tendsto (scaleU K M0 Qcl τ) atTop (𝓝 0) := by
  have hNlim : Tendsto (fun L : ℕ => ((K * L : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro L
    have : L ≤ K * L := Nat.le_mul_of_pos_left L (by omega)
    exact_mod_cast this
  have hpow : Tendsto (fun L : ℕ => ((K * L : ℕ) : ℝ) ^ (2 * τ - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - 2 * τ by linarith)).comp hNlim
    have he : (fun L : ℕ => ((K * L : ℕ) : ℝ) ^ (2 * τ - 1)) =
        (fun x : ℝ => x ^ (-(1 - 2 * τ))) ∘ (fun L : ℕ => ((K * L : ℕ) : ℝ)) := by
      funext L
      simp only [Function.comp_apply, neg_sub]
    rw [he]
    exact h
  have h := ((hpow.const_mul ((K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ))).const_add 1).pow 72
  have h' := h.sub_const 1
  simp only [mul_zero, add_zero, one_pow, sub_self] at h'
  exact h'

end Consequences

/-! ### The starting scale `L_*` -/

section Threshold

/-- `β = 1/20` (`def:record:analytic-stage`). -/
noncomputable def stageBeta : ℝ := 1 / 20

/-- `τ = 1/201` (`def:record:analytic-stage`). -/
noncomputable def stageTau : ℝ := 1 / 201

/-- `t_an = 1/60` (`def:record:analytic-stage`). -/
noncomputable def stageTan : ℝ := 1 / 60

/-- The four inequalities (S5) of the analytic stage, in the paper's order:
`1 − 2τ − 6β > 0`, `β/2 − τ > 0`, `β/2 − t_an > 0`, `β(1 − 2τ) − β/2 > 0`. -/
theorem stage_S5 :
    0 < 1 - 2 * stageTau - 6 * stageBeta ∧ 0 < stageBeta / 2 - stageTau ∧
      0 < stageBeta / 2 - stageTan ∧ 0 < stageBeta * (1 - 2 * stageTau) - stageBeta / 2 := by
  norm_num [stageBeta, stageTau, stageTan]

/-- Conditions (i)–(vii) of `lem:scale-conditions` at the scale `L`, with
`N = KL`, `Q = N^β`, `H = N^{β/2}`, `T₀ = N^{t_an}`, `P₅ = 2^{65536}`; the
thresholds `N₀`, `N₀'` of `prop:record:kernel20` are parameters. -/
structure ScaleConditionsAt (K M0 Qcl Qpre N0 N0' L : ℕ) : Prop where
  /-- (i) `L ≥ 10 N^{6β}`. -/
  cond_i : 10 * ((K * L : ℕ) : ℝ) ^ (6 * stageBeta) ≤ L
  /-- (ii) `H Q_cl N^τ ≤ Q`. -/
  cond_ii : ((K * L : ℕ) : ℝ) ^ (stageBeta / 2) * Qcl * ((K * L : ℕ) : ℝ) ^ stageTau ≤
    ((K * L : ℕ) : ℝ) ^ stageBeta
  /-- (iii) `n₀^β ≥ H`. -/
  cond_iii_root : ((K * L : ℕ) : ℝ) ^ (stageBeta / 2) ≤
    scaleN0 K M0 Qcl stageTau (K * L) ^ stageBeta
  /-- (iii) `n₀ ≥ 10 N^{6β}`. -/
  cond_iii_size : 10 * ((K * L : ℕ) : ℝ) ^ (6 * stageBeta) ≤ scaleN0 K M0 Qcl stageTau (K * L)
  /-- (iv) `K² M₀² Q_cl N^{2τ−1} ≤ 1`. -/
  cond_iv : (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * Qcl * ((K * L : ℕ) : ℝ) ^ (2 * stageTau - 1) ≤ 1
  /-- (v) `N^β ≥ P₅`. -/
  cond_v : (2 : ℝ) ^ (65536 : ℕ) ≤ ((K * L : ℕ) : ℝ) ^ stageBeta
  /-- (vi) `H Q_pre T₀ ≤ Q`. -/
  cond_vi_cutoff : ((K * L : ℕ) : ℝ) ^ (stageBeta / 2) * Qpre * ((K * L : ℕ) : ℝ) ^ stageTan ≤
    ((K * L : ℕ) : ℝ) ^ stageBeta
  /-- (vi) `M₀ Q_pre T₀ ≤ min(N^{1/20}, L)`. -/
  cond_vi_min : (M0 : ℝ) * Qpre * ((K * L : ℕ) : ℝ) ^ stageTan ≤
    min (((K * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20)) L
  /-- (vii) `N ≥ N₀` and `N ≥ N₀'`. -/
  cond_vii : N0 ≤ K * L ∧ N0' ≤ K * L

/-- (v) gives what the paper uses it for: every prime below `P₅` is at most
the cutoff `N^β`, hence a coordinate of `G_N` when it is at least `P₄`. -/
theorem ScaleConditionsAt.le_cutoff {K M0 Qcl Qpre N0 N0' L : ℕ}
    (h : ScaleConditionsAt K M0 Qcl Qpre N0 N0' L) {p : ℕ} (hp : p < 2 ^ 65536) :
    (p : ℝ) ≤ ((K * L : ℕ) : ℝ) ^ stageBeta := by
  have : (p : ℝ) < (2 : ℝ) ^ (65536 : ℕ) := by exact_mod_cast hp
  exact this.le.trans h.cond_v

/-- `C ≤ x^a` for all large `x`, when `a > 0`. -/
theorem scale_eventually_le_rpow (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, C ≤ x ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop C

/-- `C x^a ≤ x^b` for all large `x`, when `a < b`. -/
theorem scale_eventually_mul_rpow_le (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ x ^ b := by
  filter_upwards [scale_eventually_le_rpow C (sub_pos.mpr hab), eventually_gt_atTop 0]
    with x hx hx0
  calc C * x ^ a ≤ x ^ (b - a) * x ^ a := mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le a)
    _ = x ^ b := by rw [← Real.rpow_add hx0]; ring_nf

theorem tendsto_scaleN {K : ℕ} (hK : 1 ≤ K) :
    Tendsto (fun L : ℕ => ((K * L : ℕ) : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
  intro L
  have : L ≤ K * L := Nat.le_mul_of_pos_left L (by omega)
  exact_mod_cast this

/-- `lem:scale-conditions`: there is `L_* ≥ 2`, depending only on the analytic
stage, `K`, `M₀`, `Q_cl`, `Q_pre` and the kernel thresholds, such that
(i)–(vii) hold for every `L ≥ L_*`. -/
theorem exists_scaleThreshold (K M0 Qcl Qpre N0 N0' : ℕ) (hK : 1 ≤ K) (hM0 : 1 ≤ M0)
    (hQcl : 1 ≤ Qcl) :
    ∃ Lstar : ℕ, 2 ≤ Lstar ∧ ∀ L, Lstar ≤ L → ScaleConditionsAt K M0 Qcl Qpre N0 N0' L := by
  obtain ⟨hS1, hS2, hS3, hS4⟩ := stage_S5
  have hb : 0 < stageBeta := by norm_num [stageBeta]
  have hf := tendsto_scaleN hK
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hc0 : 0 < (K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ) := by
    have : (0 : ℝ) < M0 := by exact_mod_cast hM0
    have : (0 : ℝ) < Qcl := by exact_mod_cast hQcl
    positivity
  have hcb : 0 < ((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ)) ^ stageBeta := Real.rpow_pos_of_pos hc0 _
  have hNL : ∀ L : ℕ, ((K * L : ℕ) : ℝ) = (K : ℝ) * L := fun L => by push_cast; ring
  -- the eventual inequalities, as functions of `x = N`
  have e0 := hf.eventually (eventually_gt_atTop (0 : ℝ))
  have e1 := hf.eventually (scale_eventually_mul_rpow_le (10 * K) (a := 6 * stageBeta) (b := 1)
    (by norm_num [stageBeta]))
  have e2 := hf.eventually (scale_eventually_mul_rpow_le (Qcl : ℝ)
    (a := stageBeta / 2 + stageTau) (b := stageBeta) (by linarith))
  have e3 := hf.eventually (scale_eventually_mul_rpow_le
    (((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ)) ^ stageBeta)
    (a := stageBeta / 2) (b := (1 - 2 * stageTau) * stageBeta) (by nlinarith))
  have e4 := hf.eventually (scale_eventually_mul_rpow_le (10 * ((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ)))
    (a := 6 * stageBeta) (b := 1 - 2 * stageTau) (by linarith))
  have e5 := hf.eventually (scale_eventually_le_rpow ((K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * Qcl)
    (a := 1 - 2 * stageTau) (by linarith))
  have e6 := hf.eventually (scale_eventually_le_rpow ((2 : ℝ) ^ (65536 : ℕ)) hb)
  have e7 := hf.eventually (scale_eventually_mul_rpow_le (Qpre : ℝ)
    (a := stageBeta / 2 + stageTan) (b := stageBeta) (by linarith))
  have e8 := hf.eventually (scale_eventually_mul_rpow_le ((M0 : ℝ) * Qpre)
    (a := stageTan) (b := 1 / 20) (by norm_num [stageTan]))
  have e9 := hf.eventually (scale_eventually_mul_rpow_le ((K : ℝ) * M0 * Qpre)
    (a := stageTan) (b := 1) (by norm_num [stageTan]))
  have e10 : ∀ᶠ L : ℕ in atTop, N0 ≤ K * L ∧ N0' ≤ K * L := by
    filter_upwards [eventually_ge_atTop (max N0 N0')] with L hL
    have : L ≤ K * L := Nat.le_mul_of_pos_left L (by omega)
    constructor <;> omega
  have hall : ∀ᶠ L : ℕ in atTop, ScaleConditionsAt K M0 Qcl Qpre N0 N0' L := by
    filter_upwards [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      with L h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    set x : ℝ := ((K * L : ℕ) : ℝ) with hx
    have hxL : x = (K : ℝ) * L := hNL L
    refine ⟨?_, ?_, ?_, ?_, ?_, h6, ?_, ?_, h10⟩
    · -- (i)
      rw [Real.rpow_one] at h1
      have : 10 * x ^ (6 * stageBeta) * K ≤ L * K := by rw [hxL] at h1 ⊢; nlinarith
      exact le_of_mul_le_mul_right this hK'
    · -- (ii)
      calc x ^ (stageBeta / 2) * Qcl * x ^ stageTau = Qcl * x ^ (stageBeta / 2 + stageTau) := by
            rw [Real.rpow_add h0]; ring
        _ ≤ _ := h2
    · -- (iii), root
      unfold scaleN0
      rw [← hx, Real.div_rpow (Real.rpow_nonneg h0.le _) hc0.le, ← Real.rpow_mul h0.le,
        le_div_iff₀ hcb]
      calc x ^ (stageBeta / 2) * ((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ)) ^ stageBeta
          = ((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ)) ^ stageBeta * x ^ (stageBeta / 2) := by ring
        _ ≤ _ := h3
    · -- (iii), size
      unfold scaleN0
      rw [← hx, le_div_iff₀ hc0]
      calc 10 * x ^ (6 * stageBeta) * ((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ))
          = 10 * ((K : ℝ) * (M0 : ℝ) ^ 2 * (Qcl : ℝ)) * x ^ (6 * stageBeta) := by ring
        _ ≤ _ := h4
    · -- (iv)
      calc (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * Qcl * x ^ (2 * stageTau - 1)
          ≤ x ^ (1 - 2 * stageTau) * x ^ (2 * stageTau - 1) :=
            mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg h0.le _)
        _ = 1 := by rw [← Real.rpow_add h0]; ring_nf; exact Real.rpow_zero x
    · -- (vi), cutoff
      calc x ^ (stageBeta / 2) * Qpre * x ^ stageTan = Qpre * x ^ (stageBeta / 2 + stageTan) := by
            rw [Real.rpow_add h0]; ring
        _ ≤ _ := h7
    · -- (vi), min
      apply le_min h8
      rw [Real.rpow_one] at h9
      have : (M0 : ℝ) * Qpre * x ^ stageTan * K ≤ L * K := by rw [hxL] at h9 ⊢; nlinarith
      exact le_of_mul_le_mul_right this hK'
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp hall
  exact ⟨max L0 2, le_max_right _ _, fun L hL => hL0 L (le_trans (le_max_left _ _) hL)⟩

/-- `lem:scale-conditions` at the paper's parameters: at every scale where
(i)–(vii) hold, the consequences hold with `Q = N^β`, `H = N^{β/2}`:
`R ≤ M₀² Q_cl N^{2τ}`, `H D_E ≤ Q`, `n₀ ≤ n ≤ N`, `n^β ≥ H`, `n ≥ 10 n^{6β}`,
`1 ≤ λ ≤ 2`, `λ^{72} ≤ 1 + u_L`; in particular the hypotheses
`H ≤ n^β`, `H D_E ≤ Q` of `lem:record:fibre-scale`(b) and `n ≥ 10 n^{6β}` of (e). -/
theorem ScaleConditionsAt.consequences {K M0 Qcl Qpre N0 N0' L M D0 qE cE : ℕ}
    (h : ScaleConditionsAt K M0 Qcl Qpre N0 N0' L) (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hM : M = K * L ∨ M = L) (hD0 : D0 ∣ M0) (hM0 : 1 ≤ M0)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcop0 : D0.Coprime (qE * cE)) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((K * L : ℕ) : ℝ) ^ stageTau) :
    let N := K * L
    let R := leastSquare (D0 * (qE * cE))
    let n := K * stepScale K M R
    (R : ℝ) ≤ (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * stageTau) ∧
      (N : ℝ) ^ (stageBeta / 2) * ((qE * cE : ℕ) : ℝ) ≤ (N : ℝ) ^ stageBeta ∧
      (scaleN0 K M0 Qcl stageTau N ≤ n ∧ n ≤ N) ∧
      (N : ℝ) ^ (stageBeta / 2) ≤ (n : ℝ) ^ stageBeta ∧
      10 * (n : ℝ) ^ (6 * stageBeta) ≤ n ∧
      (1 ≤ (R * n : ℝ) / M ∧ (R * n : ℝ) / M ≤ 2) ∧
      ((R * n : ℝ) / M) ^ 72 ≤ 1 + scaleU K M0 Qcl stageTau L :=
  scaleConsequences hK hL rfl hM hD0 hM0 hqE hcE hcE0 hcQ hcop0 hcopE hqN
    (by norm_num [stageBeta]) (Real.rpow_nonneg (Nat.cast_nonneg _) _) h.cond_ii
    ⟨h.cond_iii_root, h.cond_iii_size⟩ h.cond_iv

/-- `u_L → 0` at the paper's `τ = 1/201`. -/
theorem tendsto_scaleU_stage {K M0 Qcl : ℕ} (hK : 1 ≤ K) :
    Tendsto (scaleU K M0 Qcl stageTau) atTop (𝓝 0) :=
  tendsto_scaleU hK (by norm_num [stageTau])

/-- `lem:scale-conditions`, assembled: there is `L_* ≥ 2` such that for every
`L ≥ L_*` conditions (i)–(vii) hold, and therefore the consequences hold for
every selection `E` (`D_E = q_E c_E`, `q_E ≤ N^τ`), divisor `D₀ ∣ M₀` and
`I ∈ 𝓘_L`; moreover `u_L → 0`. -/
theorem scaleConditions_assembled (K M0 Qcl Qpre N0 N0' : ℕ) (hK : 1 ≤ K) (hM0 : 1 ≤ M0)
    (hQcl : 1 ≤ Qcl) :
    (∃ Lstar : ℕ, 2 ≤ Lstar ∧ ∀ L, Lstar ≤ L →
      ScaleConditionsAt K M0 Qcl Qpre N0 N0' L ∧
      ∀ M D0 qE cE : ℕ, (M = K * L ∨ M = L) → D0 ∣ M0 → Squarefree qE → IsSquare cE →
        cE ≠ 0 → cE ≤ Qcl → D0.Coprime (qE * cE) → qE.Coprime cE →
        (qE : ℝ) ≤ ((K * L : ℕ) : ℝ) ^ stageTau →
        let N := K * L
        let R := leastSquare (D0 * (qE * cE))
        let n := K * stepScale K M R
        (R : ℝ) ≤ (M0 : ℝ) ^ 2 * Qcl * (N : ℝ) ^ (2 * stageTau) ∧
          (N : ℝ) ^ (stageBeta / 2) * ((qE * cE : ℕ) : ℝ) ≤ (N : ℝ) ^ stageBeta ∧
          (scaleN0 K M0 Qcl stageTau N ≤ n ∧ n ≤ N) ∧
          (N : ℝ) ^ (stageBeta / 2) ≤ (n : ℝ) ^ stageBeta ∧
          10 * (n : ℝ) ^ (6 * stageBeta) ≤ n ∧
          (1 ≤ (R * n : ℝ) / M ∧ (R * n : ℝ) / M ≤ 2) ∧
          ((R * n : ℝ) / M) ^ 72 ≤ 1 + scaleU K M0 Qcl stageTau L) ∧
    Tendsto (scaleU K M0 Qcl stageTau) atTop (𝓝 0) := by
  obtain ⟨Lstar, hL2, hall⟩ := exists_scaleThreshold K M0 Qcl Qpre N0 N0' hK hM0 hQcl
  refine ⟨⟨Lstar, hL2, fun L hL => ⟨hall L hL, ?_⟩⟩, tendsto_scaleU_stage hK⟩
  intro M D0 qE cE hM hD0 hqE hcE hcE0 hcQ hcop0 hcopE hqN
  exact (hall L hL).consequences hK (by omega) hM hD0 hM0 hqE hcE hcE0 hcQ hcop0 hcopE hqN

end Threshold

end Sarkozy.Functional
