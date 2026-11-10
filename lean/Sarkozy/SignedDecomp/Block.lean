module

public import Sarkozy.SignedDecomp.Numbers

@[expose] public section

/-!
# The gates of a middle block from the piece tables (SD2)

`paper/sections/24_matching_mean.tex`, `prop:signed-sides`(i);
`paper/sections/21_middle_records.tex`,
`prop:signed-bounds`(c),(d), `cert:signed-local`; `lem:majorant`; `lem:record:local-domain`(ii).

For a middle block of piece `k` (primes `p_i ≥ X_k`, at most `n_k` of them, scale `r = b^{-1/2}`
with `b ≥ X_k` the least prime):
* **`AnalyticAt`** (hypotheses, the analytic content of PG's `SD` at the paper's constants, per
  prime):
  - `col`: `lem:record:conditional-collision`(d) with `c_col = ccolP` (the paper's value);
  - `new`: `prop:signed-bounds`(c), the centred signed record `O₀ + L^m_t + R^new` with
    `‖R^new‖ ≤ e_sg q`, `e_sg = esgP` (the paper's value);
  - `comp`: `prop:signed-bounds`(c), every centred component has norm at most `c_+ r`,
    `c_+ = cpP` (the paper's value).
* **`gateAt_paper`**: PG's `GateAt` at `e_o = eoP pr ccolP`, `e_sg = esgP`, `c_+ = cpP` and the
  shift `σ = r d_k / H_𝔅`, **proved** from `gate_check` and the monotonicity of the constants
  (`atomsAt_le`, `GammaA_le`, `*_mono`).
* **`decompGateAtC_of_analytic`**: PG's `DecompGateAtC` from `AnalyticAt`.
* `Hblock_le`: `H_𝔅 = ∏(1 + e₀(p)) ≤ (1 + e₀(X))^{n_k}`; `card_le_of_budget`: a block with
  `∑ log p ≤ 570` and primes `≥ X_k` has at most `n_k` primes.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedDecomp

open Sarkozy.PrimeGram Sarkozy.MiddleRecords Sarkozy.SignedGram Sarkozy.SignedComponents
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.SignedEstimates (e0)
open Sarkozy.MainFinal2 (tPaper)
open Sarkozy.MiddleRefinement (sideQ paperSide)

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

variable (pr) in
/-- **The analytic inputs of a middle block at the paper's constants** (hypotheses, per prime
`p_i`, at `(q, r) = (1/p_i, p_i^{-1/2})`):
* `col`: `lem:record:conditional-collision`(d), last claim, with `c_col = ccolP` of
  `eq:signed-constants`;
* `new`: `prop:signed-bounds`(c), `Π_⊥ T[K_{t,p}] Π_⊥ = O₀ + L^m_t + R^new`,
  `‖R^new‖ ≤ e_sg q`, with `e_sg = esgP` of `eq:signed-constants` (`t = 127/500`, `k_col = 9/4`);
* `comp`: `prop:signed-bounds`(c), `‖Π_⊥ T[P_{uv,p}] Π_⊥‖ ≤ c_+ r` for the three components,
  with `c_+ = cpP` of `eq:signed-constants`. -/
structure AnalyticAt (hne : MiddleNonempty pr) (C : FoldComponents pr hne) : Prop where
  col : ∀ i, CollisionBound (hne.F2 i) (ccolP pr i)
  new : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper (esgP pr i)
  comp : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) (cpP pr i * rP pr i)

variable (pr) in
/-- **The analytic inputs of a middle block, with the crude component constant `80`**
(hypotheses): as `AnalyticAt`, with `comp` weakened to `‖Π_⊥ T[P_{uv,p}] Π_⊥‖ ≤ 80 r` (implied by
`prop:signed-bounds`(c), `c_+ < 1.74`; `AnalyticAt.to80`). -/
structure AnalyticAt80 (hne : MiddleNonempty pr) (C : FoldComponents pr hne) : Prop where
  col : ∀ i, CollisionBound (hne.F2 i) (ccolP pr i)
  new : ∀ i, NewDecomp (mP hne i) (∑ c, signedCoef tPaper c • compP hne C c i) tPaper (esgP pr i)
  comp : ∀ c i, CentredNorm (mP hne i) (compP hne C c i) (80 * rP pr i)

omit [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- `H_𝔅 ≤ (1 + e₀(X))^n` for a block of at most `n` primes, all `≥ X ≥ 5`. -/
theorem Hblock_le {X : ℝ} {n : ℕ} (hX : 5 ≤ X) (hXp : ∀ i, X ≤ (pr i : ℝ))
    (hcard : Fintype.card ι ≤ n) : Hblock pr ≤ (1 + e0 X) ^ n := by
  have he : 0 ≤ e0 X := Sarkozy.SignedEstimates.e0_nonneg hX
  unfold Hblock
  calc ∏ i, (1 + e0 (pr i : ℝ)) ≤ ∏ _i : ι, (1 + e0 X) := by
        refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
        · have := Sarkozy.SignedEstimates.e0_nonneg (hX.trans (hXp i)); linarith
        · have := e0_le hX (hXp i); linarith
    _ = (1 + e0 X) ^ Fintype.card ι := by rw [prod_const, card_univ]
    _ ≤ (1 + e0 X) ^ n := pow_le_pow_right₀ (by linarith) hcard

omit [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- **The number of primes of a block** (`lem:record:local-domain`(ii)): if every prime is at least
`X ≥ 2`, `∑ log p ≤ 570` and `2.7182818286^{570} < X^{n+1}`, then there are at most `n` primes. -/
theorem card_le_of_budget {X n : ℕ} (hX : 2 ≤ X) (hXp : ∀ i, X ≤ pr i)
    (hbud : ∑ i, Real.log (pr i) ≤ 570)
    (hE : 27182818286 ^ 570 < X ^ (n + 1) * 10 ^ 5700) : Fintype.card ι ≤ n := by
  have hX1 : (1 : ℝ) < X := by exact_mod_cast hX
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hsum : (Fintype.card ι : ℝ) * Real.log X ≤ 570 := by
    have : ∑ _i : ι, Real.log (X : ℝ) ≤ ∑ i, Real.log (pr i) := by
      refine sum_le_sum fun i _ => ?_
      exact Real.log_le_log (by linarith) (by exact_mod_cast hXp i)
    rw [sum_const, card_univ, nsmul_eq_mul] at this
    linarith
  have hexp : Real.exp 570 < (X : ℝ) ^ (n + 1) := by
    have h1 : Real.exp 570 = Real.exp 1 ^ 570 := by
      rw [← Real.exp_nat_mul]; simp only [Nat.cast_ofNat, mul_one]
    have h2 : Real.exp 1 ^ 570 < (2.7182818286 : ℝ) ^ 570 :=
      pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
    have h3 : ((27182818286 ^ 570 : ℕ) : ℝ) < ((X ^ (n + 1) * 10 ^ 5700 : ℕ) : ℝ) :=
      Nat.cast_lt.mpr hE
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_ofNat] at h3
    have h4 : (2.7182818286 : ℝ) ^ 570 = 27182818286 ^ 570 / 10 ^ 5700 := by
      rw [show (2.7182818286 : ℝ) = 27182818286 / 10 ^ 10 by norm_num, div_pow, ← pow_mul,
        show (10 : ℕ) * 570 = 5700 from rfl]
    rw [h1]
    refine h2.trans ?_
    rw [h4, div_lt_iff₀ (by positivity)]
    exact h3
  have hlog : 570 < ((n : ℝ) + 1) * Real.log X := by
    have := (Real.lt_log_iff_exp_lt (by positivity)).mpr hexp
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have : (Fintype.card ι : ℝ) < n + 1 :=
    lt_of_mul_lt_mul_right (lt_of_le_of_lt hsum hlog) hlX.le
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

omit [Fintype ι] [DecidableEq ι] in
/-- `gammaP ≤ Γ_A` at the prime (`gammaW_le`). -/
theorem gammaP_le_GammaAP (h19 : ∀ i, 19 ≤ pr i) (i : ι) : gammaP pr i ≤ GammaAP pr i := by
  have h7 : (7 : ℝ) ≤ (Fintype.card (ZMod (pr i)) : ℝ) := by
    rw [ZMod.card]; exact_mod_cast le_trans (by norm_num) (h19 i)
  have h := gammaW_le (F := ZMod (pr i)) h7
  rw [ZMod.card, one_div, Real.sqrt_inv] at h
  exact h

theorem hX_cast {k : Fin 33} (hX5 : 5 ≤ XQ k) :
    ((hX k : ℚ) : ℝ) = (1 + e0 (XQ k : ℝ)) ^ nX k := by
  unfold hX
  push_cast
  rw [eQ_cast hX5]

/-- **The gates on a middle block of piece `k`** at `e_o = eoP pr ccolP`, `e_sg = esgP` and any
component constants `cp ≤ c_B` (`c_B` rational, with the two component gates at `c_B`), for any
scale `r ≥ 0` with `p^{-1/2} ≤ r ≤ r_X` at every prime. -/
theorem gateAt_gen (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) (hcard : Fintype.card ι ≤ nX k)
    {r : ℝ} (hr0 : 0 ≤ r) (hrp : ∀ i, rP pr i ≤ r) (hrX : r ≤ (rX k : ℝ)) (cp : ι → ℝ) (cB : ℚ)
    (hcpX : ∀ i, cp i ≤ (cB : ℝ)) (p4 : 0 ≤ cB)
    (g2 : ((gamX k + eoX k * rX k) ^ 2 + 627 / 500 * cB ^ 2) * rX k * hX k ≤ sideQ k)
    (g4 : cB * rX k ≤ 1) :
    GateAt pr (eoP pr (ccolP pr)) (esgP pr) cp (r * paperSide k / Hblock pr) ∧
      (∀ i, 0 ≤ ccolP pr i) ∧ (∀ i, 0 ≤ esgP pr i) := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨g1, -, g3, -⟩ := gate_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hX5 : (5 : ℕ) ≤ XQ k := le_trans (by norm_num) hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hp0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le (by norm_num) (hX'.trans (hXp' i))
  have hp5 : ∀ i, (5 : ℝ) ≤ pr i := fun i => le_trans (by norm_num) (hX'.trans (hXp' i))
  have hrP0 : ∀ i, 0 ≤ rP pr i := fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeA : ∀ i, (atomsAt (pr i) (GammaAP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 ((hγ0 i).trans (hγA i)) (hΓA i)
  have hLeG : ∀ i, (atomsAt (pr i) (gammaP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 (hγ0 i) ((hγA i).trans (hΓA i))
  -- the constants
  have hcol : ∀ i, ccolP pr i = ccolPoly (atomsAt (pr i) (GammaAP pr i)) := fun i =>
    cColS_eq (hp5 i) _
  have hcolX : ∀ i, ccolP pr i ≤ ((ccolX k : ℚ) : ℝ) := fun i => by
    rw [hcol, ccolX, ccolPoly_cast]; exact ccolPoly_mono (hLeA i)
  have hcol0 : ∀ i, 0 ≤ ccolP pr i := fun i => by rw [hcol]; exact ccolPoly_nonneg (hLeA i)
  have hesg : ∀ i, esgP pr i = esgPoly (atomsAt (pr i) (GammaAP pr i)) := fun i =>
    esgL_eq (hp0 i) _
  have hesgX : ∀ i, esgP pr i ≤ ((esgX k : ℚ) : ℝ) := fun i => by
    rw [hesg, esgX, esgPoly_cast]; exact esgPoly_mono (hLeA i)
  have hesg0 : ∀ i, 0 ≤ esgP pr i := fun i => by rw [hesg]; exact esgPoly_nonneg (hLeA i)
  have heo : ∀ i, eoP pr (ccolP pr) i = eoPoly (atomsAt (pr i) (gammaP pr i)) (ccolP pr i) :=
    fun i => eoC_eq _ _ _
  have heoX : ∀ i, eoP pr (ccolP pr) i ≤ ((eoX k : ℚ) : ℝ) := fun i => by
    rw [heo, eoX, eoPoly_cast]; exact eoPoly_mono (hLeG i) (hcol0 i) (hcolX i)
  have heo0 : ∀ i, 0 ≤ eoP pr (ccolP pr) i := fun i => by
    rw [heo]; exact eoPoly_nonneg (hLeG i) (hcol0 i)
  -- the density bound
  have hH : Hblock pr ≤ ((hX k : ℚ) : ℝ) := by
    rw [hX_cast hX5]; exact Hblock_le (by exact_mod_cast hX5) hXp' hcard
  have hH0 : 0 < Hblock pr := Hblock_pos pr h19
  -- the rational gates in `ℝ`
  obtain ⟨p1, p2, p3, -, p5, p6⟩ := pos_check k
  have pG : (0 : ℝ) ≤ ((gamX k : ℚ) : ℝ) := by exact_mod_cast p1
  have pE : (0 : ℝ) ≤ ((eoX k : ℚ) : ℝ) := by exact_mod_cast p2
  have pS : (0 : ℝ) ≤ ((esgX k : ℚ) : ℝ) := by exact_mod_cast p3
  have pC : (0 : ℝ) ≤ ((cB : ℚ) : ℝ) := by exact_mod_cast p4
  have pR : (0 : ℝ) ≤ ((rX k : ℚ) : ℝ) := by exact_mod_cast p5
  have pT : (0 : ℝ) ≤ ((stU : ℚ) : ℝ) := by exact_mod_cast p6
  have h1 : (((stU * gamX k + (eoX k + esgX k) * rX k) * hX k : ℚ) : ℝ) ≤ ((sideQ k : ℚ) : ℝ) := by
    exact_mod_cast g1
  have h2 : ((((gamX k + eoX k * rX k) ^ 2 + 627 / 500 * cB ^ 2) * rX k * hX k : ℚ) : ℝ) ≤
      ((sideQ k : ℚ) : ℝ) := by
    exact_mod_cast g2
  have h3 : (((gamX k + eoX k * rX k) * rX k : ℚ) : ℝ) ≤ 1 := by exact_mod_cast g3
  have h4 : (((cB * rX k : ℚ) : ℝ)) ≤ 1 := by exact_mod_cast g4
  push_cast at h1 h2 h3 h4
  have hd : paperSide k = ((sideQ k : ℚ) : ℝ) := rfl
  set G := ((gamX k : ℚ) : ℝ)
  set E := ((eoX k : ℚ) : ℝ)
  set S := ((esgX k : ℚ) : ℝ)
  set P := ((cB : ℚ) : ℝ)
  set R := ((rX k : ℚ) : ℝ)
  set T := ((stU : ℚ) : ℝ)
  set H := ((hX k : ℚ) : ℝ)
  set d := ((sideQ k : ℚ) : ℝ)
  have hrR : ∀ i, rP pr i ≤ R := fun i => (hrp i).trans hrX
  have hσ : ∀ x : ℝ, 0 ≤ x → x * H ≤ d → r * x ≤ r * paperSide k / Hblock pr := by
    intro x hx hxd
    rw [hd, le_div_iff₀ hH0]
    have : x * Hblock pr ≤ d := (mul_le_mul_of_nonneg_left hH hx).trans hxd
    nlinarith
  refine ⟨⟨fun i => ?_, (G + E * R) * r, P * r, by positivity, ?_, by positivity, ?_, fun i => ?_,
    fun i => ?_, ?_⟩, hcol0, hesg0⟩
  · -- the prime Gram gate
    have hA : Sarkozy.Envelopes.sT tPaper * gammaP pr i + (eoP pr (ccolP pr) i + esgP pr i) *
        rP pr i ≤ T * G + (E + S) * R := by
      have := mul_le_mul sT_le ((hγA i).trans (hΓA i)) (hγ0 i) pT
      have := mul_le_mul (add_le_add (heoX i) (hesgX i)) (hrR i) (hrP0 i) (add_nonneg pE pS)
      linarith
    have hA0 : 0 ≤ Sarkozy.Envelopes.sT tPaper * gammaP pr i + (eoP pr (ccolP pr) i + esgP pr i) *
        rP pr i := by
      have : 0 ≤ Sarkozy.Envelopes.sT tPaper := Real.sqrt_nonneg _
      have := hγ0 i
      have := heo0 i
      have := hesg0 i
      have := hrP0 i
      positivity
    have := hσ (T * G + (E + S) * R) (by positivity) h1
    calc _ ≤ (T * G + (E + S) * R) * r := mul_le_mul hA (hrp i) (hrP0 i) (by positivity)
      _ = r * (T * G + (E + S) * R) := by ring
      _ ≤ _ := this
  · have : (G + E * R) * r ≤ (G + E * R) * R := mul_le_mul_of_nonneg_left hrX (by positivity)
    linarith
  · have : P * r ≤ P * R := mul_le_mul_of_nonneg_left hrX pC
    linarith
  · refine min_le_of_right_le ?_
    have : gammaP pr i + eoP pr (ccolP pr) i * rP pr i ≤ G + E * R := by
      have := mul_le_mul (heoX i) (hrR i) (hrP0 i) pE
      linarith [(hγA i).trans (hΓA i)]
    exact mul_le_mul this (hrp i) (hrP0 i) (by positivity)
  · exact min_le_of_right_le (mul_le_mul (hcpX i) (hrp i) (hrP0 i) pC)
  · have ht : (1 : ℝ) + tPaper = 627 / 500 := by norm_num [tPaper]
    rw [ht]
    have := hσ (((G + E * R) ^ 2 + 627 / 500 * P ^ 2) * R) (by positivity) (by linarith)
    have hW : 0 ≤ (G + E * R) ^ 2 + 627 / 500 * P ^ 2 := by positivity
    calc ((G + E * R) * r) ^ 2 + 627 / 500 * (P * r) ^ 2
        = r * (((G + E * R) ^ 2 + 627 / 500 * P ^ 2) * r) := by ring
      _ ≤ r * (((G + E * R) ^ 2 + 627 / 500 * P ^ 2) * R) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrX hW) hr0
      _ ≤ _ := this

/-- **The gates and the nonnegativity of the paper's constants on a middle block of piece `k`**,
for any scale `r ≥ 0` with `p^{-1/2} ≤ r ≤ r_X` at every prime. -/
theorem gateAt_paper (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) (hcard : Fintype.card ι ≤ nX k)
    {r : ℝ} (hr0 : 0 ≤ r) (hrp : ∀ i, rP pr i ≤ r) (hrX : r ≤ (rX k : ℝ)) :
    GateAt pr (eoP pr (ccolP pr)) (esgP pr) (cpP pr) (r * paperSide k / Hblock pr) ∧
      (∀ i, 0 ≤ ccolP pr i) ∧ (∀ i, 0 ≤ esgP pr i) ∧ (∀ i, 0 ≤ cpP pr i) := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  obtain ⟨-, g2, -, g4⟩ := gate_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hp0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le (by norm_num) (hX'.trans (hXp' i))
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeA : ∀ i, (atomsAt (pr i) (GammaAP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 ((hγ0 i).trans (hγA i)) (hΓA i)
  have hcp : ∀ i, cpP pr i = cpPoly (atomsAt (pr i) (GammaAP pr i)) := fun i => cpL_eq (hp0 i) _
  have hcpX : ∀ i, cpP pr i ≤ ((cpX k : ℚ) : ℝ) := fun i => by
    rw [hcp, cpX, cpPoly_cast]; exact cpPoly_mono (hLeA i)
  have hcp0 : ∀ i, 0 ≤ cpP pr i := fun i => by rw [hcp]; exact cpPoly_nonneg (hLeA i)
  obtain ⟨G, h0, h1⟩ := gateAt_gen k hXp hcard hr0 hrp hrX (cpP pr) (cpX k) hcpX
    (pos_check k).2.2.2.1 g2 g4
  exact ⟨G, h0, h1, hcp0⟩

variable (pr) in
/-- **PG's `DecompGateAtC` on a middle block of piece `k`** from the analytic inputs at the
paper's constants (`AnalyticAt`); the gates are proved (`gateAt_paper`). -/
theorem decompGateAtC_of_analytic (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) (hcard : Fintype.card ι ≤ nX k) {r : ℝ} (hr0 : 0 ≤ r)
    (hrp : ∀ i, rP pr i ≤ r) (hrX : r ≤ (rX k : ℝ)) (H : AnalyticAt pr hne C) :
    DecompGateAtC pr hne C r (paperSide k) := by
  obtain ⟨G, h0, h1, h2⟩ := gateAt_paper k hXp hcard hr0 hrp hrX
  exact ⟨ccolP pr, esgP pr, cpP pr, ⟨H.col, H.new, H.comp, h0, h1, h2⟩, G⟩

variable (pr) in
/-- **PG's `DecompGateAtC` from the crude-component inputs** (`AnalyticAt80`; the gates proved,
`gateAt_gen` at `c_B = 80`, `crude_check`). -/
theorem decompGateAtC_of_analytic80 (hne : MiddleNonempty pr) (C : FoldComponents pr hne)
    (k : Fin 33) (hXp : ∀ i, XQ k ≤ pr i) (hcard : Fintype.card ι ≤ nX k) {r : ℝ} (hr0 : 0 ≤ r)
    (hrp : ∀ i, rP pr i ≤ r) (hrX : r ≤ (rX k : ℝ)) (H : AnalyticAt80 pr hne C) :
    DecompGateAtC pr hne C r (paperSide k) := by
  obtain ⟨c2, c4, -⟩ := crude_check k
  obtain ⟨G, h0, h1⟩ := gateAt_gen k hXp hcard hr0 hrp hrX (fun _ => 80) 80
    (fun _ => by norm_num) (by norm_num) c2 c4
  exact ⟨ccolP pr, esgP pr, fun _ => 80, ⟨H.col, H.new, H.comp, h0, h1, fun _ => by norm_num⟩, G⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **The paper's component bound implies the crude one** at a middle block of piece `k`:
`c_+(p) ≤ c_+(X) ≤ 80`. -/
theorem AnalyticAt.to80 {hne : MiddleNonempty pr} {C : FoldComponents pr hne} (k : Fin 33)
    (hXp : ∀ i, XQ k ≤ pr i) (H : AnalyticAt pr hne C) : AnalyticAt80 pr hne C := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hXp' : ∀ i, (XQ k : ℝ) ≤ (pr i : ℝ) := fun i => by exact_mod_cast hXp i
  have h19 : ∀ i, 19 ≤ pr i := fun i => le_trans (by norm_num) (hX24.trans (hXp i))
  have hp0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le (by norm_num) (hX'.trans (hXp' i))
  have hγ0 : ∀ i, 0 ≤ gammaP pr i := gammaP_nonneg h19
  have hγA : ∀ i, gammaP pr i ≤ GammaAP pr i := gammaP_le_GammaAP h19
  have hΓA : ∀ i, GammaAP pr i ≤ ((gamX k : ℚ) : ℝ) := fun i => GammaA_le hX24 (hXp' i) hs2 hs1
  have hLeA : ∀ i, (atomsAt (pr i) (GammaAP pr i)).Le (AX k).cast := fun i =>
    atomsAt_le hX24 (hXp' i) hs2 hs1 ((hγ0 i).trans (hγA i)) (hΓA i)
  have h80 : ((cpX k : ℚ) : ℝ) ≤ 80 := by exact_mod_cast (crude_check k).2.2
  refine ⟨H.col, H.new, fun c i => ?_⟩
  have hcp : cpP pr i = cpPoly (atomsAt (pr i) (GammaAP pr i)) := cpL_eq (hp0 i) _
  have hle : cpP pr i ≤ 80 := by
    rw [hcp]
    refine le_trans ?_ h80
    rw [cpX, cpPoly_cast]
    exact cpPoly_mono (hLeA i)
  have h0 : 0 ≤ cpP pr i := by rw [hcp]; exact cpPoly_nonneg (hLeA i)
  have hr : 0 ≤ rP pr i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  exact centredNorm_mono (mP_nonneg hne i) (H.comp c i) (mul_nonneg h0 hr)
    (mul_le_mul_of_nonneg_right hle hr)

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- **The scale of a block**: if `r ≥ 0`, `r² b = 1`, `b ≤ p` at every prime and `X_k ≤ b`, then
`p^{-1/2} ≤ r ≤ r_X = 1/⌊√X_k⌋`. -/
theorem scale_bounds (k : Fin 33) {r b : ℝ} (hr0 : 0 ≤ r) (hrb : r ^ 2 * b = 1)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) (hXb : (XQ k : ℝ) ≤ b) :
    (∀ i, rP pr i ≤ r) ∧ r ≤ (rX k : ℝ) := by
  obtain ⟨hX24, hs1, hs2, -⟩ := table_check k
  have hX' : (2 : ℝ) ^ 24 ≤ (XQ k : ℝ) := by exact_mod_cast hX24
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) (hX'.trans hXb)
  have hr2 : r ^ 2 = b⁻¹ := by field_simp; linarith
  refine ⟨fun i => ?_, ?_⟩
  · have hp0 : (0 : ℝ) < pr i := lt_of_lt_of_le hb0 (hbp i)
    have h : rP pr i ^ 2 ≤ r ^ 2 := by
      rw [hr2, rP, inv_pow, Real.sq_sqrt hp0.le]
      exact inv_anti₀ hb0 (hbp i)
    exact (pow_le_pow_iff_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hr0 two_ne_zero).mp h
  · have hs0 : (0 : ℝ) < sX k := by exact_mod_cast hs1
    have hsX : ((sX k : ℝ)) ^ 2 ≤ (XQ k : ℝ) := by exact_mod_cast hs2
    have h : r ^ 2 ≤ ((rX k : ℚ) : ℝ) ^ 2 := by
      rw [hr2, rX]
      push_cast
      rw [div_pow, one_pow, one_div]
      exact inv_anti₀ (by positivity) (hsX.trans hXb)
    have hR : (0 : ℝ) ≤ ((rX k : ℚ) : ℝ) := by
      rw [rX]; push_cast; positivity
    exact (pow_le_pow_iff_left₀ hr0 hR two_ne_zero).mp h

end Block

end Sarkozy.SignedDecomp
