module

public import Sarkozy.DensityChain.Fields

@[expose] public section

/-!
# Fields 28–31 with the constants inequality discharged by summability

`envMeanBound_of_chain_lp`, `fixMeanBound_of_chain_lp` (`Fields`) leave one inequality between
constants per counterexample:
`C_dc L^{-σ} α Π + B T^{-1/4} Π_H + E_𝒥 E_ω ∑_f r₂ ≤ c L^{-1/825} α`, where
`Π = ∏_𝔟 (1 + 2‖Q_𝔟‖ + ‖Ñ₀ − μ‖)` and `Π_H = ∏_𝔟 (1 + (2‖Q_𝔟‖ + ‖Ñ₀ − μ‖) w_𝔟^{1/4})`.
This file discharges it as the paper does:

* `Π ≤ exp(2 T_Q + U₀)` from the price totals `∑_𝔟 u_𝔟 ≤ T_Q`, `∑_𝔟 u'_𝔟 ≤ U₀` and
  `‖Q_𝔟‖ ≤ u_𝔟`, `‖Ñ₀ − μ‖ ≤ u'_𝔟` (`sq(D)^a ≥ 1`) (`prod_termWeight_le`);
* `Π_H ≤ exp W` from the `w^{1/4}`-weighted summability `∑_𝔟 w_𝔟^{1/4} (2u_𝔟 + u'_𝔟) ≤ W`
  (summability (c) of `def:cp8`; the data's `Summability.summable` with `w = q_𝔟`)
  (`prod_termWeight_rankin_le`);
* `L^{-σ} ≤ L^{-1/825}` for `σ ≥ 1/825`, and `B T^{-1/4} ≤ C' N^{ε'/20 − τ/4} α ≤ C' L^{-1/825} α`
  for `T = N^τ` and `ε'/20 − τ/4 ≤ −1/825` ((S4); satisfiable, `lp_room`);
* the `r₂` summation (`lem:sharp-first`, DC2's fields 24–27) stays an input, as
  `E_𝒥 E_ω ∑_f r₂ ≤ c₂ L^{-1/825} α`.

**`envMeanBound_of_summable`**, **`fixMeanBound_of_summable`**: B9's `EnvMeanBound`,
`FixMeanBound` with the explicit constant
`c = C_dc e^{2T_Q + U₀} + M₀^{72} |X₀|^{72} C_lp K e^W + c₂`. The per-term inputs that remain:
every term is chain-covered (`EnvChainTerm`), or the `μ`-term's direct bound, or large
(`N^τ < ∏_{f∪g} w`).
-/

namespace Sarkozy.DensityChain

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- The per-atom sum of the weights: `∑_{x,y} G = 1 + 2‖Q‖ + ‖Ñ₀ − μ‖`. -/
theorem sum_termWeight (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (b : BlockAtom Bk J L) :
    ∑ x, ∑ y, termWeight D L Qb b x y =
      1 + (2 * ∑ z, |lawDensity (Qb b) z| + ∑ z, |lawDensity (recLaw D L b) z|) := by
  simp only [Fintype.sum_bool, termWeight, ↓reduceIte, Bool.false_eq_true]
  ring

omit [DecidableEq P] in
/-- The `w^{1/4}`-weighted per-atom sum. -/
theorem sum_termWeight_rankin (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (w : BlockAtom Bk J L → ℝ)
    (b : BlockAtom Bk J L) :
    ∑ x, ∑ y, termWeight D L Qb b x y *
        (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1) =
      1 + w b ^ ((1 : ℝ) / 4) *
        (2 * ∑ z, |lawDensity (Qb b) z| + ∑ z, |lawDensity (recLaw D L b) z|) := by
  simp only [Fintype.sum_bool, termWeight, ↓reduceIte, Bool.false_eq_true, Bool.true_or,
    Bool.or_self, Bool.false_or]
  ring

/-- `‖κ‖ ≤ u` from `‖κ‖ sq(D)^a ≤ u` and `a ≥ 0`. -/
theorem norm_le_price {x u : ℝ} {d : ℕ} {a' : ℝ} (ha : 0 ≤ a') (hx : 0 ≤ x)
    (h : x * ((leastSquare d : ℕ) : ℝ) ^ a' ≤ u) : x ≤ u := by
  have h1 : (1 : ℝ) ≤ ((leastSquare d : ℕ) : ℝ) ^ a' :=
    Real.one_le_rpow (by exact_mod_cast leastSquare_pos d) ha
  nlinarith

omit [DecidableEq P] in
/-- **`Π ≤ exp(2 T_Q + U₀)`** from the price totals. -/
theorem prod_termWeight_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ha : 0 ≤ a) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : BlockAtom Bk J L → ℝ) {TQ U0 : ℝ}
    (hQ : ∀ b, (∑ x, |lawDensity (Qb b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ price b)
    (hR : ∀ b, (∑ x, |lawDensity (recLaw D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b)
    (hTQ : ∑ b, price b ≤ TQ) (hU0 : ∑ b, D.GB.uprice L b ≤ U0) :
    ∏ b, ∑ x, ∑ y, termWeight D L Qb b x y ≤ Real.exp (2 * TQ + U0) := by
  simp_rw [sum_termWeight]
  refine (prod_one_add_le_exp _ _ fun b _ => by positivity).trans ?_
  apply Real.exp_le_exp.mpr
  have h1 : ∀ b, 2 * ∑ z, |lawDensity (Qb b) z| + ∑ z, |lawDensity (recLaw D L b) z| ≤
      2 * price b + D.GB.uprice L b := by
    intro b
    have := norm_le_price ha (sum_nonneg fun _ _ => abs_nonneg _) (hQ b)
    have := norm_le_price ha (sum_nonneg fun _ _ => abs_nonneg _) (hR b)
    linarith
  calc ∑ b, (2 * ∑ z, |lawDensity (Qb b) z| + ∑ z, |lawDensity (recLaw D L b) z|)
      ≤ ∑ b, (2 * price b + D.GB.uprice L b) := sum_le_sum fun b _ => h1 b
    _ = 2 * ∑ b, price b + ∑ b, D.GB.uprice L b := by rw [sum_add_distrib, mul_sum]
    _ ≤ 2 * TQ + U0 := by linarith

omit [DecidableEq P] in
/-- **`Π_H ≤ exp W`** from the `w^{1/4}`-weighted summability (`def:cp8`(c)). -/
theorem prod_termWeight_rankin_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ha : 0 ≤ a) (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : BlockAtom Bk J L → ℝ) (w : BlockAtom Bk J L → ℝ) (hw : ∀ b, 0 ≤ w b) {W : ℝ}
    (hQ : ∀ b, (∑ x, |lawDensity (Qb b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ price b)
    (hR : ∀ b, (∑ x, |lawDensity (recLaw D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b)
    (hW : ∑ b, w b ^ ((1 : ℝ) / 4) * (2 * price b + D.GB.uprice L b) ≤ W) :
    ∏ b, ∑ x, ∑ y, termWeight D L Qb b x y *
      (if (x || y) = true then w b ^ ((1 : ℝ) / 4) else 1) ≤ Real.exp W := by
  simp_rw [sum_termWeight_rankin]
  have hw4 : ∀ b, 0 ≤ w b ^ ((1 : ℝ) / 4) := fun b => Real.rpow_nonneg (hw b) _
  refine (prod_one_add_le_exp _ _ fun b _ => mul_nonneg (hw4 b) (by positivity)).trans ?_
  apply Real.exp_le_exp.mpr
  refine le_trans (sum_le_sum fun b _ => ?_) hW
  apply mul_le_mul_of_nonneg_left _ (hw4 b)
  have := norm_le_price ha (sum_nonneg fun _ _ => abs_nonneg _) (hQ b)
  have := norm_le_price ha (sum_nonneg fun _ _ => abs_nonneg _) (hR b)
  linarith

/-- **The constants inequality** of `Fields` from the bounds on `Π`, `Π_H`, the exponents and
the `r₂` summation. -/
theorem constants_le {L : ℕ} (hL : 1 ≤ L) {α Cdc Pm0 PH0 Pm PH B0 ε' σ r c₂ : ℝ}
    (hα : 0 ≤ α) (hCdc : 0 ≤ Cdc) (hB0 : 0 ≤ B0) (hPm0 : 0 ≤ Pm) (hPH0 : 0 ≤ PH)
    (hPm : Pm ≤ Pm0) (hPH : PH ≤ PH0) (hσ : Sarkozy.cancellationDecay ≤ σ)
    (hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (hr : r ≤ c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α) :
    Cdc * (L : ℝ) ^ (-σ) * α * Pm +
        B0 * paperCutoff (blockScale * L) ^ ε' * α *
          ((((blockScale * L : ℕ) : ℝ) ^ stageTau) ^ (-((1 : ℝ) / 4)) * PH) + r ≤
      (Cdc * Pm0 + B0 * PH0 + c₂) * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * α := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set N : ℝ := ((blockScale * L : ℕ) : ℝ) with hN
  have hLN : (L : ℝ) ≤ N := by
    rw [hN]
    exact_mod_cast Nat.le_mul_of_pos_left L (by norm_num [blockScale])
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (hL1.trans hLN)
  set lam : ℝ := (L : ℝ) ^ (-Sarkozy.cancellationDecay) with hlam
  have hlam0 : 0 ≤ lam := Real.rpow_nonneg (by linarith) _
  have h1 : (L : ℝ) ^ (-σ) ≤ lam :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h2 : paperCutoff (blockScale * L) ^ ε' * (N ^ stageTau) ^ (-((1 : ℝ) / 4)) ≤ lam := by
    unfold paperCutoff liftExponent
    rw [← Real.rpow_mul hN0.le, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (hL1.trans hLN) ?_)
      (Real.rpow_le_rpow_of_nonpos (by linarith) hLN
        (by norm_num [Sarkozy.cancellationDecay]))
    linarith
  have hp1 : 0 ≤ paperCutoff (blockScale * L) ^ ε' := by
    unfold paperCutoff
    exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
  have hp2 : 0 ≤ (N ^ stageTau) ^ (-((1 : ℝ) / 4)) :=
    Real.rpow_nonneg (Real.rpow_nonneg hN0.le _) _
  have e1 : Cdc * (L : ℝ) ^ (-σ) * α * Pm ≤ Cdc * Pm0 * lam * α := by
    have := mul_le_mul h1 hPm hPm0 hlam0
    have h3 : 0 ≤ Cdc * α := mul_nonneg hCdc hα
    nlinarith
  have e2 : B0 * paperCutoff (blockScale * L) ^ ε' * α * ((N ^ stageTau) ^ (-((1 : ℝ) / 4)) * PH)
      ≤ B0 * PH0 * lam * α := by
    have h3 : 0 ≤ B0 * α := mul_nonneg hB0 hα
    have h4 : paperCutoff (blockScale * L) ^ ε' * ((N ^ stageTau) ^ (-((1 : ℝ) / 4)) * PH) ≤
        lam * PH0 := by
      rw [← mul_assoc]
      exact mul_le_mul h2 hPH hPH0 hlam0
    calc B0 * paperCutoff (blockScale * L) ^ ε' * α * ((N ^ stageTau) ^ (-((1 : ℝ) / 4)) * PH)
        = (B0 * α) * (paperCutoff (blockScale * L) ^ ε' *
            ((N ^ stageTau) ^ (-((1 : ℝ) / 4)) * PH)) := by ring
      _ ≤ (B0 * α) * (lam * PH0) := mul_le_mul_of_nonneg_left h4 h3
      _ = B0 * PH0 * lam * α := by ring
  have e3 : r ≤ c₂ * lam * α := hr
  nlinarith [e1, e2, e3]

/-- The constant `M₀^{72} |X₀|^{72} C_lp K` of `lpBound`. -/
noncomputable def lpConst (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (blk : J₀ → Bk) (M0 : ℕ) (C : ℝ) :
    ℝ :=
  (M0 : ℝ) ^ 72 * (Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C * blockScale

omit [DecidableEq J₀] in
theorem lpBound_eq (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (blk : J₀ → Bk) (M0 : ℕ) (C ε' : ℝ)
    (L : ℕ) (A : Finset ℤ) :
    lpBound m₀ blk M0 C ε' L A =
      lpConst m₀ blk M0 C * paperCutoff (blockScale * L) ^ ε' * density (blockScale * L) A := by
  unfold lpBound lpConst
  ring

/-- **Fields 30–31 (`EnvMeanBound`) with density-dc, density-lp and the constants discharged.**
The constant is `c = C_dc e^{2T_Q + U₀} + M₀^{72} |X₀|^{72} C_lp K e^W + c₂`. -/
theorem envMeanBound_of_summable (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (Qb : ∀ L b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (price : ∀ L, BlockAtom Bk J L → ℝ) (u : E → reservedCut.Half)
    (r2 : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hp : ∀ L j, (p L j).Prime) (_hinj : ∀ L, Injective (p L))
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ L k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hu : Injective u) (_hprice : ∀ L b, 0 ≤ price L b)
    (_hQpos : ∀ L b, IsPositiveRecord (Qb L b))
    (_hQ : ∀ L b, (∑ x, |lawDensity (Qb L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ price L b)
    (_hR : ∀ L b, (∑ x, |lawDensity (recLaw D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b)
    {TQ U0 W : ℝ} (_hTQ : ∀ L, ∑ b, price L b ≤ TQ) (_hU0 : ∀ L, ∑ b, D.GB.uprice L b ≤ U0)
    (w : ∀ L, BlockAtom Bk J L → ℝ) (_hw : ∀ L b, 0 ≤ w L b)
    (_hW : ∀ L, ∑ b, w L b ^ ((1 : ℝ) / 4) * (2 * price L b + D.GB.uprice L b) ≤ W)
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      (queryLaw D.index.C D.index.t).expect (fun Jq =>
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ Jq, (queryLaw D.index.C D.index.t).weight Jq ≠ 0 → ∀ f, ∀ g ∈ validChoices f,
        EnvChainTerm hcop D (hpair L) (Qb L) u Qcl Jq f g ∨
        (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
            (fun ω => envTermEnergy hcop D hpair Qb u L A Jq ω f g) ≤
          (1 + z L) * envTermPrice D price L A Jq f g +
            (∏ b, termWeight D L (Qb L) b (f b) (g b)) *
              (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
        ((blockScale * L : ℕ) : ℝ) ^ stageTau <
          ∏ b, (if (f b || g b) = true then w L b else 1))),
    EnvMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * Real.exp (2 * TQ + U0) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂) Qb price u r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := envMeanBound_of_chain_lp (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, ?_⟩
  intro D hpair z Qb price u r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hprice
    hQpos hQ hR TQ U0 W hTQ hU0 w hw hW σ hσc hS1 hS4 c₂ hr2 hterms
  have hσ : 0 ≤ σ := le_trans (by norm_num [Sarkozy.cancellationDecay]) hσc
  apply hmain D hpair z _ Qb price u r2 ha hM0 hsc hp hinj hMod hcopM hz hu hprice hQpos hQ hR
    hσ hS1
  have hL1 : ∀ᶠ L : ℕ in atTop, 1 ≤ L := eventually_ge_atTop 1
  filter_upwards [hterms, hr2, hL1] with L hL hrL hL1L
  intro C hC hk A hA hY
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hT : 0 < ((blockScale * L : ℕ) : ℝ) ^ stageTau :=
    Real.rpow_pos_of_pos (by exact_mod_cast hKL) _
  refine ⟨w L, ((blockScale * L : ℕ) : ℝ) ^ stageTau, hw L, hT, hL C hC hk A hA hY, ?_⟩
  have hCdc := dcConstant_nonneg (C' := (prefixConductor (m₀ := m₀) blk D.R.P5 : ℝ))
    (γ := Sarkozy.AnalyticStage.γ) (Nat.cast_nonneg _) (Nat.cast_nonneg M0)
    (X := (Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ)) hC1.le hC71.le
  have hB0 : 0 ≤ lpConst m₀ blk M0 Clp := by
    unfold lpConst
    have : (0 : ℝ) ≤ blockScale := by norm_num [blockScale]
    positivity
  have hPm := prod_termWeight_le D L ha (Qb L) (price L) (hQ L) (hR L) (hTQ L) (hU0 L)
  have hPH := prod_termWeight_rankin_le D L ha (Qb L) (price L) (w L) (hw L) (hQ L) (hR L)
    (hW L)
  have hPm0 : 0 ≤ ∏ b, ∑ x, ∑ y, termWeight D L (Qb L) b x y :=
    prod_nonneg fun b _ => sum_nonneg fun x _ => sum_nonneg fun y _ =>
      termWeight_nonneg D L (Qb L) b x y
  have hPH0 : 0 ≤ ∏ b, ∑ x, ∑ y, termWeight D L (Qb L) b x y *
      (if (x || y) = true then w L b ^ ((1 : ℝ) / 4) else 1) :=
    prod_nonneg fun b _ => sum_nonneg fun x _ => sum_nonneg fun y _ =>
      mul_nonneg (termWeight_nonneg D L (Qb L) b x y) (by
        split_ifs
        · exact Real.rpow_nonneg (hw L b) _
        · exact zero_le_one)
  have key := constants_le hL1L (density_nonneg (blockScale * L) A) hCdc hB0 hPm0 hPH0 hPm hPH
    hσc hS4 (hrL C hC hk A hA hY)
  rw [lpBound_eq]
  unfold remainder
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · ring
  · rfl

/-- **Fields 28–29 (`FixMeanBound`) with density-dc, density-lp and the constants discharged**
(as `envMeanBound_of_summable`, with `Q_𝔟 = wrapInc`, `u_𝔟 = wrapPrice`). -/
theorem fixMeanBound_of_summable (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ C1 C71 Clp : ℝ, 0 < C1 ∧ 0 < C71 ∧ 0 < Clp ∧ DCBlockProp ε C1 C71 ∧
    ∀ (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (z : ℕ → ℝ) (u : E → reservedCut.Half) (t : ZMod blockScale)
    (r2 : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (_ha : 0 ≤ a) {M0 Qcl Qpre N0 N0' : ℕ} (_hM0 : 1 ≤ M0)
    (_hsc : ∀ᶠ L in atTop, ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (_hp : ∀ L j, (p L j).Prime) (_hinj : ∀ L, Injective (p L))
    (_hMod : modulus pr h ∣ M0)
    (_hcopM : ∀ L k, (modulus pr h).Coprime (crtModuli m₀ blk p L k))
    (_hz : ∀ᶠ L in atTop, scaleU blockScale M0 Qcl stageTau L ≤ z L)
    (_hu : Injective u)
    (_hQ : ∀ L b, (∑ x, |lawDensity (TheoremCBlock.Structured.wrapInc D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
        TheoremCBlock.Structured.wrapPrice D L b)
    (_hR : ∀ L b, (∑ x, |lawDensity (recLaw D L b) x|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ D.GB.uprice L b)
    {TQ U0 W : ℝ} (_hTQ : ∀ L, ∑ b, TheoremCBlock.Structured.wrapPrice D L b ≤ TQ)
    (_hU0 : ∀ L, ∑ b, D.GB.uprice L b ≤ U0)
    (w : ∀ L, BlockAtom Bk J L → ℝ) (_hw : ∀ L b, 0 ≤ w L b)
    (_hW : ∀ L, ∑ b, w L b ^ ((1 : ℝ) / 4) *
      (2 * TheoremCBlock.Structured.wrapPrice D L b + D.GB.uprice L b) ≤ W)
    {σ : ℝ} (_hσc : Sarkozy.cancellationDecay ≤ σ)
    (_hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ)
    (_hS4 : ε' / 20 - stageTau / 4 ≤ -Sarkozy.cancellationDecay)
    (c₂ : ℝ)
    (_hr2 : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, r2 L A S Jq ω f)) ≤
        c₂ * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A))
    (_hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ S : Finset E, S ≠ ∅ → ∀ Jq, ∀ f, ∀ g ∈ validChoices f,
        FixChainTerm hcop D (hpair L) (TheoremCBlock.Structured.wrapInc D L) u Qcl S t Jq f g ∨
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
            (fun ω => fixTermEnergy hcop D hpair u t L A S Jq ω f g) ≤
          (1 + z L) * fixTermPrice D L A S Jq f g +
            (∏ b, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b (f b) (g b)) *
              (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
                (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
                (L : ℝ) ^ (-σ) * density (blockScale * L) A) ∨
        ((blockScale * L : ℕ) : ℝ) ^ stageTau <
          ∏ b, (if (f b || g b) = true then w L b else 1))),
    FixMeanBound hcop D hpair z
      (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * Real.exp (2 * TQ + U0) +
        lpConst m₀ blk M0 Clp * Real.exp W + c₂) u t r2 := by
  obtain ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, hmain⟩ := fixMeanBound_of_chain_lp (a := a)
    (m₀ := m₀) (blk := blk) (p := p) (pr := pr) (h := h) (E := E) hcop ε ε' hε hε'
  refine ⟨C1, C71, Clp, hC1, hC71, hClp, hdcb, ?_⟩
  intro D hpair z u t r2 ha M0 Qcl Qpre N0 N0' hM0 hsc hp hinj hMod hcopM hz hu hQ hR TQ U0 W
    hTQ hU0 w hw hW σ hσc hS1 hS4 c₂ hr2 hterms
  have hσ : 0 ≤ σ := le_trans (by norm_num [Sarkozy.cancellationDecay]) hσc
  apply hmain D hpair z _ u t r2 ha hM0 hsc hp hinj hMod hcopM hz hu hQ hR hσ hS1
  have hL1 : ∀ᶠ L : ℕ in atTop, 1 ≤ L := eventually_ge_atTop 1
  filter_upwards [hterms, hr2, hL1] with L hL hrL hL1L
  intro C hC hk A hA hY S hS
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hT : 0 < ((blockScale * L : ℕ) : ℝ) ^ stageTau :=
    Real.rpow_pos_of_pos (by exact_mod_cast hKL) _
  refine ⟨w L, ((blockScale * L : ℕ) : ℝ) ^ stageTau, hw L, hT, hL C hC hk A hA hY S hS, ?_⟩
  have hCdc := dcConstant_nonneg (C' := (prefixConductor (m₀ := m₀) blk D.R.P5 : ℝ))
    (γ := Sarkozy.AnalyticStage.γ) (Nat.cast_nonneg _) (Nat.cast_nonneg M0)
    (X := (Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ)) hC1.le hC71.le
  have hB0 : 0 ≤ lpConst m₀ blk M0 Clp := by
    unfold lpConst
    have : (0 : ℝ) ≤ blockScale := by norm_num [blockScale]
    positivity
  have hPm := prod_termWeight_le D L ha (TheoremCBlock.Structured.wrapInc D L)
    (TheoremCBlock.Structured.wrapPrice D L) (hQ L) (hR L) (hTQ L) (hU0 L)
  have hPH := prod_termWeight_rankin_le D L ha (TheoremCBlock.Structured.wrapInc D L)
    (TheoremCBlock.Structured.wrapPrice D L) (w L) (hw L) (hQ L) (hR L) (hW L)
  have hPm0 : 0 ≤ ∏ b, ∑ x, ∑ y,
      termWeight D L (TheoremCBlock.Structured.wrapInc D L) b x y :=
    prod_nonneg fun b _ => sum_nonneg fun x _ => sum_nonneg fun y _ =>
      termWeight_nonneg D L _ b x y
  have hPH0 : 0 ≤ ∏ b, ∑ x, ∑ y, termWeight D L (TheoremCBlock.Structured.wrapInc D L) b x y *
      (if (x || y) = true then w L b ^ ((1 : ℝ) / 4) else 1) :=
    prod_nonneg fun b _ => sum_nonneg fun x _ => sum_nonneg fun y _ =>
      mul_nonneg (termWeight_nonneg D L _ b x y) (by
        split_ifs
        · exact Real.rpow_nonneg (hw L b) _
        · exact zero_le_one)
  have key := constants_le hL1L (density_nonneg (blockScale * L) A) hCdc hB0 hPm0 hPH0 hPm hPH
    hσc hS4 (hrL C hC hk A hA hY S hS)
  rw [lpBound_eq]
  unfold remainder
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · ring
  · rfl

end Sarkozy.DensityChain
