module

public import Sarkozy.TheoremC.RecordComparison
public import Sarkozy.TheoremCParam.Defs

@[expose] public section



open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.Comparison Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-! ## Elementary facts about counterexamples and remainders -/

/-- The reference energy is positive at a least normalized counterexample. -/
theorem counterexample_pos {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} (hC : 1 ≤ C) {L : ℕ}
    {A : Finset ℤ}
    (h : C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent < Y L A) :
    0 < Y L A := by
  have h0 : 0 ≤ C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  linarith

variable {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]

/-! ## The joint hypothesis from (i) and (ii) -/

/-- **The hypothesis of `cor:joint-closing` from (i) and (ii) of `thm:record:criterion`.**
If `|Y_ν - Y_λ| ≤ (𝓔 + ε₁) Y + r₁` (i) and `½(e_L + e_R) ≥ (m - ε₂) Y - r₂` ((CP7), (ii)) at
every least normalized counterexample, then for every number `k` of queries
`(2^k - 1)(Y_λ - Y_ν) - ½(e_L + e_R) ≤ (2^k 𝓗 - 1 + o(1)) Y + r` with
`𝓗 = jointConstantC k 𝓔 m`. -/
theorem joint_of_comparison_mean (μ lam ν ML MR : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ) {𝓔 m c₁ c₂ : ℝ} {ε₁ ε₂ : ℕ → ℝ}
    (hcomp : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      |energyComparison ν F L A - energyFirst lam F L A| ≤
        (𝓔 + ε₁ L) * energyFirst μ F L A + remainder c₁ L A)
    (hmean : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      (m - ε₂ L) * energyFirst μ F L A - remainder c₂ L A ≤
        (energyMean F ML L A + energyMean F MR L A) / 2) (k : ℕ) :
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      (2 ^ k - 1) * (energyFirst lam F L A - energyComparison ν F L A) -
          (energyMean F ML L A + energyMean F MR L A) / 2 ≤
        (2 ^ k * jointConstantC k 𝓔 m - 1 + ((2 ^ k - 1) * ε₁ L + ε₂ L)) *
            energyFirst μ F L A + remainder ((2 ^ k - 1) * c₁ + c₂) L A := by
  filter_upwards [hcomp, hmean] with L h1 h2
  intro C hC hind A hA hc
  have e1 := h1 C hC hind A hA hc
  have e2 := h2 C hC hind A hA hc
  have hk : (0 : ℝ) ≤ 2 ^ k - 1 := by
    have := one_le_pow₀ (n := k) (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  have hdiff : energyFirst lam F L A - energyComparison ν F L A ≤
      (𝓔 + ε₁ L) * energyFirst μ F L A + remainder c₁ L A := by
    have := neg_abs_le (energyComparison ν F L A - energyFirst lam F L A)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hk
  rw [two_pow_mul_jointConstantC, remainder_add, remainder_mul]
  nlinarith [hmul, e2]

/-! ## Hypothesis (i): the record comparison -/

section Comparison

variable {T : ∀ L, Atom L → Type} [∀ L b, Fintype (T L b)] [∀ L b, DecidableEq (T L b)]

/-- **Hypothesis (i) of `thm:record:criterion`: `|Y_ν - Y_λ| ≤ (𝓔 + o(1)) Y`**
(`lem:record:record-expansion` (i) and (ii) without the classes of (CP5), at the reserved
cut). At every scale `L`:

* (CP4)(b): `ν_b = λ_b + ∑_t (ζ^s_{b,t} + ζ^a_{b,t})`, `ζ^s` symmetric and `ζ^a` skew at
  `ι`, with the brackets `(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0`, `π̃ ≥ 0`;
* (CP3): `λ_b` symmetric at `ι` and `(Ñ_b λ_b; λ_b Ñ_b) ⪰_ι 0`;
* the prices `π^ε_{b,t} = π̃^ε_{b,t} q_b` (`q_b ≥ 0` the selection factors) have totals at
  most `S` (symmetric) and `Askew` (skew; the paper's `A`, renamed since `A` names the set),
  and `𝓔 ≥ B(e^S cosh A - 1)`;
* `hE1`: (E1) of `lem:energy-toolkit` for the envelopes of the selections
  (`lem:bracket-energy`), robustly: `Y_{(⊗_{b∈X} D) ⊗ Ñ_{-X}} ≤ (B + ε) C_X Y + r_ω`,
  `C_X = ∏_{b ∈ X} q_b`, with `ε ≥ 0` and remainders `r_ω` whose sum weighted by the
  monomials `∏_{b ∈ X} π̃^{ε_b}_{b,t_b}` is a density-linear remainder `hrE` (the
  large-union terms of `lem:record:density-lp`).

Then `|Y_ν - Y_λ| ≤ (𝓔 + ε (e^S cosh A - 1)) Y + c L^{-σ} α`. -/
theorem comparison_estimate (μ lam Nt ν : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (ζ D : ∀ L b, T L b → ChangeType → ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (hν : ∀ L b, ν L b = lam L b + ∑ t, (ζ L b t .sym + ζ L b t .skew))
    (hlam : ∀ L b, IsSymmetricAt reservedCut (lam L b))
    (hs : ∀ L b t, IsSymmetricAt reservedCut (ζ L b t .sym))
    (ha : ∀ L b t, IsSkewAt reservedCut (ζ L b t .skew))
    (πt : ∀ L b, T L b → ChangeType → ℝ) (hπt : ∀ L b t e, 0 ≤ πt L b t e)
    (hN : ∀ L b, reservedCut.Bracket (Nt L b) (lam L b) (Nt L b))
    (hζ : ∀ L b t e, reservedCut.Bracket (πt L b t e • D L b t e) (ζ L b t e)
      (πt L b t e • D L b t e))
    (q : ∀ L, Atom L → ℝ) (hq : ∀ L b, 0 ≤ q L b) {S Askew Bf 𝓔 cE : ℝ}
    (hS : ∀ L, ∑ b, symTotal (fun b t e => πt L b t e * q L b) b ≤ S)
    (hA : ∀ L, ∑ b, skewTotal (fun b t e => πt L b t e * q L b) b ≤ Askew)
    (hBf : 0 ≤ Bf) (h𝓔 : Bf * (Real.exp S * Real.cosh Askew - 1) ≤ 𝓔)
    (εE : ℕ → ℝ) (hεE0 : ∀ L, 0 ≤ εE L) (rE : ∀ L, Finset ℤ → Choice (T L) → ℝ)
    (hE1 : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F)
        fun L A => ∀ ω : Choice (T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (Nt L) (D L) ω) (F L A) ≤
        (Bf + εE L) * (∏ b ∈ Choice.support ω, q L b) * energyFirst μ F L A + rE L A ω)
    (hrE : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (T L) => IsSelection ω),
        monomial (πt L) ω * rE L A ω ≤ remainder cE L A) :
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      |energyComparison ν F L A - energyFirst lam F L A| ≤
        (𝓔 + εE L * (Real.exp S * Real.cosh Askew - 1)) * energyFirst μ F L A +
          remainder cE L A := by
  filter_upwards [hE1, hrE] with L h1 h2
  intro C hC hind A' hA' hc
  have hE := h1 C hC hind A' hA' hc
  have hr := h2 C hC hind A' hA' hc
  have hY : 0 < energyFirst μ F L A' := counterexample_pos hC hc
  have hBz : 0 ≤ Bf + εE L := add_nonneg hBf (hεE0 L)
  have hterm : ∀ ω : Choice (T L), IsSelection ω →
      |term (lam L) (ζ L) (F L A') ω| ≤
        (Bf + εE L) * monomial (fun b t e => πt L b t e * q L b) ω * energyFirst μ F L A' +
          monomial (πt L) ω * rE L A' ω := by
    intro ω hω
    have h1' := abs_term_le_envelope (c := reservedCut) (hN L) (hζ L) (F L A') ω
    have hm : 0 ≤ monomial (πt L) ω := monomial_nonneg (hπt L) ω
    have h2' := mul_le_mul_of_nonneg_left (hE ω hω) hm
    rw [monomial_mul_selectionFactor]
    calc |term (lam L) (ζ L) (F L A') ω|
        ≤ monomial (πt L) ω * diagonalIntegral (envelopeLaw (Nt L) (D L) ω) (F L A') := h1'
      _ ≤ monomial (πt L) ω * ((Bf + εE L) * (∏ b ∈ Choice.support ω, q L b) *
            energyFirst μ F L A' + rE L A' ω) := h2'
      _ = (Bf + εE L) * (monomial (πt L) ω * ∏ b ∈ Choice.support ω, q L b) *
            energyFirst μ F L A' + monomial (πt L) ω * rE L A' ω := by ring
  have hmain := abs_energy_sub_le_of_terms reservedCut (hν L) (hlam L) (hs L) (ha L) (F L A')
    (fun b t e => mul_nonneg (hπt L b t e) (hq L b)) hY.le hBz
    (fun ω => monomial (πt L) ω * rE L A' ω) hterm
  have hS0 : 0 ≤ ∑ b, skewTotal (fun b t e => πt L b t e * q L b) b :=
    sum_nonneg fun b _ => sum_nonneg fun t _ => mul_nonneg (hπt L b t _) (hq L b)
  have hmono := exp_mul_cosh_le_of_le (hS L) hS0 (hA L)
  have hnueq : energyComparison ν F L A' = diagonalIntegral (tensorLaw (ν L)) (F L A') :=
    Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
  have hlameq : energyFirst lam F L A' = diagonalIntegral (tensorLaw (lam L)) (F L A') :=
    Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
  have step1 : (Bf + εE L) * (Real.exp (∑ b, symTotal (fun b t e => πt L b t e * q L b) b) *
        Real.cosh (∑ b, skewTotal (fun b t e => πt L b t e * q L b) b) - 1) *
          energyFirst μ F L A' ≤
      (Bf + εE L) * (Real.exp S * Real.cosh Askew - 1) * energyFirst μ F L A' := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    apply mul_le_mul_of_nonneg_left _ hBz
    linarith
  have step2 : (Bf + εE L) * (Real.exp S * Real.cosh Askew - 1) * energyFirst μ F L A' ≤
      (𝓔 + εE L * (Real.exp S * Real.cosh Askew - 1)) * energyFirst μ F L A' := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    linarith
  rw [hnueq, hlameq]
  linarith [hmain, step1, step2, hr]

/-- **The hypothesis of `cor:joint-closing`** from the record comparison
(`comparison_estimate`, hypothesis (i) of `thm:record:criterion`) and the mean credit of
(CP7) (hypothesis (ii)): `joint_of_comparison_mean` with `ε₁ = ε (e^S cosh A - 1)` and the
remainder constant `c₁ = cE`. The only analytic hypotheses are `hE1`/`hrE` (see
`comparison_estimate`) and the robust (CP7) bound `hmean`. -/
theorem joint_estimate (μ lam Nt ν ML MR : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (ζ D : ∀ L b, T L b → ChangeType → ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
    (hν : ∀ L b, ν L b = lam L b + ∑ t, (ζ L b t .sym + ζ L b t .skew))
    (hlam : ∀ L b, IsSymmetricAt reservedCut (lam L b))
    (hs : ∀ L b t, IsSymmetricAt reservedCut (ζ L b t .sym))
    (ha : ∀ L b t, IsSkewAt reservedCut (ζ L b t .skew))
    (πt : ∀ L b, T L b → ChangeType → ℝ) (hπt : ∀ L b t e, 0 ≤ πt L b t e)
    (hN : ∀ L b, reservedCut.Bracket (Nt L b) (lam L b) (Nt L b))
    (hζ : ∀ L b t e, reservedCut.Bracket (πt L b t e • D L b t e) (ζ L b t e)
      (πt L b t e • D L b t e))
    (q : ∀ L, Atom L → ℝ) (hq : ∀ L b, 0 ≤ q L b) {S Askew Bf 𝓔 cE : ℝ}
    (hS : ∀ L, ∑ b, symTotal (fun b t e => πt L b t e * q L b) b ≤ S)
    (hA : ∀ L, ∑ b, skewTotal (fun b t e => πt L b t e * q L b) b ≤ Askew)
    (hBf : 0 ≤ Bf) (h𝓔 : Bf * (Real.exp S * Real.cosh Askew - 1) ≤ 𝓔)
    (εE : ℕ → ℝ) (hεE0 : ∀ L, 0 ≤ εE L) (rE : ∀ L, Finset ℤ → Choice (T L) → ℝ)
    (hE1 : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F)
        fun L A => ∀ ω : Choice (T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (Nt L) (D L) ω) (F L A) ≤
        (Bf + εE L) * (∏ b ∈ Choice.support ω, q L b) * energyFirst μ F L A + rE L A ω)
    (hrE : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (T L) => IsSelection ω),
        monomial (πt L) ω * rE L A ω ≤ remainder cE L A)
    {m c₂ : ℝ} {ε₂ : ℕ → ℝ}
    (hmean : Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      (m - ε₂ L) * energyFirst μ F L A - remainder c₂ L A ≤
        (energyMean F ML L A + energyMean F MR L A) / 2) (k : ℕ) :
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst μ F) fun L A =>
      (2 ^ k - 1) * (energyFirst lam F L A - energyComparison ν F L A) -
          (energyMean F ML L A + energyMean F MR L A) / 2 ≤
        (2 ^ k * jointConstantC k 𝓔 m - 1 +
            ((2 ^ k - 1) * (εE L * (Real.exp S * Real.cosh Askew - 1)) + ε₂ L)) *
          energyFirst μ F L A + remainder ((2 ^ k - 1) * cE + c₂) L A :=
  joint_of_comparison_mean μ lam ν ML MR F
    (ε₁ := fun L => εE L * (Real.exp S * Real.cosh Askew - 1))
    (comparison_estimate μ lam Nt ν F ζ D hν hlam hs ha πt hπt hN hζ q hq hS hA hBf h𝓔 εE
      hεE0 rE hE1 hrE) hmean k

end Comparison

end Sarkozy.TheoremCParam
