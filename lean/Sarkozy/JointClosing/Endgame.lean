module

public import Sarkozy.TargetLedger.Closing

@[expose] public section

/-!
# The joint endgame: Theorem C from the joint bound of `cor:joint-closing`

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`;
`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`.

K0's `TheoremCBlock.ComparisonData.closingEstimates` (and `closingEstimates_classes`) derive the
`joint` field of `Param.ClosingEstimates` from two *separate* bounds: (i) the comparison loss
`(2^k − 1)(Y_λ − Y_ν) ≤ ((2^k − 1)𝓔 + o(1)) Y` and (ii) the mean credit (CP7)
`½(e_L + e_R) ≥ (m − o(1)) Y`, with `H = (1 − 2^{-k})𝓔 + (1 − m)/2^k`. The paper's final closing
does not have this form: `eq:final-joint-closing`,
`Θ = (63/64)(L₀ + 𝓔) + J + W + (1 − m₁)/64 − Δ_mid − Δ_u + R_u`, comes from the *joint* bound of
`cor:joint-closing`, and the corrections `Δ_mid` (`prop:joint-middle-mean`) and `Δ_u − R_u`
(`prop:joint-upper-mean`) are "justified inside the common positive completion; they are not
additional independent instances of (CP7)" (`subsec` "The joint closing number").

This file takes the joint bound itself as the input:

* `JointBound D H` (`cor:joint-closing`, hypothesis): robustly
  `(2^k − 1)(Y_λ − Y_ν) − ½(e_L + e_R) ≤ (2^k H − 1 + o(1)) Y`;
* **`closingEstimates_joint`**: the five closing estimates with joint constant `H`, from
  `JointBound D H` and the four other Section 10 inputs (sharp first stage, nonwrapping
  cancellation, wrapping terms, envelope energies) — the proof of `closingEstimates_classes` with
  the `joint` field taken directly. Neither (CP5) (`ClassBounds`), (E1) (`EnvelopeBound`) nor the
  mean credit `MC` is used;
* `theoremC_joint`, `theoremC_joint_reduced`: Theorem C with `jointTheta k L₀ J W H < 1`;
* **`jointTheta_le_of_ledger`**: `jointTheta 6 L₀ J W H^{ledger} ≤ Θ^{ledger}` from the
  comparison of `B`, `L₀`, `T`, `R_I`, `S + A` with the ledger (no `hm`, no `𝓔`);
* **`theoremC_joint_reduced_target_of_ledger`**: the bound `N^{1 − a_T/71}` from `TargetBounds l`,
  the five comparisons, `JointBound D l.jointConstant`, and the inputs of T1's
  `theoremC_classes_reduced_target_of_ledger` other than `hm`, `CB`, `hΨ`, `hE1`, `hCB`.

The data `D` still carries the fields `MC` and `SM` of `TheoremCBlock.ComparisonData`; no
statement here reads them (`MC.m` does not occur in `jointTheta … H`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.JointClosing

open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetDecay targetDecay_nonneg target_valid target_saving TargetBounds)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The joint comparison-and-mean bound** (`cor:joint-closing`, its displayed hypothesis, with
`k = |E|` queries): robustly,
`(2^k − 1)(Y_λ − Y_ν) − ½(e_L + e_R) ≤ (2^k H − 1 + o(1)) Y`, with `Y_λ`, `Y_ν` the energies of the
first stage and of the comparison law and `e_s = Q_{⊗M_s}(X̄, X̄)` the mean energies of the
envelopes of (CP6). It is exactly the `joint` field of `Param.ClosingEstimates`. -/
def JointBound (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (H : ℝ) : Prop :=
  ∃ εj : ℕ → ℝ, Tendsto εj atTop (𝓝 0) ∧ ∃ cj : ℝ, 0 ≤ cj ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (2 ^ Fintype.card E - 1) * (energyFirst D.FS.lam (blockLift m₀ blk p) L A -
          energyComparison D.CL.ν (blockLift m₀ blk p) L A) -
        (energyMean (blockLift m₀ blk p) D.ME.ML L A +
          energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2 ≤
      (2 ^ Fintype.card E * H - 1 + εj L) * D.Y L A + remainder cj L A

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The five closing estimates from the joint bound** (`thm:record:criterion` in the form of
`cor:joint-closing`): the first stage (`lem:record:first-stage`, from `SharpFirstTerms`), the frame
(`eq:cp:mean-step`, from the brackets of (CP6)), the wrapping terms (`lem:record:wrap-expansion`),
the envelope energies (`lem:envelope-energy`) and the joint bound with constant `H`, taken
directly. The proof of K0's `closingEstimates_classes` without its comparison and mean steps. -/
theorem closingEstimates_joint {H : ℝ} (hJ : JointBound D H)
    (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop) :
    Nonempty (Param.ClosingEstimates (Params.ofDecay a) D.Y (Fintype.card E) D.L₀ D.Jc D.W H) := by
  obtain ⟨εj, hεj, cj, hcj, hjoint⟩ := hJ
  obtain ⟨εs, hεs0, hεs, cs, hcs, rs, htermS, hrS⟩ := hSF
  obtain ⟨cn, hcn, hnon⟩ := hcan
  obtain ⟨εw, hεw0, hεw, cw, hcw, hwrapT⟩ := hwr
  obtain ⟨εenv, hεenv, cenv, hcenv, henvL, henvR⟩ := henv
  -- first stage
  have hfirst := TheoremCParam.firstStage_estimate (Atom := BlockAtom Bk J)
      (Xb := BlockLabel m₀ blk p) D.FS.ϑ₀
    (D.R.law p) D.FS.ρ D.FS.lam (blockLift m₀ blk p) (fun L b => D.law_positive D.FS.ϑ₀_family L b)
    (fun L b => D.rho_below L b) (fun L b i => D.FS.κ' L b i - D.FS.κ L b i) (fun L b => rfl)
    D.FS.tag D.FS.dprice D.FS.vprice (fun L b i => D.dprice_nonneg L b i)
    (fun L b i => D.vprice_nonneg L b i) D.FS.pvar (fun L b => D.pvar_nonneg L b)
    D.FS.P_total D.FS.dT_total D.FS.vT_total εs hεs0 rs cs htermS hrS
  -- wrap
  have hwrap := wrap_estimate m₀ blk p pr h hcop D.Y D.S.index.μ D.S.index.hμ D.S.index.hμ1
    D.S.index.t D.S.index.hnorm D.S.Q.u D.S.Q.w D.S.Q.hu D.S.Q.hw D.CL.ν
    (Bf := D.B) (SA := D.CL.S + D.CL.A) (x := D.wrapRatio) εw hεw0 hcn hcw hnon hwrapT
  -- envelopes
  have hJc := D.two_pow_mul_Jc
  have henvL' : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      inclusionEnergyL D.index D.ME.ML (fun L A e => blockInput m₀ blk p pr h hcop L A e)
          (blockLift m₀ blk p) L A ≤
        (2 ^ Fintype.card E * D.Jc + εenv L) * D.Y L A + remainder cenv L A := by
    rw [hJc]
    exact henvL
  have henvR' : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      inclusionEnergyR D.index D.ME.MR (fun L A e => blockInput m₀ blk p pr h hcop L A e)
          (blockLift m₀ blk p) L A ≤
        (2 ^ Fintype.card E * D.Jc + εenv L) * D.Y L A + remainder cenv L A := by
    rw [hJc]
    exact henvR
  exact ⟨Param.ClosingEstimates.ofConcrete
      (Params.ofDecay a) D.index D.FS.lam D.ME.ML D.CL.ν D.ME.MR
    (fun L A e => blockInput m₀ blk p pr h hcop L A e)
        (fun L A e => blockInput m₀ blk p pr h hcop L A e)
    (blockLift m₀ blk p) D.ME.bracket (fun L A e y => expect_blockInput m₀ blk p pr h hcop L A e y)
    (fun L A e y => expect_blockInput m₀ blk p pr h hcop L A e y)
    (fun L => 3 ^ Fintype.card E * εw L) εenv (fun L => εs L * D.L₀) εj
    (4 ^ Fintype.card E * cn + 3 ^ Fintype.card E * cw) cenv cs cj
    (by simpa only [mul_zero] using hεw.const_mul ((3 : ℝ) ^ Fintype.card E)) hεenv
    (firstStage_error_tendsto _ _ _ hεs) hεj
    (by positivity) hcenv hcs hcj hwrap henvL' henvR' hfirst hjoint⟩

/-- **Theorem C in the joint form** (`thm:comparison` with `cor:joint-closing`): if
`jointTheta k L₀ J W H < 1`, the joint bound with constant `H` and the four other Section 10
inputs give `s(N) ≤ C N^{1 − ε}`. -/
theorem theoremC_joint (hP : (Params.ofDecay a).Valid) {H : ℝ}
    (hΘ : jointTheta (Fintype.card E) D.L₀ D.Jc D.W H < 1) (hJ : JointBound D H)
    (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.PowerSavingBound (Params.ofDecay a) := by
  obtain ⟨e⟩ := closingEstimates_joint D hcop hJ hSF hcan hwr henv
  exact Param.paperMain_powerSavingBound_theta m₀ p hP D.S.p_prime D.S.p_inj
    (blockAssembly m₀ blk D.R.μ₀) D.R.μp (blockAssembly_unif m₀ blk D.R.μ₀ D.R.unif₀)
    (blockAssembly_rp m₀ blk D.R.μ₀ D.R.rp₀).slot D.R.unifp (fun q _ hq => (D.R.rpp q hq).slot)
    hunit hΘ
    (e.transfer fun L A _ => energyFirst_blockRefLaws m₀ blk p D.R.μ₀ D.R.μp L A)

/-- **Theorem C in the joint form, reduced** (the nonwrapping cancellation from
`lem:record:density-can`, the wrapping terms from the fixed-interval envelope energies), as K0's
`theoremC_classes_reduced`. -/
theorem theoremC_joint_reduced (hP : (Params.ofDecay a).Valid) (ha : 0 ≤ a) {H : ℝ}
    (hΘ : jointTheta (Fintype.card E) D.L₀ D.Jc D.W H < 1) (hJ : JointBound D H)
    (hSF : D.SharpFirstTerms) (hDC : DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.PowerSavingBound (Params.ofDecay a) :=
  theoremC_joint D hcop hP hΘ hJ hSF
    (D.nonwrappingCancellation_of_densityCancellation' hcop ha hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv hunit

/-! ## The closing from a ledger, with the ledger's joint constant -/

omit [DecidableEq P] in
/-- **The joint closing number of the data is at most the ledger's** (`eq:final-joint-closing`):
with the ledger's joint constant `H = (63/64)𝓔 + (1 − m₁)/64 − Δ_mid − Δ_u + R_u`
(`PrimitiveLedger.jointConstant`), `jointTheta 6 L₀ J W H ≤ Θ^{ledger}` when `B`, `L₀`, `T`, `R_I`
and `S + A` are bounded by the ledger. No mean credit and no `𝓔` of the data enter. -/
theorem jointTheta_le_of_ledger {l : PrimitiveLedger} (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A) :
    jointTheta (Fintype.card E) D.L₀ D.Jc D.W l.jointConstant ≤ l.theta := by
  have hw0 := PrimitiveLedger.wrapFactor_pos
  have hJ : D.Jc ≤ l.J := by
    unfold TheoremCBlock.ComparisonData.Jc PrimitiveLedger.J
    rw [hcard]
    have hR6 : (D.S.index.R_I / 2) ^ 6 ≤ (l.R_I / 2) ^ 6 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 6
    have h1 : D.B * Real.exp D.ME.T ≤ l.B * Real.exp l.T :=
      mul_le_mul hB (Real.exp_le_exp.mpr hT) (Real.exp_pos _).le (le_trans hB0 hB)
    exact mul_le_mul h1 hR6 (pow_nonneg (by linarith) 6)
      (mul_nonneg (le_trans hB0 hB) (Real.exp_pos _).le)
  have hW : D.W ≤ l.W := by
    unfold TheoremCBlock.ComparisonData.W PrimitiveLedger.W wrapNumber
    rw [hcard, TargetLedger.ComparisonData.wrapRatio_eq]
    have hx : D.S.index.R_I * PrimitiveLedger.wrapFactor / 2 ≤
        l.R_I / 2 * PrimitiveLedger.wrapFactor := by
      have := mul_le_mul_of_nonneg_right hR hw0.le
      linarith
    have hx0 : 0 ≤ D.S.index.R_I * PrimitiveLedger.wrapFactor / 2 :=
      div_nonneg (mul_nonneg hR0 hw0.le) (by norm_num)
    have hpow : (1 + D.S.index.R_I * PrimitiveLedger.wrapFactor / 2) ^ 6 - 1 ≤
        (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 :=
      sub_le_sub_right (pow_le_pow_left₀ (by linarith) (by linarith) 6) 1
    have hpow0 : 0 ≤ (1 + D.S.index.R_I * PrimitiveLedger.wrapFactor / 2) ^ 6 - 1 := by
      have := one_le_pow₀ (n := 6)
        (show (1 : ℝ) ≤ 1 + D.S.index.R_I * PrimitiveLedger.wrapFactor / 2 by linarith)
      linarith
    have h1 : D.B * Real.exp (D.CL.S + D.CL.A) ≤ l.B * Real.exp (l.S + l.A) :=
      mul_le_mul hB (Real.exp_le_exp.mpr hSA) (Real.exp_pos _).le (le_trans hB0 hB)
    exact mul_le_mul h1 hpow hpow0 (mul_nonneg (le_trans hB0 hB) (Real.exp_pos _).le)
  rw [← l.jointTheta_eq, hcard]
  unfold jointTheta
  have h64 : (0 : ℝ) ≤ 1 - ((2 : ℝ) ^ 6)⁻¹ := by norm_num
  have := mul_le_mul_of_nonneg_left hL₀ h64
  linarith

/-- **The bound `N^{1 − a_T/71}` from the joint bound, closing discharged from the target ledger**
(`thm:comparison` with `cor:joint-closing`, `thm:density:induction` at `a_T`): T1's
`theoremC_classes_reduced_target_of_ledger` with the comparison bound (`CB`, `hΨ`, `hE1`, `hCB`)
and the mean credit (`hm`) replaced by the joint bound with the ledger's joint constant. -/
theorem theoremC_joint_reduced_target_of_ledger
    (D : TheoremCBlock.ComparisonData targetDecay m₀ blk p pr h E)
    (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
    {l : PrimitiveLedger} (hl : TargetBounds l)
    (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A)
    (hJ : JointBound D l.jointConstant)
    (hSF : D.SharpFirstTerms)
    (hDC : TheoremCBlock.DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound TargetLedger.targetSaving := by
  rw [← target_saving]
  exact (Param.sarkozyBound_iff _).mp
    (theoremC_joint_reduced D hcop target_valid targetDecay_nonneg
      ((jointTheta_le_of_ledger D hcard hB0 hB hL₀ hT hR0 hR hSA).trans_lt hl.theta_lt_one)
      hJ hSF hDC hfix henv hunit)

end Sarkozy.JointClosing
