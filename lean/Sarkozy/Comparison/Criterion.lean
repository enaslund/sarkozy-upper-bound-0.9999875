module

public import Sarkozy.RelativeErrors

/-!
# The closing criterion of Theorem C, with explicit robust errors

This module formalizes the scalar part of `thm:record:criterion` and its joint form
`cor:joint-closing` (`paper/sections/11_comparison_proof.tex`). The five estimates
combined there are:

* (wrap) `lem:record:wrap-expansion`: `2^k Y_ν ≤ J_ν + (2^k W + o(1)) Y`;
* (frame) `cor:index-support-frame`, as used in `eq:cp:mean-step`:
  `J_ν ≤ Y_ν + ½[(V_L - e_L) + (V_R - e_R)]`;
* (envelope) `lem:envelope-energy`: `V_L, V_R ≤ (2^k J + o(1)) Y`, where
  `2^k J = B e^T R_I^k`;
* (first stage) `lem:record:first-stage`: `Y_λ ≥ (1 - L₀ - o(1)) Y`;
* (joint) the hypothesis of `cor:joint-closing`:
  `(2^k - 1)(Y_λ - Y_ν) - ½(e_L + e_R) ≤ (2^k H - 1 + o(1)) Y`.

Here `Y` is the reference energy. Every `o(1)` of the paper is robust
(`def:robust`, `lem:record:rec`): it consists of a relative error tending to zero
uniformly in the set and in the induction constant, and of analytic remainders that
are linear in the density. We record each estimate in exactly that form,
`… + ε(L) Y + c L^(-σ) α`, at every least normalized counterexample
(`def:record:counterexample`) of every sufficiently large scale, uniformly in the
induction constant `C ≥ 1`. The conclusion is the project's `RawComparison`
recurrence with coefficient tending to `Θ = (1 - 2^(-k)) L₀ + J + W + H`.

The energies are abstract functions of the scale and the set here. Their definitions
for the paper's laws, and the proofs of the five estimates, are separate tasks.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Sarkozy.Comparison

/-- `P L A` holds at every least normalized counterexample `(L, A)` of every
sufficiently large scale `L`, uniformly in the induction constant `C ≥ 1`
(the antecedent of `Sarkozy.RawComparison`). -/
def AtCounterexamples (Y : ℕ → Finset ℤ → ℝ) (P : ℕ → Finset ℤ → Prop) : Prop :=
  ∀ᶠ L : ℕ in atTop, ∀ C : ℝ, 1 ≤ C →
    (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt Y C k) →
    ∀ A : Finset ℤ, Admissible (blockScale * L) A →
      C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A →
      P L A

/-- A density-linear analytic remainder `c L^(-σ) α`, `σ = 1/825`. -/
noncomputable def remainder (c : ℝ) (L : ℕ) (A : Finset ℤ) : ℝ :=
  c * (L : ℝ) ^ (-cancellationDecay) * density (blockScale * L) A

/-- The five robust estimates of the closing criterion for `k` queries, with closing
data `L₀, J, W, H` (`H` is the joint comparison-and-mean constant of
`cor:joint-closing`). -/
structure ClosingEstimates (Y : ℕ → Finset ℤ → ℝ) (k : ℕ) (L₀ J W H : ℝ) where
  /-- Energy of the first-stage law `λ`. -/
  Yfs : ℕ → Finset ℤ → ℝ
  /-- Energy of the comparison law `ν`. -/
  Yν : ℕ → Finset ℤ → ℝ
  /-- Signed index form `J_ν`. -/
  Jν : ℕ → Finset ℤ → ℝ
  /-- Mean energies of the two envelopes of (CP6). -/
  eL : ℕ → Finset ℤ → ℝ
  eR : ℕ → Finset ℤ → ℝ
  /-- Single-half random-inclusion energies of the two envelopes. -/
  VL : ℕ → Finset ℤ → ℝ
  VR : ℕ → Finset ℤ → ℝ
  /-- Relative errors, one per estimate. -/
  εwrap : ℕ → ℝ
  εenv : ℕ → ℝ
  εfirst : ℕ → ℝ
  εjoint : ℕ → ℝ
  /-- Remainder constants, one per estimate. -/
  cwrap : ℝ
  cenv : ℝ
  cfirst : ℝ
  cjoint : ℝ
  εwrap_tendsto : Tendsto εwrap atTop (𝓝 0)
  εenv_tendsto : Tendsto εenv atTop (𝓝 0)
  εfirst_tendsto : Tendsto εfirst atTop (𝓝 0)
  εjoint_tendsto : Tendsto εjoint atTop (𝓝 0)
  cwrap_nonneg : 0 ≤ cwrap
  cenv_nonneg : 0 ≤ cenv
  cfirst_nonneg : 0 ≤ cfirst
  cjoint_nonneg : 0 ≤ cjoint
  wrap : AtCounterexamples Y fun L A =>
    2 ^ k * Yν L A ≤ Jν L A + (2 ^ k * W + εwrap L) * Y L A + remainder cwrap L A
  frame : AtCounterexamples Y fun L A =>
    Jν L A ≤ Yν L A + ((VL L A - eL L A) + (VR L A - eR L A)) / 2
  envelopeL : AtCounterexamples Y fun L A =>
    VL L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder cenv L A
  envelopeR : AtCounterexamples Y fun L A =>
    VR L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder cenv L A
  firstStage : AtCounterexamples Y fun L A =>
    (1 - L₀ - εfirst L) * Y L A - remainder cfirst L A ≤ Yfs L A
  joint : AtCounterexamples Y fun L A =>
    (2 ^ k - 1) * (Yfs L A - Yν L A) - (eL L A + eR L A) / 2 ≤
      (2 ^ k * H - 1 + εjoint L) * Y L A + remainder cjoint L A

/-- The closing number of `cor:joint-closing`. -/
noncomputable def jointTheta (k : ℕ) (L₀ J W H : ℝ) : ℝ :=
  (1 - ((2 : ℝ) ^ k)⁻¹) * L₀ + J + W + H

namespace ClosingEstimates

variable {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}

/-- The coefficient of the recurrence at scale `L`. -/
noncomputable def coefficient (e : ClosingEstimates Y k L₀ J W H) (L : ℕ) : ℝ :=
  jointTheta k L₀ J W H +
    (((2 : ℝ) ^ k - 1) * e.εfirst L + e.εwrap L + e.εenv L + e.εjoint L) / 2 ^ k

/-- The combined remainder constant of the recurrence. -/
noncomputable def remainderConstant (e : ClosingEstimates Y k L₀ J W H) : ℝ :=
  (e.cwrap + e.cenv + e.cjoint + ((2 : ℝ) ^ k - 1) * e.cfirst) / 2 ^ k

theorem remainderConstant_nonneg (e : ClosingEstimates Y k L₀ J W H) :
    0 ≤ e.remainderConstant := by
  have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  unfold remainderConstant
  have := e.cwrap_nonneg
  have := e.cenv_nonneg
  have := e.cjoint_nonneg
  have := e.cfirst_nonneg
  apply div_nonneg _ (by positivity)
  nlinarith

theorem coefficient_tendsto (e : ClosingEstimates Y k L₀ J W H) :
    Tendsto e.coefficient atTop (𝓝 (jointTheta k L₀ J W H)) := by
  have h := (((e.εfirst_tendsto.const_mul ((2 : ℝ) ^ k - 1)).add e.εwrap_tendsto).add
    e.εenv_tendsto).add e.εjoint_tendsto
  have h' := (h.div_const ((2 : ℝ) ^ k)).const_add (jointTheta k L₀ J W H)
  unfold coefficient
  simpa only [mul_zero, add_zero, zero_div] using h'

/-- Algebra of the closing step at one counterexample. -/
theorem closing_step {M Y Yfs Yν Jν eL eR VL VR L₀ J W H εw εe εf εj rw re rf rj : ℝ}
    (hM : 0 < M) (hM1 : 1 ≤ M)
    (hwrap : M * Yν ≤ Jν + (M * W + εw) * Y + rw)
    (hframe : Jν ≤ Yν + ((VL - eL) + (VR - eR)) / 2)
    (hL : VL ≤ (M * J + εe) * Y + re) (hR : VR ≤ (M * J + εe) * Y + re)
    (hfirst : (1 - L₀ - εf) * Y - rf ≤ Yfs)
    (hjoint : (M - 1) * (Yfs - Yν) - (eL + eR) / 2 ≤ (M * H - 1 + εj) * Y + rj) :
    Y ≤ ((1 - M⁻¹) * L₀ + J + W + H + ((M - 1) * εf + εw + εe + εj) / M) * Y +
      (rw + re + rj + (M - 1) * rf) / M := by
  have hM0 : M ≠ 0 := hM.ne'
  have key : M * Y ≤ M * (((1 - M⁻¹) * L₀ + J + W + H + ((M - 1) * εf + εw + εe + εj) / M) * Y +
      (rw + re + rj + (M - 1) * rf) / M) := by
    have hexp : M * (((1 - M⁻¹) * L₀ + J + W + H + ((M - 1) * εf + εw + εe + εj) / M) * Y +
        (rw + re + rj + (M - 1) * rf) / M) =
        ((M - 1) * L₀ + M * J + M * W + M * H + (M - 1) * εf + εw + εe + εj) * Y +
          (rw + re + rj + (M - 1) * rf) := by
      field_simp
      ring
    rw [hexp]
    have hprod := mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr hM1)
    nlinarith [hwrap, hframe, hL, hR, hprod, hjoint]
  exact le_of_mul_le_mul_left key hM

/-- **Closing criterion with robust errors.** The five estimates imply the raw
comparison recurrence, with coefficient tending to the joint closing number. -/
theorem rawComparison (e : ClosingEstimates Y k L₀ J W H) :
    RawComparison Y e.coefficient e.remainderConstant := by
  have hM : (0 : ℝ) < 2 ^ k := by positivity
  filter_upwards [e.wrap, e.frame, e.envelopeL, e.envelopeR, e.firstStage, e.joint] with
    L hw hf hl hr hs hj
  intro C hC hind A hA hcounter
  have h := closing_step (M := (2 : ℝ) ^ k) hM (one_le_pow₀ (by norm_num)) (hw C hC hind A hA hcounter)
    (hf C hC hind A hA hcounter) (hl C hC hind A hA hcounter) (hr C hC hind A hA hcounter)
    (hs C hC hind A hA hcounter) (hj C hC hind A hA hcounter)
  have hrem : (remainder e.cwrap L A + remainder e.cenv L A + remainder e.cjoint L A +
      ((2 : ℝ) ^ k - 1) * remainder e.cfirst L A) / 2 ^ k =
      e.remainderConstant * (L : ℝ) ^ (-cancellationDecay) * density (blockScale * L) A := by
    unfold remainder remainderConstant
    field_simp
  rw [hrem] at h
  simpa only [coefficient, jointTheta] using h

end ClosingEstimates

/-- **Theorem C, conditional form at the level of the closing criterion.** The
reflection lower bound, the global second-density moment bound, and the five robust
estimates with a closing number below one give the power saving. -/
theorem powerSavingBound_of_closingEstimates
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H M : ℝ}
    (hθ : jointTheta k L₀ J W H < 1) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound Y M) (e : ClosingEstimates Y k L₀ J W H) :
    PowerSavingBound :=
  powerSavingBound_of_scaledEnergyEstimate
    (scaledEnergyEstimate_of_rawComparison hM e.remainderConstant_nonneg hθ hreflection
      hglobal e.rawComparison e.coefficient_tendsto)

end Sarkozy.Comparison
