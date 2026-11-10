module

public import Sarkozy.Param.RelativeErrors
public import Sarkozy.Comparison.Criterion

@[expose] public section

/-!
# The closing criterion with robust errors, for general exponents

Parametrized copy of `Sarkozy/Comparison/Criterion.lean`: the scalar part of
`thm:record:criterion` and its joint form `cor:joint-closing`
(`paper/sections/11_comparison_proof.tex`), as reused by `thm:density:induction`
(`paper/sections/31_density_induction_upgrade.tex`: "Equivalently, `Θ` may be computed by the
joint closing of `cor:joint-closing`"), at the exponents `P : Params`.

* `AtCounterexamples P`: at every least normalized counterexample of every sufficiently large
  scale, uniformly in `C ≥ 1`, for the bound `Y ≤ C L^{-a} α^ϑ` (`def:record:counterexample`
  with the exponents of `P`).
* `remainder P c L A = c L^{-σ} α`.
* `ClosingEstimates P`: the five robust estimates (wrap, frame, envelopes, first stage, joint).
* `powerSavingBound_of_closingEstimates`: **the parametrized endgame**. For every `P` with
  `P.Valid`, reflection, the global moment bound and the five estimates with joint closing
  number `jointTheta k L₀ J W H < 1` give `s(N) ≤ C N^{1 − a/(72 − ϑ)}`.

The closing number `Sarkozy.Comparison.jointTheta` and the algebra lemma
`Sarkozy.Comparison.ClosingEstimates.closing_step` do not involve the exponents and are reused.
-/

open Filter
open scoped Topology

namespace Sarkozy.Param

open Sarkozy.Comparison (jointTheta)

variable (P : Params)

/-- `Q L A` holds at every least normalized counterexample `(L, A)` of every sufficiently large
scale `L`, uniformly in the induction constant `C ≥ 1`, for the exponents `P`
(`def:record:counterexample`; `Sarkozy.Comparison.AtCounterexamples` in general). -/
def AtCounterexamples (Y : ℕ → Finset ℤ → ℝ) (Q : ℕ → Finset ℤ → Prop) : Prop :=
  ∀ᶠ L : ℕ in atTop, ∀ C : ℝ, 1 ≤ C →
    (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt P Y C k) →
    ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
      C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A →
      Q L A

/-- A density-linear analytic remainder `c L^{-σ} α` (`Sarkozy.Comparison.remainder` in
general). -/
noncomputable def remainder (c : ℝ) (L : ℕ) (A : Finset ℤ) : ℝ :=
  c * (L : ℝ) ^ (-P.cancellationDecay) * density (P.blockScale * L) A

/-- The energy is positive at a counterexample (`Sarkozy.TheoremC.counterexample_pos` in general;
`Sarkozy.TheoremC.nonneg_of_counterexample` and `energy_nonneg_of_counter` are its weak forms). -/
theorem counterexample_pos {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} (hC : 1 ≤ C) {L : ℕ}
    {A : Finset ℤ}
    (h : C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A) :
    0 < Y L A := by
  have h0 : 0 ≤ C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)
  linarith

/-- A pointwise estimate holds in particular at counterexamples. -/
theorem AtCounterexamples.of_forall {Y : ℕ → Finset ℤ → ℝ} {Q : ℕ → Finset ℤ → Prop}
    (h : ∀ L A, Q L A) : AtCounterexamples P Y Q :=
  Eventually.of_forall fun L _ _ _ A _ _ => h L A

/-- The five robust estimates of the closing criterion (`thm:record:criterion`,
`cor:joint-closing`) for `k` queries, with closing data `L₀, J, W, H`, at the exponents `P`
(`Sarkozy.Comparison.ClosingEstimates` in general). They are hypotheses here. -/
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
  wrap : AtCounterexamples P Y fun L A =>
    2 ^ k * Yν L A ≤ Jν L A + (2 ^ k * W + εwrap L) * Y L A + remainder P cwrap L A
  frame : AtCounterexamples P Y fun L A =>
    Jν L A ≤ Yν L A + ((VL L A - eL L A) + (VR L A - eR L A)) / 2
  envelopeL : AtCounterexamples P Y fun L A =>
    VL L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder P cenv L A
  envelopeR : AtCounterexamples P Y fun L A =>
    VR L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder P cenv L A
  firstStage : AtCounterexamples P Y fun L A =>
    (1 - L₀ - εfirst L) * Y L A - remainder P cfirst L A ≤ Yfs L A
  joint : AtCounterexamples P Y fun L A =>
    (2 ^ k - 1) * (Yfs L A - Yν L A) - (eL L A + eR L A) / 2 ≤
      (2 ^ k * H - 1 + εjoint L) * Y L A + remainder P cjoint L A

namespace ClosingEstimates

variable {P} {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}

/-- The coefficient of the recurrence at scale `L`. -/
noncomputable def coefficient (e : ClosingEstimates P Y k L₀ J W H) (L : ℕ) : ℝ :=
  jointTheta k L₀ J W H +
    (((2 : ℝ) ^ k - 1) * e.εfirst L + e.εwrap L + e.εenv L + e.εjoint L) / 2 ^ k

/-- The combined remainder constant of the recurrence. -/
noncomputable def remainderConstant (e : ClosingEstimates P Y k L₀ J W H) : ℝ :=
  (e.cwrap + e.cenv + e.cjoint + ((2 : ℝ) ^ k - 1) * e.cfirst) / 2 ^ k

theorem remainderConstant_nonneg (e : ClosingEstimates P Y k L₀ J W H) :
    0 ≤ e.remainderConstant := by
  have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  unfold remainderConstant
  have := e.cwrap_nonneg
  have := e.cenv_nonneg
  have := e.cjoint_nonneg
  have := e.cfirst_nonneg
  apply div_nonneg _ (by positivity)
  nlinarith

theorem coefficient_tendsto (e : ClosingEstimates P Y k L₀ J W H) :
    Tendsto e.coefficient atTop (𝓝 (jointTheta k L₀ J W H)) := by
  have h := (((e.εfirst_tendsto.const_mul ((2 : ℝ) ^ k - 1)).add e.εwrap_tendsto).add
    e.εenv_tendsto).add e.εjoint_tendsto
  have h' := (h.div_const ((2 : ℝ) ^ k)).const_add (jointTheta k L₀ J W H)
  unfold coefficient
  simpa only [mul_zero, add_zero, zero_div] using h'

/-- **Closing criterion with robust errors** (`thm:record:criterion`, `cor:joint-closing`) at
the exponents `P`: the five estimates imply the raw comparison recurrence, with coefficient
tending to the joint closing number. -/
theorem rawComparison (e : ClosingEstimates P Y k L₀ J W H) :
    RawComparison P Y e.coefficient e.remainderConstant := by
  have hM : (0 : ℝ) < 2 ^ k := by positivity
  filter_upwards [e.wrap, e.frame, e.envelopeL, e.envelopeR, e.firstStage, e.joint] with
    L hw hf hl hr hs hj
  intro C hC hind A hA hcounter
  have h := Comparison.ClosingEstimates.closing_step (M := (2 : ℝ) ^ k) hM
    (one_le_pow₀ (by norm_num)) (hw C hC hind A hA hcounter)
    (hf C hC hind A hA hcounter) (hl C hC hind A hA hcounter) (hr C hC hind A hA hcounter)
    (hs C hC hind A hA hcounter) (hj C hC hind A hA hcounter)
  have hrem : (remainder P e.cwrap L A + remainder P e.cenv L A + remainder P e.cjoint L A +
      ((2 : ℝ) ^ k - 1) * remainder P e.cfirst L A) / 2 ^ k =
      e.remainderConstant * (L : ℝ) ^ (-P.cancellationDecay) *
        density (P.blockScale * L) A := by
    unfold remainder remainderConstant
    field_simp
  rw [hrem] at h
  simpa only [coefficient, jointTheta] using h

end ClosingEstimates

variable {P}

/-- **The parametrized endgame** (`thm:density:induction` in the joint form of
`cor:joint-closing`; `Sarkozy.Comparison.powerSavingBound_of_closingEstimates` in general).
For exponents `P` satisfying the side conditions `P.Valid`, the reflection lower bound
`α^{72} ≤ Y`, the global second-density moment bound (`lem:density:global-moment`, a
hypothesis) and the five robust closing estimates (hypotheses) with closing number below one
give `s(N) ≤ C N^{1 − a/(72 − ϑ)}`. Finite initialization, error absorption, the scalar
induction and the passage to cardinalities are proved. -/
theorem powerSavingBound_of_closingEstimates (hP : P.Valid)
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H M : ℝ}
    (hθ : jointTheta k L₀ J W H < 1) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound P Y M) (e : ClosingEstimates P Y k L₀ J W H) :
    PowerSavingBound P :=
  powerSavingBound_of_scaledEnergyEstimate hP
    (scaledEnergyEstimate_of_rawComparison hP hM e.remainderConstant_nonneg hθ hreflection
      hglobal e.rawComparison e.coefficient_tendsto)

/-- **The parametrized endgame, energy form**: the first conclusion `α^{72} ≤ Y ≤ C L^{-a} α^ϑ`
of `thm:density:induction`, under the hypotheses of `powerSavingBound_of_closingEstimates`. -/
theorem scaledEnergyEstimate_of_closingEstimates (hP : P.Valid)
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H M : ℝ}
    (hθ : jointTheta k L₀ J W H < 1) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound P Y M) (e : ClosingEstimates P Y k L₀ J W H) :
    ScaledEnergyEstimate P Y :=
  scaledEnergyEstimate_of_rawComparison hP hM e.remainderConstant_nonneg hθ hreflection
    hglobal e.rawComparison e.coefficient_tendsto

/-! ## Transfer between functionals that agree on admissible sets -/

theorem AtCounterexamples.transfer {Y Y' : ℕ → Finset ℤ → ℝ}
    (h : ∀ L A, Admissible (P.blockScale * L) A → Y L A = Y' L A)
    {Q : ℝ → ℕ → Finset ℤ → Prop} (hQ : AtCounterexamples P Y fun L A => Q (Y L A) L A) :
    AtCounterexamples P Y' fun L A => Q (Y' L A) L A := by
  filter_upwards [hQ] with L hL
  intro C hC hind A hA hcounter
  have hind' : ∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt P Y C k := by
    intro k hk hkL A' hA'
    rw [h k A' hA']
    exact hind k hk hkL A' hA'
  have hc : C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent <
      Y L A := by
    rw [h L A hA]
    exact hcounter
  have hq := hL C hC hind' A hA hc
  rwa [h L A hA] at hq

/-- The closing estimates only see the functional on admissible sets
(`Sarkozy.Comparison.ClosingEstimates.transfer` in general). -/
noncomputable def ClosingEstimates.transfer {Y Y' : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (h : ∀ L A, Admissible (P.blockScale * L) A → Y L A = Y' L A)
    (e : ClosingEstimates P Y k L₀ J W H) : ClosingEstimates P Y' k L₀ J W H where
  Yfs := e.Yfs
  Yν := e.Yν
  Jν := e.Jν
  eL := e.eL
  eR := e.eR
  VL := e.VL
  VR := e.VR
  εwrap := e.εwrap
  εenv := e.εenv
  εfirst := e.εfirst
  εjoint := e.εjoint
  cwrap := e.cwrap
  cenv := e.cenv
  cfirst := e.cfirst
  cjoint := e.cjoint
  εwrap_tendsto := e.εwrap_tendsto
  εenv_tendsto := e.εenv_tendsto
  εfirst_tendsto := e.εfirst_tendsto
  εjoint_tendsto := e.εjoint_tendsto
  cwrap_nonneg := e.cwrap_nonneg
  cenv_nonneg := e.cenv_nonneg
  cfirst_nonneg := e.cfirst_nonneg
  cjoint_nonneg := e.cjoint_nonneg
  wrap := AtCounterexamples.transfer h
    (Q := fun y L A => 2 ^ k * e.Yν L A ≤ e.Jν L A + (2 ^ k * W + e.εwrap L) * y +
      remainder P e.cwrap L A) e.wrap
  frame := AtCounterexamples.transfer h
    (Q := fun _ L A => e.Jν L A ≤ e.Yν L A + ((e.VL L A - e.eL L A) + (e.VR L A - e.eR L A)) / 2)
    e.frame
  envelopeL := AtCounterexamples.transfer h
    (Q := fun y L A => e.VL L A ≤ (2 ^ k * J + e.εenv L) * y + remainder P e.cenv L A)
    e.envelopeL
  envelopeR := AtCounterexamples.transfer h
    (Q := fun y L A => e.VR L A ≤ (2 ^ k * J + e.εenv L) * y + remainder P e.cenv L A)
    e.envelopeR
  firstStage := AtCounterexamples.transfer h
    (Q := fun y L A => (1 - L₀ - e.εfirst L) * y - remainder P e.cfirst L A ≤ e.Yfs L A)
    e.firstStage
  joint := AtCounterexamples.transfer h
    (Q := fun y L A => (2 ^ k - 1) * (e.Yfs L A - e.Yν L A) - (e.eL L A + e.eR L A) / 2 ≤
      (2 ^ k * H - 1 + e.εjoint L) * y + remainder P e.cjoint L A) e.joint

end Sarkozy.Param
