module

public import Sarkozy.JointClosing.Allocation
public import Sarkozy.ClassBoundsPaper.Polynomial

@[expose] public section

/-!
# The joint bound `JB` from the class bounds and the joint mean allocations

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`; `paper/sections/24a_joint_mean.tex`,
`prop:joint-middle-mean`, `prop:joint-upper-mean`; `paper/sections/32_four_routes_closing.tex`,
`eq:final-joint-closing`, `cert:four-routes-closing`; `paper/sections/28_closing.tex`,
`prop:closing-data`(d).

B3's `JointClosing.JointBound D H` is the hypothesis of `cor:joint-closing`. The paper proves it by
expanding the comparison loss into selection terms (`lem:record:record-expansion`), bounding the
terms of the classes by energies of labelled positive diagonals with coefficients `w_i`
(`thm:envelopes`(i), `cor:envelope-costs`) and the others through (E1), expanding the mean energies
with the one-block credit `m₁` and retained energies `b_i Z_i` on the same diagonals
(`prop:record:mean-credit`), combining `(63 w_i − b_i) Z_i` first, and only then applying upper
prices `Z_i ≤ (u_i + o(1)) Y` (`cor:joint-closing`, last paragraph; end of the proof of
`prop:joint-middle-mean`).

* `JointAllocL D H`: B3's `JointAllocation` with a comparison constant `κ L` that may depend on the
  scale (the part of the comparison polynomial on no shared diagonal is evaluated at each scale).
  `JointAllocL.jointBound`: `JointBound D H` (B3's proof, with `κ L`).
* **`jointBound_of_classes`**: `JointBound D H` from
  - (J1′) the term-level comparison bound
    `∑_ω |I_ω| ≤ ∑_i w_i Z_i + (κ′_L + o(1)) Y + rem` (`hterms`; the energy-level class bounds of
    `thm:envelopes`(i) and `cor:envelope-costs`, and (E1) off the classes), which gives the energy
    level comparison through the record expansion (`energy_sub_eq_sum_selections`);
  - (J2) the mean expansion with `m₁` and `b_i Z_i` (`prop:record:mean-credit`), (J3) the upper
    prices of the diagonals (`lem:bracket-energy`, (E1));
  - the residual gates `b_i ≤ (2^k − 1) w_i` (the 192 residuals of `cert:four-routes-closing`);
  - (G1) `κ′_L + ∑_i w_i u_i ≤ 𝓔` (the complete polynomial at the upper prices,
    `prop:closing-data`(d)); (G2) `∑_i b_i u_i ≥ Δ` (the joint mean allocations); and
    `(2^k − 1)𝓔 − Δ ≤ 2^k H − 1 + m₁`.
* **`jointBound_target`**: the case `k = 6`, `H = targetLedger.jointConstant`, `𝓔 = targetLedger.E`,
  `Δ = 64(Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u)`, `m₁ = targetLedger.m₁`; the last gate is an identity
  (`jointConstant_gate`).
* **`jointBound_target_of_classInputs`**: (G1) from the class inputs `CI` and upper data `PD` of
  this package: if at every scale the decomposition at upper prices is at most the complete
  polynomial `Ψ(π̂, ŷ)` of `PD` (`hG1`), then `PolynomialData.Psi_le_E` gives (G1).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetLedger)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **A joint allocation with a scale-dependent comparison constant** (`cor:joint-closing`): B3's
`JointAllocation` with `κ : ℕ → ℝ`. -/
structure JointAllocL (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (H : ℝ) where
  ι : ℕ → Type
  [ιFintype : ∀ L, Fintype (ι L)]
  Z : ∀ L, Finset ℤ → ι L → ℝ
  c : ∀ L, ι L → ℝ
  b : ∀ L, ι L → ℝ
  κ : ℕ → ℝ
  m₁ : ℝ
  /-- (J1) The comparison loss at energy level. -/
  comparison : ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (2 ^ Fintype.card E - 1) * (energyFirst D.FS.lam (blockLift m₀ blk p) L A -
          energyComparison D.CL.ν (blockLift m₀ blk p) L A) ≤
        ∑ i, c L i * Z L A i + (κ L + ε₁ L) * D.Y L A + remainder c₁ L A
  /-- (J2) The mean energies at energy level. -/
  mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (m₁ - ε₂ L) * D.Y L A + ∑ i, b L i * Z L A i - remainder c₂ L A ≤
        (energyMean (blockLift m₀ blk p) D.ME.ML L A +
          energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2
  u : ∀ L, ι L → ℝ
  v : ∀ L, ι L → ℝ
  /-- (J3) The upper prices of the shared diagonals. -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
    (∀ L, ∑ i, (c L i - b L i) * v L i ≤ V) ∧ ∃ r : ∀ L, Finset ℤ → ι L → ℝ,
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ i, Z L A i ≤ (u L i + ε₃ L * v L i) * D.Y L A + r L A i) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ i, (c L i - b L i) * r L A i ≤ remainder c₃ L A)
  /-- (J4) The residual coefficients are nonnegative. -/
  resid_nonneg : ∀ L i, b L i ≤ c L i
  /-- (J4) The evaluated residual series closes with the joint constant `H`, at every scale. -/
  gate : ∀ L, κ L + ∑ i, (c L i - b L i) * u L i ≤ 2 ^ Fintype.card E * H - 1 + m₁

attribute [instance] JointAllocL.ιFintype

omit [DecidableEq P] in
/-- **The joint bound from a joint allocation** (`cor:joint-closing`), B3's
`JointAllocation.jointBound` with `κ L`. -/
theorem JointAllocL.jointBound {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {H : ℝ}
    (JA : JointAllocL D H) : JointBound D H := by
  obtain ⟨ε₁, hε₁, c₁, hc₁, h1⟩ := JA.comparison
  obtain ⟨ε₂, hε₂, c₂, hc₂, h2⟩ := JA.mean
  obtain ⟨ε₃, hε₃0, hε₃, V, c₃, hc₃, hV, r, h3, h3r⟩ := JA.upper
  refine ⟨fun L => ε₁ L + ε₂ L + ε₃ L * V, ?_, c₁ + c₂ + c₃, by positivity, ?_⟩
  · have := (hε₁.add hε₂).add (hε₃.mul_const V)
    simpa only [add_zero, zero_mul] using this
  · unfold Param.AtCounterexamples at h1 h2 h3 h3r ⊢
    filter_upwards [h1, h2, h3, h3r] with L hL1 hL2 hL3 hL3r
    intro C hC hk A hAd hY
    have hYpos := Param.counterexample_pos (Params.ofDecay a) hC hY
    have e1 := hL1 C hC hk A hAd hY
    have e2 := hL2 C hC hk A hAd hY
    have e3 := hL3 C hC hk A hAd hY
    have e3r := hL3r C hC hk A hAd hY
    have hres : ∑ i, (JA.c L i - JA.b L i) * JA.Z L A i ≤
        (∑ i, (JA.c L i - JA.b L i) * JA.u L i) * D.Y L A +
          ε₃ L * (∑ i, (JA.c L i - JA.b L i) * JA.v L i) * D.Y L A +
          ∑ i, (JA.c L i - JA.b L i) * r L A i := by
      have hterm : ∀ i, (JA.c L i - JA.b L i) * JA.Z L A i ≤
          (JA.c L i - JA.b L i) * JA.u L i * D.Y L A +
            ε₃ L * ((JA.c L i - JA.b L i) * JA.v L i) * D.Y L A +
            (JA.c L i - JA.b L i) * r L A i := by
        intro i
        have hcb : 0 ≤ JA.c L i - JA.b L i := sub_nonneg.mpr (JA.resid_nonneg L i)
        have := mul_le_mul_of_nonneg_left (e3 i) hcb
        nlinarith
      calc _ ≤ ∑ i, ((JA.c L i - JA.b L i) * JA.u L i * D.Y L A +
            ε₃ L * ((JA.c L i - JA.b L i) * JA.v L i) * D.Y L A +
            (JA.c L i - JA.b L i) * r L A i) := sum_le_sum fun i _ => hterm i
        _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← mul_sum]
    have hsplit : ∑ i, JA.c L i * JA.Z L A i - ∑ i, JA.b L i * JA.Z L A i =
        ∑ i, (JA.c L i - JA.b L i) * JA.Z L A i := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    have hgate := mul_le_mul_of_nonneg_right (JA.gate L) hYpos.le
    have hVY := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hV L) (hε₃0 L)) hYpos.le
    rw [JointClosing.remainder_add, JointClosing.remainder_add]
    nlinarith

theorem remainder_smul (k c : ℝ) (L : ℕ) (A : Finset ℤ) :
    remainder (k * c) L A = k * remainder c L A := by
  unfold remainder
  ring

/-- The joint gate of the ledger is an identity:
`(2^6 − 1)𝓔 − 64(Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u) = 2^6 H − 1 + m₁` for
`H = jointConstant` (`eq:final-joint-closing`). -/
theorem jointConstant_gate (l : PrimitiveLedger) :
    (2 ^ 6 - 1) * l.E - 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) = 2 ^ 6 * l.jointConstant - 1 + l.m₁ := by
  unfold PrimitiveLedger.jointConstant
  ring

omit [DecidableEq P] in
/-- **`JointBound` from the class bounds at energy level and the joint mean allocations**
(`cor:joint-closing`; see the module docstring for the inputs). -/
theorem jointBound_of_classes (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {H 𝓔 Δ : ℝ}
    (ι : ℕ → Type) [∀ L, Fintype (ι L)] (Z : ∀ L, Finset ℤ → ι L → ℝ) (w b u v : ∀ L, ι L → ℝ)
    (κ' : ℕ → ℝ) (m₁ : ℝ)
    (hterms : ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
          ∑ i, w L i * Z L A i + (κ' L + ε₁ L) * D.Y L A + remainder c₁ L A)
    (hmean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (m₁ - ε₂ L) * D.Y L A + ∑ i, b L i * Z L A i - remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (hupper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
      (∀ L, ∑ i, ((2 ^ Fintype.card E - 1) * w L i - b L i) * v L i ≤ V) ∧
      ∃ r : ∀ L, Finset ℤ → ι L → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∀ i, Z L A i ≤ (u L i + ε₃ L * v L i) * D.Y L A + r L A i) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ i, ((2 ^ Fintype.card E - 1) * w L i - b L i) * r L A i ≤ remainder c₃ L A))
    (hresid : ∀ L i, b L i ≤ (2 ^ Fintype.card E - 1) * w L i)
    (hG1 : ∀ L, κ' L + ∑ i, w L i * u L i ≤ 𝓔)
    (hG2 : ∀ L, Δ ≤ ∑ i, b L i * u L i)
    (hH : (2 ^ Fintype.card E - 1) * 𝓔 - Δ ≤ 2 ^ Fintype.card E * H - 1 + m₁) :
    JointBound D H := by
  have hk : (0 : ℝ) ≤ 2 ^ Fintype.card E - 1 := by
    have : (1 : ℝ) ≤ 2 ^ Fintype.card E := one_le_pow₀ (by norm_num)
    linarith
  refine JointAllocL.jointBound (D := D) (H := H)
    { ι := ι, Z := Z, c := fun L i => (2 ^ Fintype.card E - 1) * w L i, b := b,
      κ := fun L => (2 ^ Fintype.card E - 1) * κ' L, m₁ := m₁, comparison := ?_, mean := hmean,
      u := u, v := v, upper := hupper, resid_nonneg := hresid, gate := ?_ }
  · obtain ⟨ε₁, hε₁, c₁, hc₁, h1⟩ := hterms
    have hlim : Tendsto (fun L => (2 ^ Fintype.card E - 1) * ε₁ L) atTop (𝓝 0) := by
      simpa using hε₁.const_mul ((2 : ℝ) ^ Fintype.card E - 1)
    refine ⟨fun L => (2 ^ Fintype.card E - 1) * ε₁ L, hlim, (2 ^ Fintype.card E - 1) * c₁,
      mul_nonneg hk hc₁, ?_⟩
    unfold Param.AtCounterexamples at h1 ⊢
    filter_upwards [h1] with L hL
    intro C hC hkk A hAd hY
    have e1 := hL C hC hkk A hAd hY
    have hexp := energy_sub_eq_sum_selections reservedCut (D.nu_eq L) (D.GB.lam_sym L)
      (fun b t => isSymmetricAt_symPart _ _) (fun b t => isSkewAt_skewPart _ _)
      (blockLift m₀ blk p L A)
    have hnueq : energyComparison D.CL.ν (blockLift m₀ blk p) L A =
        diagonalIntegral (tensorLaw (D.CL.ν L)) (blockLift m₀ blk p L A) :=
      Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
    have hlameq : energyFirst D.FS.lam (blockLift m₀ blk p) L A =
        diagonalIntegral (tensorLaw (D.FS.lam L)) (blockLift m₀ blk p L A) :=
      Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
    have hdiff : energyFirst D.FS.lam (blockLift m₀ blk p) L A -
        energyComparison D.CL.ν (blockLift m₀ blk p) L A ≤
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
          |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| := by
      rw [hnueq, hlameq]
      have h' : diagonalIntegral (tensorLaw (D.FS.lam L)) (blockLift m₀ blk p L A) -
          diagonalIntegral (tensorLaw (D.CL.ν L)) (blockLift m₀ blk p L A) =
          -∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω := by
        rw [← hexp]
        ring
      rw [h']
      exact (neg_le_abs _).trans (Finset.abs_sum_le_sum_abs _ _)
    have hstep := mul_le_mul_of_nonneg_left (hdiff.trans e1) hk
    have e2 : (2 ^ Fintype.card E - 1) * (∑ i, w L i * Z L A i + (κ' L + ε₁ L) * D.Y L A +
        remainder c₁ L A) = ∑ i, (2 ^ Fintype.card E - 1) * w L i * Z L A i +
        ((2 ^ Fintype.card E - 1) * κ' L + (2 ^ Fintype.card E - 1) * ε₁ L) * D.Y L A +
        (2 ^ Fintype.card E - 1) * remainder c₁ L A := by
      rw [mul_add, mul_add, mul_sum]
      simp only [mul_assoc]
      ring
    rw [remainder_smul]
    linarith
  · intro L
    have h1 := mul_le_mul_of_nonneg_left (hG1 L) hk
    have h2 := hG2 L
    have e : ∑ i, ((2 ^ Fintype.card E - 1) * w L i - b L i) * u L i =
        (2 ^ Fintype.card E - 1) * ∑ i, w L i * u L i - ∑ i, b L i * u L i := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    rw [e]
    nlinarith

/-- The joint mean allocations of the ledger (`prop:joint-middle-mean`, `prop:joint-upper-mean`):
`Δ = 64(Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u)`. -/
noncomputable def ledgerDelta (l : PrimitiveLedger) : ℝ :=
  64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) + l.deltaUpper - l.upperError)

omit [DecidableEq P] in
/-- **`JB` for the ledger** (`cor:joint-closing` at `k = 6`, `H = targetLedger.jointConstant`,
`eq:final-joint-closing`): `jointBound_of_classes` with `𝓔 = targetLedger.E`,
`Δ = ledgerDelta targetLedger` and `m₁ = targetLedger.m₁`; the closing gate is
`jointConstant_gate`. -/
theorem jointBound_target (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hcard : Fintype.card E = 6)
    (ι : ℕ → Type) [∀ L, Fintype (ι L)] (Z : ∀ L, Finset ℤ → ι L → ℝ) (w b u v : ∀ L, ι L → ℝ)
    (κ' : ℕ → ℝ)
    (hterms : ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
          ∑ i, w L i * Z L A i + (κ' L + ε₁ L) * D.Y L A + remainder c₁ L A)
    (hmean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ i, b L i * Z L A i - remainder c₂ L A ≤
          (energyMean (blockLift m₀ blk p) D.ME.ML L A +
            energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2)
    (hupper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
      (∀ L, ∑ i, (63 * w L i - b L i) * v L i ≤ V) ∧ ∃ r : ∀ L, Finset ℤ → ι L → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∀ i, Z L A i ≤ (u L i + ε₃ L * v L i) * D.Y L A + r L A i) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ i, (63 * w L i - b L i) * r L A i ≤ remainder c₃ L A))
    (hresid : ∀ L i, b L i ≤ 63 * w L i)
    (hG1 : ∀ L, κ' L + ∑ i, w L i * u L i ≤ targetLedger.E)
    (hG2 : ∀ L, ledgerDelta targetLedger ≤ ∑ i, b L i * u L i) :
    JointBound D targetLedger.jointConstant := by
  have h63 : (2 : ℝ) ^ Fintype.card E - 1 = 63 := by rw [hcard]; norm_num
  refine jointBound_of_classes D ι Z w b u v κ' targetLedger.m₁ hterms hmean (by
    rw [h63]; exact hupper) (by rw [h63]; exact hresid) hG1 hG2 ?_
  rw [hcard, ← jointConstant_gate targetLedger, ledgerDelta]

omit [DecidableEq P] in
/-- **(G1) from the class polynomial of this package** (`prop:closing-data`(d)): if at every scale
the comparison constant off the shared diagonals and the diagonal weights at their upper prices are
at most the complete polynomial `Ψ(π̂, ŷ)` of the upper data `PD` (`hΨdec`), then (G1) holds with
`𝓔 = targetLedger.E` (`PolynomialData.Psi_le_E`). -/
theorem G1_of_polynomialData {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {CI : ClassInputs D.CL} (PD : PolynomialData CI) {ι : ℕ → Type} [∀ L, Fintype (ι L)]
    (w u : ∀ L, ι L → ℝ) (κ' : ℕ → ℝ) (hΨdec : ∀ L, κ' L + ∑ i, w L i * u L i ≤ (PD.U L).Psi) :
    ∀ L, κ' L + ∑ i, w L i * u L i ≤ targetLedger.E :=
  fun L => (hΨdec L).trans (PD.Psi_le_E L)

end Sarkozy.ClassBoundsPaper
