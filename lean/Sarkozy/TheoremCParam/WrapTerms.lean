module

public import Sarkozy.TheoremC.WrapTerms
public import Sarkozy.TheoremCParam.Main

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-! ## Brackets add -/

/-! ## Stage 2: matrices -/

/-! ## Stage 2: the reduction of the fully wrapping term -/

/-! ## Stage 1: the envelope of the wrapping terms -/

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] (D : ComparisonData a m₀ p pr h E)

/-- The law `M_𝔟 = Ñ_𝔟 + ∑_t (π̃^s_{𝔟,t} D^s_{𝔟,t} + π̃^a_{𝔟,t} D^a_{𝔟,t})` dominating `ν_𝔟`
in the wrapping terms. -/
noncomputable def wrapEnvelope (L : ℕ) (b : PaperAtom J L) : AtomMeasure m₀ p L b :=
  D.GB.N L b + ∑ t, (D.CL.πt L b t .sym • D.CL.D L b t .sym +
    D.CL.πt L b t .skew • D.CL.D L b t .skew)

omit [DecidableEq P] in
/-- **The brackets of (CP3) and (CP4) add up**: `(M_𝔟 ν_𝔟; ν_𝔟* M_𝔟) ⪰_ι 0`. -/
theorem wrapEnvelope_bracket (L : ℕ) (b : PaperAtom J L) :
    reservedCut.Bracket (D.wrapEnvelope L b) (D.CL.ν L b) (D.wrapEnvelope L b) := by
  rw [D.nu_eq L b]
  unfold wrapEnvelope
  apply bracket_add (D.GB.bracket L b)
  apply bracket_sum
  intro t _
  exact bracket_add (D.CL.bracket L b t .sym) (D.CL.bracket L b t .skew)

omit [DecidableEq P] in
/-- The price of `M − Ñ` is at most `S + A`. -/
theorem wrapEnvelope_price (L : ℕ) :
    ∑ b, ∑ t, (D.CL.π L b t .sym + D.CL.π L b t .skew) ≤ D.CL.S + D.CL.A := by
  have h : ∑ b, ∑ t, (D.CL.π L b t .sym + D.CL.π L b t .skew) =
      ∑ b, symTotal (D.CL.π L) b + ∑ b, skewTotal (D.CL.π L) b := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro b _
    rw [sum_add_distrib]
    rfl
  rw [h]
  exact add_le_add (D.CL.S_total L) (D.CL.A_total L)

/-! ## Stage 3: the fixed-interval envelope energies give the wrapping-term bound -/

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- `V'_L(𝒮)`: the single-half random-inclusion energy under `⊗_𝔟 M_𝔟` of the fixed-interval
source half-function of `𝒮`. -/
noncomputable def wrapInclusionEnergyL (S : Finset E) (L : ℕ) (A : Finset ℤ) : ℝ :=
  wrapInclusionEnergy m₀ p pr h L D.S.index.t (D.wrapEnvelope L)
    (wrapSourceHalf m₀ p pr h hcop D.S.Q.u L A S)

/-- `V'_R(𝒮)`: the same for the fixed-interval target half-function. -/
noncomputable def wrapInclusionEnergyR (S : Finset E) (L : ℕ) (A : Finset ℤ) : ℝ :=
  wrapInclusionEnergy m₀ p pr h L D.S.index.t (D.wrapEnvelope L)
    (wrapTargetHalf m₀ p pr h hcop D.S.Q.w L A S)

/-- The fixed-interval factor `κ_e^{2θ/d} R_I = K^{2θ/d} R_I` of one active query
(`lem:envelope-energy` with `κ_e = K`, `d = 72`). -/
noncomputable def fixedIntervalFactor : ℝ :=
  (blockScale : ℝ) ^ (2 * densityExponent / 72) * D.S.index.R_I

/-- **`lem:envelope-energy` at fixed intervals** (`κ_e = K`) for `M_𝔟 = Ñ_𝔟 + Q_𝔟`,
`Q_𝔟 = ∑_t (π̃^s D^s + π̃^a D^a)` of total price `T_Q ≤ S + A` (`wrapEnvelope_price`), robustly:
for every nonempty `𝒮`, `V'_L(𝒮), V'_R(𝒮) ≤ (B e^{S+A} (K^{2θ/d} R_I)^{|𝒮|} + o(1)) Y`. -/
def FixedIntervalEnvelopeEnergies : Prop :=
  ∃ εf : ℕ → ℝ, (∀ L, 0 ≤ εf L) ∧ Tendsto εf atTop (𝓝 0) ∧ ∃ cf : ℝ, 0 ≤ cf ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      D.wrapInclusionEnergyL hcop S L A ≤
          (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A ∧
      D.wrapInclusionEnergyR hcop S L A ≤
          (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A)

omit [DecidableEq P] in
/-- `K^{-1} · K^{2θ/d} R_I = R_I K^{2θ/d − 1}`, the ratio of `W`. -/
theorem inv_card_mul_fixedIntervalFactor :
    (Fintype.card (ZMod blockScale) : ℝ)⁻¹ * D.fixedIntervalFactor = D.wrapRatio := by
  have hK : (blockScale : ℝ) ≠ 0 := by norm_num [blockScale]
  unfold fixedIntervalFactor wrapRatio
  rw [ZMod.card, Real.rpow_sub_one hK]
  field_simp

/-- **The wrapping terms from the fixed-interval envelope energies**:
`lem:record:common-mean`(b) (`abs_wrapForm_le`), the bracket of `M_𝔟` (`wrapEnvelope_bracket`)
and `lem:envelope-energy` at fixed intervals give the hypothesis `WrappingTerms` of Theorem C,
with the same relative error and remainder constant. -/
theorem wrappingTerms_of_envelope (hf : D.FixedIntervalEnvelopeEnergies hcop) :
    D.WrappingTerms hcop := by
  obtain ⟨εf, hεf0, hεf, cf, hcf, hV⟩ := hf
  refine ⟨εf, hεf0, hεf, cf, hcf, ?_⟩
  filter_upwards [hV] with L hL
  intro C hC hind A hA hcounter S hS
  obtain ⟨hVL, hVR⟩ := hL C hC hind A hA hcounter S hS
  have hY0 : 0 ≤ D.Y L A := nonneg_of_counterexample hC hcounter
  have hF0 : 0 ≤ D.fixedIntervalFactor :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) D.S.index.hR_I
  have hr0 : 0 ≤ remainder cf L A := remainder_nonneg' hcf L A
  have hBd0 : 0 ≤ (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) *
      D.Y L A + remainder cf L A := by
    have := D.B_nonneg
    have := hεf0 L
    positivity
  have hab := abs_wrapForm_le m₀ p pr h hcop D.S.index.μ D.S.index.hμ D.S.index.hμ1 D.S.index.t
    D.S.index.hnorm D.S.Q.u D.S.Q.w D.CL.ν D.wrapEnvelope D.wrapEnvelope_bracket L A S
  have hsq : Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
      Real.sqrt (D.wrapInclusionEnergyR hcop S L A) ≤
      (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
        remainder cf L A := by
    calc Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
          Real.sqrt (D.wrapInclusionEnergyR hcop S L A)
        ≤ Real.sqrt ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) *
              D.Y L A + remainder cf L A) *
            Real.sqrt ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card +
              εf L) * D.Y L A + remainder cf L A) :=
          mul_le_mul (Real.sqrt_le_sqrt hVL) (Real.sqrt_le_sqrt hVR) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hBd0
  have hk0 : 0 ≤ (Fintype.card (ZMod blockScale) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hk1 : (Fintype.card (ZMod blockScale) : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast Fintype.card_pos
  have hkS : ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card ≤ 1 := pow_le_one₀ hk0 hk1
  have hkS0 : 0 ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card := pow_nonneg hk0 _
  calc |wrapForm m₀ p pr h hcop D.S.index.μ D.S.Q.u D.S.Q.w D.CL.ν L A S S|
      ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
          (Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
            Real.sqrt (D.wrapInclusionEnergyR hcop S L A)) := hab
    _ ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
          ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A) := mul_le_mul_of_nonneg_left hsq hkS0
    _ = D.B * Real.exp (D.CL.S + D.CL.A) *
            ((Fintype.card (ZMod blockScale) : ℝ)⁻¹ * D.fixedIntervalFactor) ^ S.card * D.Y L A +
          ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
              (εf L * D.Y L A + remainder cf L A) := by
        rw [mul_pow]
        ring
    _ ≤ (D.B * Real.exp (D.CL.S + D.CL.A) * D.wrapRatio ^ S.card + εf L) * D.Y L A +
          remainder cf L A := by
        rw [D.inv_card_mul_fixedIntervalFactor]
        have h1 : ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
            (εf L * D.Y L A + remainder cf L A) ≤ εf L * D.Y L A + remainder cf L A :=
          mul_le_of_le_one_left (add_nonneg (mul_nonneg (hεf0 L) hY0) hr0) hkS
        linarith

end ComparisonData

end Sarkozy.TheoremCParam
