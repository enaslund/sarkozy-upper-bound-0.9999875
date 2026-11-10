module

public import Sarkozy.DensityDC.MixingP5
public import Sarkozy.Structured.ThetaChain

/-!
# The ϑ chain for `lem:record:density-dc`: the density-structured layers without `θ ≤ 1`

`density_structured_groups`, `density_structured_dc_scale`, `density_structured_dc_paper`,
`density_structured_dc_tailPrimes` and `density_structured_dc_P5` re-run on
`density_structured_reference_theta` (`Sarkozy/Structured/ThetaChain.lean`). The density-dc
step (`lem:record:density-dc`) does not depend on `θ`; only the final Jensen step of
`prop:record:density-structured` did. In each `_theta` theorem:
* `θ ≤ 1` is replaced by `2θ/72 ≤ 1` (true at `ϑ = densityExponent`,
  `two_mul_densityExponent_div_le`);
* the two-occurrence structure of `prop:density:production`
  (`31_density_induction_upgrade.tex:498`) enters as the named hypotheses `slotOf`
  (each query index occurs in exactly two changed slots) and `hindep`
  (`PairIndependent`: distinct indices are independent).

`paperExponents_theta` checks the exponent hypotheses at `(a, θ) = (decay, densityExponent)`.
At these exponents the `_theta` theorems apply in the counterexample form that
`atCounterexamples_of_isLeast` consumes.
-/

@[expose] public section

namespace Sarkozy.DensityDC

section GroupsTheta

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing

/-- `density_structured_groups` without `θ ≤ 1`. -/
theorem density_structured_groups_theta (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)] {Ω : Type}
      [Fintype Ω],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (_hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
      {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
      (_hcex : IsLeastCounterexample Yf a θ C0 L A) (_hθ : 0 < θ) (_hθ2 : 2 * (θ / 72) ≤ 1) (_ha :
          0 ≤ a)
      (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L) (_hY0 : Yf L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (μb : ∀ b, FiniteLaw (Slot → ZMod (joinModuli m₀ p b)))
      (_hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
      (_hR3 : SquareAffineInvariant (joinModuli m₀ p) μb)
      (T : Finset (J₀ ⊕ J)) (_hprime : ∀ j ∈ T, (joinModuli m₀ p j).Prime) {γ : ℝ}
      (_hγ : 0 ≤ γ) (_hmix : ∀ j ∈ T, ∀ v, IsGammaMixing (joinModuli m₀ p j) γ (μb j) {v})
      {C' : ℕ} (_hC' : 0 < C')
      (_hdiv : ∀ a : ResidueSpace (joinModuli m₀ p),
        (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
      (E : Finset (J₀ ⊕ J)) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ p j = qE * cE) (_hqE : Squarefree qE) (_hcE : IsSquare cE)
      (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ p k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, joinModuli m₀ p j = 1 ∧ M v = blockScale * L))
      (Q : ℝ) (gt : Ω → Slot → ResidueSpace (joinModuli m₀ p) → ResidueSpace (joinModuli m₀ p) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (joinModuli m₀ p) E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v))
          (c ω v) (M v) (stepR (joinModuli m₀ p) E (D0 v))
          (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (joinModuli m₀ p) E Q A D0 M c s ω v x)
      (_hun : ∀ v, ¬changed v → ∀ ω x,
        referenceEnergy (FiniteLaw.tensor μb) (gt ω v x) ≤ Yf L A)
      (_hrest : ∀ v, changed v → ∀ B : Finset ℤ,
        B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v) : ℕ) : ℤ) →
        referenceEnergy (FiniteLaw.tensor μb)
            (child (joinModuli m₀ p) E (paperCutoff (blockScale *
              stepEll (joinModuli m₀ p) E (D0 v) (M v))) B
              (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) ≤
          Yf (stepEll (joinModuli m₀ p) E (D0 v) (M v)) B)
      (_hQ1 : 1 ≤ Q) (_hQN : Q ≤ ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20))
      (_hcut : ∀ v, 2 * ⌊Q⌋₊ ≤ M v + 1 ∧ ⌊Q⌋₊ ^ 5 ≤ M v + 1)
      (_hlam : ∀ v, changed v →
        (((leastSquare (D0 v * ∏ j ∈ E, joinModuli m₀ p j) *
          (blockScale * stepScale blockScale (M v)
            (leastSquare (D0 v * ∏ j ∈ E, joinModuli m₀ p j))) : ℕ) : ℝ) / M v) ≤ 2)
      (_hQn : ∀ v, changed v →
        paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v)) ≤
          ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20))
      (_hHQ' : ∀ v, changed v → ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) ≤
        paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v)))
      (_hHQ : ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) *
        (∏ j ∈ E, joinModuli m₀ p j : ℕ) ≤ Q)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ)
      {I : Type} [Fintype I] [DecidableEq I] (_slotOf : I × Bool ≃ {v // changed v})
      (_hindep : Sarkozy.Structured.PairIndependent (joinModuli m₀ p) E A P ρ D0 M c s changed θ
          _slotOf),
      |structuredEnergy (FiniteLaw.tensor μb) P ρ
          (paperInputs (joinModuli m₀ p) E Q A D0 M c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ p) E D0 M L) (paperMeanDensity P A D0 M c s)
            changed a θ (density (blockScale * L) A) * Yf L A +
          (72 * (C' : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨Ci1, hCi1, hci1⟩ := input_moment_le_density 1 le_rfl ε hε
  obtain ⟨Ci71, hCi71, hci71⟩ := input_moment_le_density 71 (by norm_num) ε hε
  obtain ⟨Cm1, hCm1, hcm1⟩ := model_moment_le_fibre 1 le_rfl ε hε
  obtain ⟨Cm71, hCm71, hcm71⟩ := model_moment_le_fibre 71 (by norm_num) ε hε
  refine ⟨max Ci1 Cm1, max Ci71 Cm71, lt_max_of_lt_left hCi1, lt_max_of_lt_left hCi71, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ Ω _ hp hinj hpair Yf a θ C0 L A hcex hθ hθ2 ha hC0 hL hY0 M0 Qcl
    Qpre N0 N0' hsc hM0 μb hμb hR3 T hprime γ hγ hmix C' hC' hdiv E qE cE hDE hqE hcE hcE0 hcQ
    hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed _ hchg Q gt hgt hgu hun hrest hQ1
    hQN hcut hlam hQn hHQ' hHQ σ hσ hS1 I _ _ slotOf hindep
  set X : ℝ := (Fintype.card (ResidueSpace m₀) : ℝ) with hX
  set N : ℝ := ((blockScale * L : ℕ) : ℝ) with hN
  set α : ℝ := density (blockScale * L) A with hαdef
  set C1 := max Ci1 Cm1 with hC1
  set C71 := max Ci71 Cm71 with hC71
  set U := FiniteLaw.uniform (ResidueSpace (joinModuli m₀ p)) with hU
  have hK : (0 : ℝ) < blockScale := by norm_num [blockScale]
  have hL1 : 1 ≤ L := by omega
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLM : ∀ v, L ≤ M v := by
    intro v
    rcases hM v with h | h
    · rw [h]; exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    · rw [h]
  have hM1 : ∀ v, 1 ≤ M v := fun v => le_trans hL1 (hLM v)
  have hD0le : ∀ v, D0 v ≤ M0 := fun v => Nat.le_of_dvd (by omega) (hD0M v)
  have hLN : (L : ℝ) ≤ N := by
    rw [hN]
    exact_mod_cast Nat.le_mul_of_pos_left L (by norm_num [blockScale])
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (hL1'.trans hLN)
  have hα : 0 ≤ α := density_nonneg _ _
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hNe : 0 ≤ N ^ (ε / 20) := Real.rpow_nonneg hN0.le _
  have hpow20 : (N ^ ((1 : ℝ) / 20)) ^ ε = N ^ (ε / 20) := by
    rw [← Real.rpow_mul hN0.le]
    ring_nf
  have hQe : Q ^ ε ≤ N ^ (ε / 20) := by
    rw [← hpow20]
    exact Real.rpow_le_rpow (zero_le_one.trans hQ1) hQN hε.le
  have hQne : ∀ v, changed v →
      paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v)) ^ ε ≤ N ^ (ε / 20) := by
    intro v hv
    rw [← hpow20]
    apply Real.rpow_le_rpow _ (hQn v hv) hε.le
    unfold paperCutoff
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hC1i : Ci1 ≤ C1 := le_max_left _ _
  have hC1m : Cm1 ≤ C1 := le_max_right _ _
  have hC71i : Ci71 ≤ C71 := le_max_left _ _
  have hC71m : Cm71 ≤ C71 := le_max_right _ _
  have hC1 : 0 ≤ C1 := hCi1.le.trans hC1i
  have hC71' : 0 ≤ C71 := hCi71.le.trans hC71i
  -- the cited moment bounds, in the form of `density_dc_lift_moments`
  have hlift2 : ∀ ω v, U.moment 2
      (fun x => (input (joinModuli m₀ p) Q (Icc (c ω v + 1) (c ω v + M v)) (D0 v) (s ω v) A
        x).re) ≤ (M0 : ℝ) ^ 2 * (X ^ 2 * C1 * Q ^ ε * ((blockScale : ℝ) * α)) := by
    intro ω v
    have h := hci1 m₀ p hp hinj Q hQ1 (c ω v) hL1 (hLM v) (hcut v).1 (hcut v).2 (hD0le v)
      (s ω v) A
    simp only [show (2 * 1 : ℕ) = 2 from rfl, Nat.cast_ofNat] at h
    refine h.trans ?_
    gcongr
  have hlift142 : ∀ ω v, U.moment 142
      (fun x => (input (joinModuli m₀ p) Q (Icc (c ω v + 1) (c ω v + M v)) (D0 v) (s ω v) A
        x).re) ≤ (M0 : ℝ) ^ 142 * (X ^ 142 * C71 * Q ^ ε * ((blockScale : ℝ) * α)) := by
    intro ω v
    have h := hci71 m₀ p hp hinj Q hQ1 (c ω v) hL1 (hLM v) (hcut v).1 (hcut v).2 (hD0le v)
      (s ω v) A
    simp only [show (2 * 71 : ℕ) = 142 from rfl, Nat.cast_ofNat] at h
    refine h.trans ?_
    gcongr
  have hmod2 : ∀ ω v x, changed v → U.moment 2 (gt ω v x) ≤
      (X ^ 2 * C1 * N ^ (ε / 20) * 2) *
        fibreDensity (joinModuli m₀ p) E x (s ω v) A (c ω v) (M v) := by
    intro ω v x hv
    have h := hcm1 m₀ p hp hinj hpair E x (hD0 v) (s ω v) (hcop0 v) A (c ω v) (hM1 v) (hlam v hv)
    rw [hgt ω v x hv]
    simp only [show (2 * 1 : ℕ) = 2 from rfl, show (2 * 1 - 1 : ℕ) = 1 from rfl, Nat.cast_ofNat,
      pow_one] at h
    refine h.trans ?_
    have hfd : 0 ≤ fibreDensity (joinModuli m₀ p) E x (s ω v) A (c ω v) (M v) := by
      unfold fibreDensity
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hpc : 0 ≤ paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v)) ^ ε := by
      unfold paperCutoff
      exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    apply mul_le_mul_of_nonneg_right _ hfd
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hC1m (pow_nonneg hX0 _)) (hQne v hv) hpc
      (mul_nonneg (pow_nonneg hX0 _) hC1)
  have hmod142 : ∀ ω v x, changed v → U.moment 142 (gt ω v x) ≤
      (X ^ 142 * C71 * N ^ (ε / 20) * 2 ^ 141) *
        fibreDensity (joinModuli m₀ p) E x (s ω v) A (c ω v) (M v) := by
    intro ω v x hv
    have h := hcm71 m₀ p hp hinj hpair E x (hD0 v) (s ω v) (hcop0 v) A (c ω v) (hM1 v)
      (hlam v hv)
    rw [hgt ω v x hv]
    simp only [show (2 * 71 : ℕ) = 142 from rfl, show (2 * 71 - 1 : ℕ) = 141 from rfl,
      Nat.cast_ofNat] at h
    refine h.trans ?_
    have hfd : 0 ≤ fibreDensity (joinModuli m₀ p) E x (s ω v) A (c ω v) (M v) := by
      unfold fibreDensity
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hpc : 0 ≤ paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v)) ^ ε := by
      unfold paperCutoff
      exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    apply mul_le_mul_of_nonneg_right _ hfd
    apply mul_le_mul_of_nonneg_right _ (by norm_num)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hC71m (pow_nonneg hX0 _)) (hQne v hv) hpc
      (mul_nonneg (pow_nonneg hX0 _) hC71')
  have hᾱ : ∀ v, changed v → paperMeanDensity P A D0 M c s v ≤ (M0 : ℝ) * ((blockScale : ℝ) * α) :=
    fun v _ => paperMeanDensity_le P A D0 M c s v hL1 (hLM v) (hD0le v)
  have hH : 0 < N ^ ((1 : ℝ) / 40) := Real.rpow_pos_of_pos hN0 _
  have hdc0 := density_dc_lift_moments (joinModuli m₀ p) hpair μb hR3 T hprime hγ hmix hC' hdiv E
    P ρ hunif D0 hD0 hcop0 M hM1 c s changed Q
    (fun v => paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) gt hgt hgu hH
    hHQ' hHQ (by positivity) (by positivity) hlift2 hlift142 hmod2 hmod142 hᾱ (by positivity)
  -- the constant of `lem:record:density-dc`
  set Kα : ℝ := (blockScale : ℝ) * α with hKα
  set B2 : ℝ := 2 * ((M0 : ℝ) ^ 2 * (X ^ 2 * C1 * Q ^ ε * Kα)) +
    2 * ((X ^ 2 * C1 * N ^ (ε / 20) * 2) * ((M0 : ℝ) * Kα)) with hB2def
  set B : ℝ := max ((M0 : ℝ) ^ 142 * (X ^ 142 * C71 * Q ^ ε * Kα))
    ((X ^ 142 * C71 * N ^ (ε / 20) * 2 ^ 141) * ((M0 : ℝ) * Kα)) with hBdef
  set c2 : ℝ := 2 * (M0 : ℝ) ^ 2 * X ^ 2 * C1 * blockScale + 4 * X ^ 2 * C1 * M0 * blockScale
    with hc2def
  set c1 : ℝ := (M0 : ℝ) ^ 142 * X ^ 142 * C71 * blockScale +
    2 ^ 141 * X ^ 142 * C71 * M0 * blockScale with hc1def
  have hQe0 : 0 ≤ Q ^ ε := Real.rpow_nonneg (zero_le_one.trans hQ1) _
  have hKα0 : 0 ≤ Kα := mul_nonneg hK.le hα
  have hM00 : (0 : ℝ) ≤ M0 := Nat.cast_nonneg _
  have hB2 : 0 ≤ B2 := by positivity
  have hB0 : 0 ≤ B := le_max_of_le_left (by positivity)
  have hc2 : 0 ≤ c2 := by positivity
  have hc1 : 0 ≤ c1 := by positivity
  have hB2le : B2 ≤ c2 * N ^ (ε / 20) * α := by
    have key := mul_le_mul_of_nonneg_left hQe
      (show 0 ≤ 2 * (M0 : ℝ) ^ 2 * X ^ 2 * C1 * blockScale * α by positivity)
    have e1 : B2 = 2 * (M0 : ℝ) ^ 2 * X ^ 2 * C1 * blockScale * α * Q ^ ε +
        4 * X ^ 2 * C1 * M0 * blockScale * α * N ^ (ε / 20) := by
      rw [hB2def, hKα]; ring
    have e2 : c2 * N ^ (ε / 20) * α = 2 * (M0 : ℝ) ^ 2 * X ^ 2 * C1 * blockScale * α *
        N ^ (ε / 20) + 4 * X ^ 2 * C1 * M0 * blockScale * α * N ^ (ε / 20) := by
      rw [hc2def]; ring
    rw [e1, e2]
    linarith
  have hBle : B ≤ c1 * N ^ (ε / 20) * α := by
    have key := mul_le_mul_of_nonneg_left hQe
      (show 0 ≤ (M0 : ℝ) ^ 142 * X ^ 142 * C71 * blockScale * α by positivity)
    have e : c1 * N ^ (ε / 20) * α = (M0 : ℝ) ^ 142 * X ^ 142 * C71 * blockScale * α *
        N ^ (ε / 20) + 2 ^ 141 * X ^ 142 * C71 * M0 * blockScale * α * N ^ (ε / 20) := by
      rw [hc1def]; ring
    have hpos1 : 0 ≤ (M0 : ℝ) ^ 142 * X ^ 142 * C71 * blockScale * α * N ^ (ε / 20) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hM00 _)
        (pow_nonneg hX0 _)) hC71') hK.le) hα) hNe
    have hpos2 : 0 ≤ 2 ^ 141 * X ^ 142 * C71 * M0 * blockScale * α * N ^ (ε / 20) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (pow_nonneg (by norm_num) _) (pow_nonneg hX0 _)) hC71') hM00) hK.le) hα) hNe
    rw [hBdef, e]
    apply max_le
    · have e1 : (M0 : ℝ) ^ 142 * (X ^ 142 * C71 * Q ^ ε * Kα) =
          (M0 : ℝ) ^ 142 * X ^ 142 * C71 * blockScale * α * Q ^ ε := by
        rw [hKα]; ring
      rw [e1]
      linarith
    · have e2 : (X ^ 142 * C71 * N ^ (ε / 20) * 2 ^ 141) * ((M0 : ℝ) * Kα) =
          2 ^ 141 * X ^ 142 * C71 * M0 * blockScale * α * N ^ (ε / 20) := by
        rw [hKα]; ring
      rw [e2]
      linarith
  have hconst := dc_constant_le (C' := (C' : ℝ)) (Nat.cast_nonneg _) hc2 hc1 hB2 hB0 hα hL1' hLN
    hσ hS1 hB2le hBle
  have hcard : (((univ.filter changed).card : ℕ) : ℝ) ≤ 72 := by
    have : (univ.filter changed).card ≤ 72 := by
      have h := card_filter_le (univ : Finset Slot) changed
      rwa [card_univ, card_slot] at h
    exact_mod_cast this
  have hterm : 0 ≤ ((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ *
      (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)) := by
    have h1 : 0 ≤ ((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ :=
      Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hH.le) _
    have h2 : 0 ≤ B2 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hB2 _
    have h3 : 0 ≤ B ^ ((71 : ℝ) / 142) := Real.rpow_nonneg hB0 _
    positivity
  have hdc : |structuredEnergy (FiniteLaw.tensor μb) P ρ
        (paperInputs (joinModuli m₀ p) E Q A D0 M c s) -
      structuredEnergy (FiniteLaw.tensor μb) P ρ gt| ≤
      (72 * (C' : ℝ) ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142)) * totalVariation ρ *
        (L : ℝ) ^ (-σ) * α := by
    refine hdc0.trans ?_
    calc totalVariation ρ * (((univ.filter changed).card : ℝ) *
          (((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142))))
        ≤ totalVariation ρ * (72 * (((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ *
            (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)))) := by
          apply mul_le_mul_of_nonneg_left _ (totalVariation_nonneg ρ)
          exact mul_le_mul_of_nonneg_right hcard hterm
      _ ≤ totalVariation ρ * (72 * (C' : ℝ) ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) *
            (L : ℝ) ^ (-σ) * α) :=
          mul_le_mul_of_nonneg_left hconst (totalVariation_nonneg ρ)
      _ = (72 * (C' : ℝ) ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142)) * totalVariation ρ *
            (L : ℝ) ^ (-σ) * α := by ring
  exact density_structured_reference_theta (slotOf := slotOf) (hindep := hindep)
    (joinModuli m₀ p) hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb
    hμb hR3 E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed hchg Q
    (fun v => paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) gt hgt hun
    hrest hdc

/-- `density_structured_dc_scale` without `θ ≤ 1`. -/
theorem density_structured_dc_scale_theta (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)] {Ω : Type}
      [Fintype Ω],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (_hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
      {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
      (_hcex : IsLeastCounterexample Yf a θ C0 L A) (_hθ : 0 < θ) (_hθ2 : 2 * (θ / 72) ≤ 1) (_ha :
          0 ≤ a)
      (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L) (_hY0 : Yf L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (μb : ∀ b, FiniteLaw (Slot → ZMod (joinModuli m₀ p b)))
      (_hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
      (_hR3 : SquareAffineInvariant (joinModuli m₀ p) μb)
      (T : Finset (J₀ ⊕ J)) (_hprime : ∀ j ∈ T, (joinModuli m₀ p j).Prime) {γ : ℝ}
      (_hγ : 0 ≤ γ) (_hmix : ∀ j ∈ T, ∀ v, IsGammaMixing (joinModuli m₀ p j) γ (μb j) {v})
      {C' : ℕ} (_hC' : 0 < C')
      (_hdiv : ∀ a : ResidueSpace (joinModuli m₀ p),
        (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
      (E : Finset (J₀ ⊕ J)) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ p j = qE * cE) (_hqE : Squarefree qE) (_hcE : IsSquare cE)
      (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ p k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, joinModuli m₀ p j = 1 ∧ M v = blockScale * L))
      (gt : Ω → Slot → ResidueSpace (joinModuli m₀ p) → ResidueSpace (joinModuli m₀ p) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (joinModuli m₀ p) E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v))
          (c ω v) (M v) (stepR (joinModuli m₀ p) E (D0 v))
          (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M c s ω v x)
      (_hun : ∀ v, ¬changed v → ∀ ω x,
        referenceEnergy (FiniteLaw.tensor μb) (gt ω v x) ≤ Yf L A)
      (_hrest : ∀ v, changed v → ∀ B : Finset ℤ,
        B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v) : ℕ) : ℤ) →
        referenceEnergy (FiniteLaw.tensor μb)
            (child (joinModuli m₀ p) E (paperCutoff (blockScale *
              stepEll (joinModuli m₀ p) E (D0 v) (M v))) B
              (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) ≤
          Yf (stepEll (joinModuli m₀ p) E (D0 v) (M v)) B)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ)
      {I : Type} [Fintype I] [DecidableEq I] (_slotOf : I × Bool ≃ {v // changed v})
      (_hindep : Sarkozy.Structured.PairIndependent (joinModuli m₀ p) E A P ρ D0 M c s changed θ
          _slotOf),
      |structuredEnergy (FiniteLaw.tensor μb) P ρ
          (paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ p) E D0 M L) (paperMeanDensity P A D0 M c s)
            changed a θ (density (blockScale * L) A) * Yf L A +
          (72 * (C' : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_groups_theta ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ Ω _ hp hinj hpair Yf a θ C0 L A hcex hθ hθ2 ha hC0 hL hY0 M0 Qcl
    Qpre N0 N0' hsc hM0 μb hμb hR3 T hprime γ hγ hmix C' hC' hdiv E qE cE hDE hqE hcE hcE0 hcQ
    hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed _ hchg gt hgt hgu hun hrest σ hσ hS1 I
        _ _ slotOf hindep
  have hL1 : 1 ≤ L := by omega
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hLM : ∀ v, L ≤ M v := by
    intro v
    rcases hM v with h | h
    · rw [h]; exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    · rw [h]
  have hfacts := fun v => step_facts_of_scale (joinModuli m₀ p) E hsc hL1 hM0 hDE hqE hcE hcE0
    hcQ hcopE hqN (hD0M v) (hcop0 v) (hM v)
  have hQN : paperCutoff (blockScale * L) ≤ ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20) := by
    unfold paperCutoff liftExponent
    exact le_rfl
  exact h m₀ p hp hinj hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 μb hμb hR3 T hprime hγ hmix hC'
    hdiv E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed hchg
    (paperCutoff (blockScale * L)) gt hgt hgu hun hrest (one_le_paperCutoff hKL) hQN
    (fun v => cutoff_conditions_of_scale hsc hKL (hLM v)) (fun v _ => (hfacts v).1)
    (fun v _ => by
      have hn := (hfacts v).2.1
      unfold paperCutoff liftExponent
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) (by norm_num))
    (fun v _ => (hfacts v).2.2.1) (hfacts (0, 0, 0)).2.2.2 hσ hS1 slotOf hindep

end GroupsTheta

section PaperTheta

open Finset
open scoped BigOperators
open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing
  Sarkozy.PaperFrame Sarkozy.Comparison

/-- `density_structured_dc_paper` without `θ ≤ 1`. -/
theorem density_structured_dc_paper_theta (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
      (T : ℕ → Finset ℕ) [∀ L (j : ↥(T L)), NeZero (j : ℕ)] {Ω : Type} [Fintype Ω]
      (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
      (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
      {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ},
      (∀ ℓ, ℓ ≤ L → T ℓ ⊆ T L) → (∀ q ∈ T L, q.Prime) →
      (∀ ℓ, ℓ ≤ L → ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q) →
      ∀ (_hpair : Pairwise fun i j =>
          (joinModuli m₀ (tailModuli T L) i).Coprime (joinModuli m₀ (tailModuli T L) j))
      (_hcex : IsLeastCounterexample (paperY m₀ T μ0 μp) a θ C0 L A) (_hθ : 0 < θ)
      (_hθ2 : 2 * (θ / 72) ≤ 1) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L)
      (_hY0 : paperY m₀ T μ0 μp L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (_hp0 : ∀ i, SlotReflectionPositive (signedIntegral (μ0 i).weight))
      (_hpp : ∀ (q : ℕ) [NeZero q], q.Prime →
        SlotReflectionPositive (signedIntegral (μp q).weight))
      (_hR30 : ∀ i (r t : ZMod (m₀ i)), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod (m₀ i)) → ℝ,
          (μ0 i).expect (fun w => F (fun v => r * w v + t)) = (μ0 i).expect F)
      (_hR3p : ∀ (q : ℕ) [NeZero q] (r t : ZMod q), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod q) → ℝ,
          (μp q).expect (fun w => F (fun v => r * w v + t)) = (μp q).expect F)
      (Tm : Finset (J₀ ⊕ ↥(T L)))
      (_hprimeT : ∀ j ∈ Tm, (joinModuli m₀ (tailModuli T L) j).Prime) {γ : ℝ}
      (_hγ : 0 ≤ γ)
      (_hmix : ∀ j ∈ Tm, ∀ v, IsGammaMixing (joinModuli m₀ (tailModuli T L) j) γ
        (atomLaws m₀ T μ0 μp L j) {v})
      {C' : ℕ} (_hC' : 0 < C')
      (_hdiv : ∀ a : ResidueSpace (joinModuli m₀ (tailModuli T L)),
        (∏ j ∈ univ.filter (· ∉ Tm), addOrderOf (a j)) ∣ C')
      (E : Finset (J₀ ⊕ ↥(T L))) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ (tailModuli T L) j = qE * cE) (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace (joinModuli m₀ (tailModuli T L))) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ (tailModuli T L) k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v →
        ¬(D0 v * ∏ j ∈ E, joinModuli m₀ (tailModuli T L) j = 1 ∧ M v = blockScale * L))
      (gt : Ω → Slot → ResidueSpace (joinModuli m₀ (tailModuli T L)) →
        ResidueSpace (joinModuli m₀ (tailModuli T L)) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (joinModuli m₀ (tailModuli T L)) E x (s ω v) A
          (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
          (stepR (joinModuli m₀ (tailModuli T L)) E (D0 v))
          (blockScale * stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v)))
          y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * L))
          A D0 M c s ω v x)
      (_hunch : ∀ v, ¬changed v → E = ∅ ∧ D0 v = 1 ∧ M v = blockScale * L ∧ ∀ ω, c ω v = 0)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ)
      {I : Type} [Fintype I] [DecidableEq I] (_slotOf : I × Bool ≃ {v // changed v})
      (_hindep : Sarkozy.Structured.PairIndependent (joinModuli m₀ (tailModuli T L)) E A P ρ D0 M
          c s changed θ _slotOf),
      |structuredEnergy (FiniteLaw.tensor (atomLaws m₀ T μ0 μp L)) P ρ
          (paperInputs (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * L)) A D0 M
            c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ (tailModuli T L)) E D0 M L)
            (paperMeanDensity P A D0 M c s) changed a θ (density (blockScale * L) A) *
            paperY m₀ T μ0 μp L A +
          (72 * (C' : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_dc_scale_theta ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ T _ Ω _ μ0 μp a θ C0 L A hmono hprime hlarge hpair hcex hθ hθ2 ha hC0 hL hY0
    M0 Qcl Qpre N0 N0' hsc hM0 hp0 hpp hR30 hR3p Tm hprimeT γ hγ hmix C' hC' hdiv E qE cE hDE hqE
    hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed _ hchg gt hgt hgu hunch σ
    hσ hS1 I _ _ slotOf hindep
  have hL1 : 1 ≤ L := by omega
  have hℓ : ∀ v, changed v → stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v) ≤ L := by
    intro v _
    have h2 := (step_facts_of_scale (joinModuli m₀ (tailModuli T L)) E hsc hL1 hM0 hDE hqE hcE
      hcE0 hcQ hcopE hqN (hD0M v) (hcop0 v) (hM v)).2.1
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num [blockScale])
  have hinv0 : ∀ i (r : ZMod (m₀ i)) (F : (Slot → ZMod (m₀ i)) → ℝ),
      (μ0 i).expect (fun z => F (fun v => z v + r)) = (μ0 i).expect F := by
    intro i r F
    simpa only [one_mul] using hR30 i 1 r isUnit_one ⟨1, (mul_one 1).symm⟩ F
  have hinvp : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F := by
    intro q _ r F
    simpa only [one_mul] using hR3p q 1 r isUnit_one ⟨1, (mul_one 1).symm⟩ F
  have hμb : ∀ b, SlotReflectionPositive (signedIntegral (atomLaws m₀ T μ0 μp L b).weight) := by
    intro b
    cases b with
    | inl i => exact hp0 i
    | inr j => exact hpp (j : ℕ) (hprime j j.2)
  have hR3 : SquareAffineInvariant (joinModuli m₀ (tailModuli T L)) (atomLaws m₀ T μ0 μp L) := by
    intro b
    cases b with
    | inl i => exact hR30 i
    | inr j => exact hR3p (j : ℕ)
  exact h m₀ (tailModuli T L) (fun j => hprime j j.2) Subtype.val_injective hpair hcex hθ hθ2 ha
    hC0 hL hY0 hsc hM0 (atomLaws m₀ T μ0 μp L) hμb hR3 Tm hprimeT hγ hmix hC' hdiv E hDE hqE hcE
    hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed hchg gt hgt hgu
    (hun_atomLaws m₀ T μ0 μp A E D0 M c s changed gt hgu hunch)
    (hrest_atomLaws m₀ T hmono hprime hlarge μ0 μp hp0 hpp hinv0 hinvp E D0 M changed hℓ) hσ hS1
        slotOf hindep

/-- `density_structured_dc_tailPrimes` without `θ ≤ 1`. -/
theorem density_structured_dc_tailPrimes_theta (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
      (P4 : ℕ) {Ω : Type} [Fintype Ω]
      (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
      (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
      {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ},
      ∀ (_hpair : Pairwise fun i j =>
          (joinModuli m₀ (tailModuli (tailPrimes P4) L) i).Coprime
            (joinModuli m₀ (tailModuli (tailPrimes P4) L) j))
      (_hcex : IsLeastCounterexample (paperY m₀ (tailPrimes P4) μ0 μp) a θ C0 L A) (_hθ : 0 < θ)
      (_hθ2 : 2 * (θ / 72) ≤ 1) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L)
      (_hY0 : paperY m₀ (tailPrimes P4) μ0 μp L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (_hp0 : ∀ i, SlotReflectionPositive (signedIntegral (μ0 i).weight))
      (_hpp : ∀ (q : ℕ) [NeZero q], q.Prime →
        SlotReflectionPositive (signedIntegral (μp q).weight))
      (_hR30 : ∀ i (r t : ZMod (m₀ i)), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod (m₀ i)) → ℝ,
          (μ0 i).expect (fun w => F (fun v => r * w v + t)) = (μ0 i).expect F)
      (_hR3p : ∀ (q : ℕ) [NeZero q] (r t : ZMod q), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod q) → ℝ,
          (μp q).expect (fun w => F (fun v => r * w v + t)) = (μp q).expect F)
      {γ : ℝ} (_hγ : 0 ≤ γ)
      (_hmixp : ∀ (j : ↥(tailPrimes P4 L)) (v : Slot), IsGammaMixing (j : ℕ) γ (μp (j : ℕ)) {v})
      (E : Finset (J₀ ⊕ ↥(tailPrimes P4 L))) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j = qE * cE)
      (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω)
      (ρ : (Slot → ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L))) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ (tailModuli (tailPrimes P4) L) k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v →
        ¬(D0 v * ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j = 1 ∧
          M v = blockScale * L))
      (_hunch : ∀ v, ¬changed v → E = ∅ ∧ D0 v = 1 ∧ M v = blockScale * L ∧ ∀ ω, c ω v = 0)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ)
      {I : Type} [Fintype I] [DecidableEq I] (_slotOf : I × Bool ≃ {v // changed v})
      (_hindep : Sarkozy.Structured.PairIndependent (joinModuli m₀ (tailModuli (tailPrimes P4) L))
          E A P ρ D0 M c s changed θ _slotOf),
      |structuredEnergy (FiniteLaw.tensor (atomLaws m₀ (tailPrimes P4) μ0 μp L)) P ρ
          (paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
            (paperCutoff (blockScale * L)) A D0 M
            c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E D0 M L)
            (paperMeanDensity P A D0 M c s) changed a θ (density (blockScale * L) A) *
            paperY m₀ (tailPrimes P4) μ0 μp L A +
          (72 * ((∏ i, m₀ i : ℕ) : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_dc_paper_theta ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ P4 Ω _ μ0 μp a θ C0 L A hpair hcex hθ hθ2 ha hC0 hL hY0 M0 Qcl Qpre N0 N0'
    hsc hM0 hp0 hpp hR30 hR3p γ hγ hmixp E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0
    hD0M hcop0 M hM c s changed _ hchg hunch σ hσ hS1 I _ _ slotOf hindep
  obtain ⟨hmono, hprime, hlarge⟩ := tailPrimes_hyps P4 L
  set Tm : Finset (J₀ ⊕ ↥(tailPrimes P4 L)) := univ.filter (fun b => b.isRight) with hTm
  have hprimeT : ∀ j ∈ Tm, (joinModuli m₀ (tailModuli (tailPrimes P4) L) j).Prime := by
    intro j hj
    rcases j with i | j
    · simp [hTm] at hj
    · exact hprime j j.2
  have hmix : ∀ j ∈ Tm, ∀ v, IsGammaMixing (joinModuli m₀ (tailModuli (tailPrimes P4) L) j) γ
      (atomLaws m₀ (tailPrimes P4) μ0 μp L j) {v} := by
    intro j hj v
    rcases j with i | j
    · simp [hTm] at hj
    · exact hmixp j v
  have hC' : 0 < ∏ i, m₀ i := Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (m₀ i))
  have hdiv : ∀ a : ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)),
      (∏ j ∈ univ.filter (· ∉ Tm), addOrderOf (a j)) ∣ ∏ i, m₀ i := by
    intro a
    rw [Finset.prod_filter, Fintype.prod_sum_type]
    simp only [hTm, mem_filter, mem_univ, true_and, Sum.isRight_inl, Sum.isRight_inr,
      Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ite_true, ite_false,
      prod_const_one, mul_one]
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    have h := addOrderOf_dvd_card (x := a (Sum.inl i))
    rwa [ZMod.card] at h
  -- the square-step models `g̃` at the changed slots, the inputs at the others
  set gt : Ω → Slot → ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)) →
      ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)) → ℝ := fun ω v x =>
    if changed v then fun y =>
      (squareStepModel (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E x (s ω v) A
        (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v))
        (blockScale * stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v))
        (paperCutoff (blockScale *
          stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v)))
        y).re
    else paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
      (paperCutoff (blockScale * L)) A D0 M c s ω v x with hgtdef
  have hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E x (s ω v) A
        (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v))
        (blockScale * stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v))
        (paperCutoff (blockScale *
          stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v)))
        y).re := by
    intro ω v x hv
    rw [hgtdef]
    exact ite_eq_left hv
  have hgu : ∀ v, ¬changed v → ∀ ω x,
      gt ω v x = paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
        (paperCutoff (blockScale * L)) A D0 M c s ω v x := by
    intro v hv ω x
    rw [hgtdef]
    exact ite_eq_right hv
  exact h m₀ (tailPrimes P4) μ0 μp hmono hprime hlarge hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    hp0 hpp hR30 hR3p Tm hprimeT hγ hmix hC' hdiv E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0
    hD0 hD0M hcop0 M hM c s changed hchg gt hgt hgu hunch hσ hS1 slotOf hindep

/-- `density_structured_dc_P5` without `θ ≤ 1`. -/
theorem density_structured_dc_P5_theta (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
      (P4 P5 : ℕ) {Ω : Type} [Fintype Ω]
      (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
      (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
      {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ},
      ∀ (_hpair : Pairwise fun i j =>
          (joinModuli m₀ (tailModuli (tailPrimes P4) L) i).Coprime
            (joinModuli m₀ (tailModuli (tailPrimes P4) L) j))
      (_hcex : IsLeastCounterexample (paperY m₀ (tailPrimes P4) μ0 μp) a θ C0 L A) (_hθ : 0 < θ)
      (_hθ2 : 2 * (θ / 72) ≤ 1) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L)
      (_hY0 : paperY m₀ (tailPrimes P4) μ0 μp L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (_hp0 : ∀ i, SlotReflectionPositive (signedIntegral (μ0 i).weight))
      (_hpp : ∀ (q : ℕ) [NeZero q], q.Prime →
        SlotReflectionPositive (signedIntegral (μp q).weight))
      (_hR30 : ∀ i (r t : ZMod (m₀ i)), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod (m₀ i)) → ℝ,
          (μ0 i).expect (fun w => F (fun v => r * w v + t)) = (μ0 i).expect F)
      (_hR3p : ∀ (q : ℕ) [NeZero q] (r t : ZMod q), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod q) → ℝ,
          (μp q).expect (fun w => F (fun v => r * w v + t)) = (μp q).expect F)
      {γ : ℝ} (_hγ : 0 ≤ γ)
      (_hmixp : ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
        IsGammaMixing q γ (μp q) {v})
      (E : Finset (J₀ ⊕ ↥(tailPrimes P4 L))) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j = qE * cE)
      (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω)
      (ρ : (Slot → ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L))) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ (tailModuli (tailPrimes P4) L) k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v →
        ¬(D0 v * ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j = 1 ∧
          M v = blockScale * L))
      (_hunch : ∀ v, ¬changed v → E = ∅ ∧ D0 v = 1 ∧ M v = blockScale * L ∧ ∀ ω, c ω v = 0)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ)
      {I : Type} [Fintype I] [DecidableEq I] (_slotOf : I × Bool ≃ {v // changed v})
      (_hindep : Sarkozy.Structured.PairIndependent (joinModuli m₀ (tailModuli (tailPrimes P4) L))
          E A P ρ D0 M c s changed θ _slotOf),
      |structuredEnergy (FiniteLaw.tensor (atomLaws m₀ (tailPrimes P4) μ0 μp L)) P ρ
          (paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
            (paperCutoff (blockScale * L)) A D0 M
            c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E D0 M L)
            (paperMeanDensity P A D0 M c s) changed a θ (density (blockScale * L) A) *
            paperY m₀ (tailPrimes P4) μ0 μp L A +
          (72 * ((primeConductorP5 m₀ P4 P5 : ℕ) : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_dc_paper_theta ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ P4 P5 Ω _ μ0 μp a θ C0 L A hpair hcex hθ hθ2 ha hC0 hL hY0 M0 Qcl Qpre N0 N0'
    hsc hM0 hp0 hpp hR30 hR3p γ hγ hmixp E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0
    hD0M hcop0 M hM c s changed _ hchg hunch σ hσ hS1 I _ _ slotOf hindep
  obtain ⟨hmono, hprime, hlarge⟩ := tailPrimes_hyps P4 L
  set Tm : Finset (J₀ ⊕ ↥(tailPrimes P4 L)) := tailAbove P4 P5 L with hTm
  have hprimeT : ∀ j ∈ Tm, (joinModuli m₀ (tailModuli (tailPrimes P4) L) j).Prime := by
    intro j hj
    rcases j with i | j
    · exact absurd hj (inl_not_mem_tailAbove P4 P5 L i)
    · exact hprime j j.2
  have hmix : ∀ j ∈ Tm, ∀ v, IsGammaMixing (joinModuli m₀ (tailModuli (tailPrimes P4) L) j) γ
      (atomLaws m₀ (tailPrimes P4) μ0 μp L j) {v} := by
    intro j hj v
    rcases j with i | j
    · exact absurd hj (inl_not_mem_tailAbove P4 P5 L i)
    · exact hmixp (j : ℕ) (hprime j j.2) ((inr_mem_tailAbove P4 P5 L j).mp hj) v
  have hC' : 0 < primeConductorP5 m₀ P4 P5 := primeConductorP5_pos m₀ P4 P5
  have hdiv := prod_order_dvd_primeConductorP5 m₀ P4 P5 L
  -- the square-step models `g̃` at the changed slots, the inputs at the others
  set gt : Ω → Slot → ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)) →
      ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)) → ℝ := fun ω v x =>
    if changed v then fun y =>
      (squareStepModel (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E x (s ω v) A
        (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v))
        (blockScale * stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v))
        (paperCutoff (blockScale *
          stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v)))
        y).re
    else paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
      (paperCutoff (blockScale * L)) A D0 M c s ω v x with hgtdef
  have hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E x (s ω v) A
        (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v))
        (blockScale * stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v))
        (paperCutoff (blockScale *
          stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v)))
        y).re := by
    intro ω v x hv
    rw [hgtdef]
    exact ite_eq_left hv
  have hgu : ∀ v, ¬changed v → ∀ ω x,
      gt ω v x = paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
        (paperCutoff (blockScale * L)) A D0 M c s ω v x := by
    intro v hv ω x
    rw [hgtdef]
    exact ite_eq_right hv
  exact h m₀ (tailPrimes P4) μ0 μp hmono hprime hlarge hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    hp0 hpp hR30 hR3p Tm hprimeT hγ hmix hC' hdiv E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0
    hD0 hD0M hcop0 M hM c s changed hchg gt hgt hgu hunch hσ hS1 slotOf hindep

/-- **The paper's exponents are admissible for the `_theta` theorems**: at
`(a, θ) = (decay, densityExponent) = (FourRoutesA, ϑ)`, `0 < θ`, `2θ/72 ≤ 1` and `0 ≤ a`.
So `density_structured_dc_tailPrimes_theta` (and `_P5_theta`) apply at the least normalized
counterexamples `IsLeastCounterexample Y decay densityExponent C L A`, which is the form that
`Sarkozy.Structured.atCounterexamples_of_isLeast` turns into WP-FI's `AtCounterexamples`. -/
theorem paperExponents_theta : 0 < densityExponent ∧ 2 * (densityExponent / 72) ≤ 1 ∧
    0 ≤ decay := by
  refine ⟨?_, Sarkozy.Structured.two_mul_densityExponent_div_le, ?_⟩
  · unfold densityExponent; norm_num
  · unfold decay; norm_num

end PaperTheta

end Sarkozy.DensityDC
