module

public import Sarkozy.EnvelopeInputs.MixedChainDC

@[expose] public section

/-!
# `lem:record:density-dc` on the paper's groups, as a stand-alone statement

`lem:record:density-dc` (`paper/sections/08_scale_comparison.tex`, "Averaged comparison with a
density factor"): for a structured energy at `(L, A)` (`def:record:structured-energy`) with the
inputs `g_v^ω = g^{I_v, D_{0,v}, s_v}`, and `g̃_v` the square-step models of
`lem:record:fibre-scale`(b) at the changed slots (`g̃_v = g_v` at the unchanged slots),
`|𝔈 − 𝔈̃| ≤ C_dc ‖ρ‖ N^{-γβ/2+72δ} α ≤ C_dc ‖ρ‖ L^{-σ} α`.

WP-R and I1 proved the steps (`DensityDC.density_dc_paper`, `density_dc_lift_moments`,
`dc_constant_le`, the moment bounds `input_moment_le_density`, `model_moment_le_fibre`) and used
them *inside* the proofs of the `_mixed` chain (`EnvelopeInputs.density_structured_groups_mixed`),
without exporting the comparison itself. The bracket-energy chain of B9
(`BracketEnergy.env_first_mean_le`) and the fibre bounds of DC2 take the comparison as the input
`hdc`. This file exports it:

* **`density_dc_groups`**: `lem:record:density-dc` on the paper's groups
  `G = ∏_{J₀} ℤ/m₀ ⊕ ∏_J ℤ/p` (any prefix moduli, distinct prime tail moduli), with the scale
  hypotheses in the form of `lem:scale-conditions` (`ScaleConditionsAt`) and the modulus
  conditions of `def:record:structured-energy`. The constant `dcConstant` depends only on
  `ε, γ, C', M₀, |X₀|` (not on `L`, `A`, `E`, `ρ` or the index law).
* **`density_dc_point`**: the special case of a point index (`P = Unif(Unit)`) and all slots
  changed, in the form of the hypothesis `hdc` of `BracketEnergy.env_first_mean_le`.

The block coordinates of B5 (`EnvelopeEnergiesPaper.crtModuli m₀ blk p L`) are *definitionally*
`joinModuli (blockModulus m₀ blk) (p L)`, so both statements apply to them with `J₀ := Bk`; this is
done in `DensityChain.BlockDC`.

The hypotheses that remain are those of the paper's lemma: (R3) (`hR3`), (R4) at the tail
coordinates `T` (`hmix`), the prefix conductor bound `C'` (`hdiv`, the paper's `Q_pre`),
uniform one-slot marginals of `|ρ|` (`hunif`, `def:record:structured-energy`(b)), the scale
conditions, and (S1) in the form `ε/20 − γ/40 ≤ −σ`.
-/

namespace Sarkozy.DensityChain

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing
  Sarkozy.DensityDC

/-- The constant `C_dc` of `lem:record:density-dc` produced by the formal proof:
`72 C'^γ c₂^{1/2} c₁^{71/142}` with `c₂ = 2 M₀² X² C₁ K + 4 X² C₁ M₀ K`,
`c₁ = M₀^{142} X^{142} C₇₁ K + 2^{141} X^{142} C₇₁ M₀ K` (`X = |X₀|`, `K = blockScale`, `C₁`, `C₇₁`
the moment constants of `lem:record:lift-moments`(c) and `lem:record:fibre-scale`(e)). -/
noncomputable def dcConstant (C' γ M0 X C1 C71 : ℝ) : ℝ :=
  72 * C' ^ γ *
    (2 * M0 ^ 2 * X ^ 2 * C1 * blockScale + 4 * X ^ 2 * C1 * M0 * blockScale) ^ ((1 : ℝ) / 2) *
    (M0 ^ 142 * X ^ 142 * C71 * blockScale + 2 ^ 141 * X ^ 142 * C71 * M0 * blockScale) ^
      ((71 : ℝ) / 142)

theorem dcConstant_nonneg {C' γ M0 X C1 C71 : ℝ} (hC' : 0 ≤ C') (hM0 : 0 ≤ M0)
    (hC1 : 0 ≤ C1) (hC71 : 0 ≤ C71) : 0 ≤ dcConstant C' γ M0 X C1 C71 := by
  unfold dcConstant
  have hK : (0 : ℝ) ≤ blockScale := by norm_num [blockScale]
  have h1 : 0 ≤ C' ^ γ := Real.rpow_nonneg hC' _
  have h2 : 0 ≤ (2 * M0 ^ 2 * X ^ 2 * C1 * blockScale + 4 * X ^ 2 * C1 * M0 * blockScale) ^
      ((1 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have h3 : 0 ≤ (M0 ^ 142 * X ^ 142 * C71 * blockScale + 2 ^ 141 * X ^ 142 * C71 * M0 *
      blockScale) ^ ((71 : ℝ) / 142) := Real.rpow_nonneg (by positivity) _
  positivity

/-- **`lem:record:density-dc` on the paper's groups** (see the module docstring). For every
`ε > 0` there are moment constants `C₁, C₇₁ > 0` such that, for every structured energy on
`G = ∏ ℤ/m₀ × ∏ ℤ/p` at a scale satisfying `lem:scale-conditions`, with the modulus conditions on
`D_E` and inputs `g^{I_v, D_{0,v}, s_v}` (`M_v ∈ {N, L}`, `D_{0,v} ∣ M₀`), the square-step models
`g̃` at the changed slots satisfy `|𝔈 − 𝔈̃| ≤ C_dc ‖ρ‖ L^{-σ} α` with
`C_dc = dcConstant C' γ M₀ |X₀| C₁ C₇₁`. Proof: WP-R's `density_dc_lift_moments` with I1's moment
bounds and `dc_constant_le`, exactly as inside `density_structured_groups_mixed`. -/
theorem density_dc_groups (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)] {Ω : Type}
      [Fintype Ω],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (_hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
      {L : ℕ} {A : Finset ℤ} (_hL : 2 ≤ L)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (μb : ∀ b, FiniteLaw (Slot → ZMod (joinModuli m₀ p b)))
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
      (gt : Ω → Slot → ResidueSpace (joinModuli m₀ p) → ResidueSpace (joinModuli m₀ p) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (joinModuli m₀ p) E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v))
          (c ω v) (M v) (stepR (joinModuli m₀ p) E (D0 v))
          (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M c s ω v x)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ),
      |structuredEnergy (FiniteLaw.tensor μb) P ρ
          (paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M c s) -
        structuredEnergy (FiniteLaw.tensor μb) P ρ gt| ≤
        dcConstant C' γ M0 (Fintype.card (ResidueSpace m₀)) C1 C71 * totalVariation ρ *
          (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
  obtain ⟨Ci1, hCi1, hci1⟩ := input_moment_le_density 1 le_rfl ε hε
  obtain ⟨Ci71, hCi71, hci71⟩ := input_moment_le_density 71 (by norm_num) ε hε
  obtain ⟨Cm1, hCm1, hcm1⟩ := model_moment_le_fibre 1 le_rfl ε hε
  obtain ⟨Cm71, hCm71, hcm71⟩ := model_moment_le_fibre 71 (by norm_num) ε hε
  refine ⟨max Ci1 Cm1, max Ci71 Cm71, lt_max_of_lt_left hCi1, lt_max_of_lt_left hCi71, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ Ω _ hp hinj hpair L A hL M0 Qcl Qpre N0 N0' hsc hM0 μb hR3 T
    hprime γ hγ hmix C' hC' hdiv E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M
    hcop0 M hM c s changed _ gt hgt hgu σ hσ hS1
  set Q : ℝ := paperCutoff (blockScale * L) with hQdef
  set X : ℝ := (Fintype.card (ResidueSpace m₀) : ℝ) with hX
  set N : ℝ := ((blockScale * L : ℕ) : ℝ) with hN
  set α : ℝ := density (blockScale * L) A with hαdef
  set C1 := max Ci1 Cm1 with hC1
  set C71 := max Ci71 Cm71 with hC71
  set U := FiniteLaw.uniform (ResidueSpace (joinModuli m₀ p)) with hU
  have hK : (0 : ℝ) < blockScale := by norm_num [blockScale]
  have hL1 : 1 ≤ L := by omega
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hLM : ∀ v, L ≤ M v := by
    intro v
    rcases hM v with h | h
    · rw [h]; exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    · rw [h]
  have hfacts := fun v => step_facts_of_scale (joinModuli m₀ p) E hsc hL1 hM0 hDE hqE hcE hcE0
    hcQ hcopE hqN (hD0M v) (hcop0 v) (hM v)
  have hQ1 : 1 ≤ Q := one_le_paperCutoff hKL
  have hQN : Q ≤ ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20) := by
    rw [hQdef]
    unfold paperCutoff liftExponent
    exact le_rfl
  have hcut : ∀ v, 2 * ⌊Q⌋₊ ≤ M v + 1 ∧ ⌊Q⌋₊ ^ 5 ≤ M v + 1 :=
    fun v => cutoff_conditions_of_scale hsc hKL (hLM v)
  have hlam : ∀ v, changed v →
      (((leastSquare (D0 v * ∏ j ∈ E, joinModuli m₀ p j) *
        (blockScale * stepScale blockScale (M v)
          (leastSquare (D0 v * ∏ j ∈ E, joinModuli m₀ p j))) : ℕ) : ℝ) / M v) ≤ 2 :=
    fun v _ => (hfacts v).1
  have hQn : ∀ v, changed v →
      paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v)) ≤
        ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20) := by
    intro v _
    have hn := (hfacts v).2.1
    unfold paperCutoff liftExponent
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) (by norm_num)
  have hHQ' : ∀ v, changed v → ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) ≤
      paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v)) :=
    fun v _ => (hfacts v).2.2.1
  have hHQ : ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) *
      (∏ j ∈ E, joinModuli m₀ p j : ℕ) ≤ Q := (hfacts (0, 0, 0)).2.2.2
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
    _ = dcConstant C' γ M0 X C1 C71 * totalVariation ρ * (L : ℝ) ^ (-σ) * α := by
        unfold dcConstant
        ring

/-! ## The fibrewise form (the first display of the lemma) -/

/-- Reweighting a signed weight by signs does not change its variation. -/
theorem selectedMarginalsUniform_of_abs_eq {XE : Type*} [Fintype XE] [DecidableEq XE]
    (ρ ρ' : (Slot → XE) → ℝ) (h : ∀ z, |ρ' z| = |ρ z|) (hρ : selectedMarginalsUniform ρ) :
    selectedMarginalsUniform ρ' := by
  intro v x
  have ht : totalVariation ρ' = totalVariation ρ := by
    unfold totalVariation
    exact sum_congr rfl fun z _ => h z
  rw [ht, ← hρ v x]
  exact sum_congr rfl fun z _ => h z

/-- **`lem:record:density-dc`, fibrewise, at a point index** (the first display of the lemma:
the absolute value inside the `z`-integral). With the hypotheses of `density_dc_groups` and the
index law a point (`Ω = Unit`):
`∑_z |ρ(z)| · |Λ_{μ_𝒮}((g_v(z_v, ·))_v) − Λ_{μ_𝒮}((g̃_v(z_v, ·))_v)| ≤ C_dc ‖ρ‖ L^{-σ} α`.

Proof: apply `density_dc_groups` to the reweighted `ρ'(z) = ±|ρ(z)|`, with the sign of the
difference at `z`; `|ρ'| = |ρ|`, so (b) of `def:record:structured-energy` and `‖ρ'‖ = ‖ρ‖` are
unchanged, and the signed difference of the two energies for `ρ'` is the left side.

Every `σ ≥ 0` with `ε/20 − γ/40 ≤ −σ` is allowed, so the power saving over any fixed `σ₀ <
γ/40` is available by taking `ε` smaller (the constant depends on `ε`). This is the form
`N^{-γβ/2 + 72δ}` of the paper's first display, with `L ≤ N`. -/
theorem density_dc_fibrewise (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (_hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
      {L : ℕ} {A : Finset ℤ} (_hL : 2 ≤ L)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (μb : ∀ b, FiniteLaw (Slot → ZMod (joinModuli m₀ p b)))
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
      (ρ : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ p k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Slot → ℤ) (s : ∀ v : Slot, ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (gt : Slot → ResidueSpace (joinModuli m₀ p) → ResidueSpace (joinModuli m₀ p) → ℝ)
      (_hgt : ∀ v x, changed v → gt v x = fun y =>
        (squareStepModel (joinModuli m₀ p) E x (s v) A (Icc (c v + 1) (c v + M v))
          (c v) (M v) (stepR (joinModuli m₀ p) E (D0 v))
          (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ x,
        gt v x = paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M
          (fun _ : Unit => c) (fun _ : Unit => s) () v x)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ),
      ∑ z, |ρ z| *
        |multilinearIntegral (signedIntegral (FiniteLaw.tensor μb).weight)
            (fun v => paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M
              (fun _ : Unit => c) (fun _ : Unit => s) () v (z v)) -
          multilinearIntegral (signedIntegral (FiniteLaw.tensor μb).weight)
            (fun v => gt v (z v))| ≤
        dcConstant C' γ M0 (Fintype.card (ResidueSpace m₀)) C1 C71 * totalVariation ρ *
          (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_dc_groups ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ hp hinj hpair L A hL M0 Qcl Qpre N0 N0' hsc hM0 μb hR3 T
    hprime γ hγ hmix C' hC' hdiv E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN ρ hunif D0 hD0 hD0M
    hcop0 M hM c s changed _ gt hgt hgu σ hσ hS1
  set g : Slot → ResidueSpace (joinModuli m₀ p) → ResidueSpace (joinModuli m₀ p) → ℝ :=
    paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M
      (fun _ : Unit => c) (fun _ : Unit => s) () with hg
  set d : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ := fun z =>
    multilinearIntegral (signedIntegral (FiniteLaw.tensor μb).weight) (fun v => g v (z v)) -
      multilinearIntegral (signedIntegral (FiniteLaw.tensor μb).weight) (fun v => gt v (z v))
    with hd
  set ρ' : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ := fun z =>
    if 0 ≤ d z then |ρ z| else -|ρ z| with hρ'
  have habs : ∀ z, |ρ' z| = |ρ z| := by
    intro z
    simp only [hρ']
    split_ifs <;> simp
  have hunif' : selectedMarginalsUniform ρ' := selectedMarginalsUniform_of_abs_eq ρ ρ' habs hunif
  have htv : totalVariation ρ' = totalVariation ρ := by
    unfold totalVariation
    exact sum_congr rfl fun z _ => habs z
  have key := h m₀ p hp hinj hpair hL hsc hM0 μb hR3 T hprime hγ hmix hC' hdiv E hDE hqE hcE
    hcE0 hcQ hcopE hqN (FiniteLaw.uniform Unit) ρ' hunif' D0 hD0 hD0M hcop0 M hM
    (fun _ => c) (fun _ => s) changed (fun _ => gt) (fun _ v x hv => hgt v x hv)
    (fun v hv _ x => hgu v hv x) hσ hS1
  rw [htv] at key
  refine le_trans (le_of_eq ?_) (le_trans (le_abs_self _) key)
  have hU : ∀ F : Unit → ℝ, (FiniteLaw.uniform Unit).expect F = F () := by
    intro F
    rw [show F = fun _ => F () from funext fun ω => by cases ω; rfl]
    exact FiniteLaw.expect_const _ _
  unfold structuredEnergy
  rw [hU, hU, ← sum_sub_distrib]
  apply sum_congr rfl
  intro z _
  rw [← mul_sub]
  change |ρ z| * |d z| = ρ' z * d z
  simp only [hρ']
  split_ifs with h0
  · rw [abs_of_nonneg h0]
  · rw [abs_of_neg (lt_of_not_ge h0)]
    ring

end Sarkozy.DensityChain
