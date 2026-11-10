module

public import Sarkozy.SharpFirst.Pieces
public import Sarkozy.SharpSums.YBound
public import Sarkozy.ThetaOne.Hatom
public import Sarkozy.DensityChain2.Folded

@[expose] public section

/-!
# One folded energy of `lem:sharp-first` at unchanged inputs

SR (8 November 2026). The folded energies of TH's whole-difference pieces carry the unchanged
input `F_A` at every slot (`ThetaOne.sharpFirstTerms_of_wholeFolded`: `Y^O[κ] = Y_{κ⊗O}`). For a
tensor `Λ` of positive records equal to `μ_𝔟` off a set `E` of atoms:

* **`whole_chain`** (`prop:record:density-structured` for a folded energy at unchanged inputs,
  with `lem:record:density-dc` and restoration `lem:record:fibre-scale`(c)): if `D_E ≠ 1` and
  `D_E` satisfies the modulus conditions of `def:record:structured-energy`(a) with `q_E ≤ N^τ`,
  `|∫ ∏_v F_A d(⊗Λ)| ≤ (∏_{E} ‖Λ_𝔟‖) ((1 + u_L) sq(D_E)^a Y + C_dc L^{-σ} α)`.
  This is DC2's `block_energy_le_structured_data` at the whole slot datum `wholeDatum L` at every
  slot, with `hrest` (DC3's `hrest_block`), `hdc` (DC1's `DCBlockProp`), `hun` (vacuous, every
  slot is changed) and `hatom` (`θ = 1`, positive records) discharged. The main price of whole
  slot data is at most `sq(D_E)^a` (`mainPrice_whole_le`).
* **`whole_holder`** (`lem:record:density-lp`, first step: Hölder in `L^{72}` with uniform
  marginals, and `lem:record:lift-moments`(c)): for every tensor of positive records,
  `|∫ ∏_v F_A d(⊗Λ)| ≤ (∏_𝔟 ‖Λ_𝔟‖) M₀^{72} |X₀|^{72} C_ε Q^ε K α`.
-/

namespace Sarkozy.SharpFirst

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.DensityChain2 Sarkozy.DensityDC

/-- **The main price of whole slot data** is at most `sq(D_E)^a`: every slot price is
`(N/N) sq(D_E)` and every mean density is at most `α`. -/
theorem mainPrice_whole_le {Jc : Type} [Fintype Jc] [DecidableEq Jc] (m : Jc → ℕ)
    [∀ j, NeZero (m j)] (Es : Finset Jc) {L : ℕ} (hL : 1 ≤ L) (A : Finset ℤ) (a θ : ℝ)
    (hθ : 0 ≤ θ) :
    mainPrice (paperPrice m Es (fun _ => (wholeDatum L).1) (fun _ => (wholeDatum L).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A (fun _ => (wholeDatum L).1)
        (fun _ => (wholeDatum L).2.2.1) (fun _ _ => (wholeDatum L).2.2.2)
        (fun _ _ => (wholeDatum L).2.1))
      (fun _ => True) a θ (density (blockScale * L) A) ≤
      ((leastSquare (∏ j ∈ Es, m j) : ℕ) : ℝ) ^ a := by
  rw [mainPrice_split m Es (fun _ => (wholeDatum L).1) (fun _ => (wholeDatum L).2.2.1) L _ a θ
    (density (blockScale * L) A) (fun _ => Nat.coprime_one_left _)]
  have hsq : 0 ≤ ((leastSquare (∏ j ∈ Es, m j) : ℕ) : ℝ) ^ a :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hsq) (le_of_eq (mul_one _))
  unfold mainPrice
  have hKL : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hN : ((blockScale * L : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hKL.ne'
  have h1 : ∀ v : Slot, paperPrice m ∅ (fun _ => (wholeDatum L).1)
      (fun _ => (wholeDatum L).2.2.1) L v = 1 := by
    intro v
    unfold paperPrice
    have e : stepR m ∅ (wholeDatum L).1 = 1 := stepR_empty_one m
    rw [e]
    simp only [wholeDatum, Nat.cast_one, mul_one]
    exact div_self hN
  simp only [h1, Real.one_rpow, prod_const_one, one_mul]
  refine prod_le_one₀ (fun v _ => Real.rpow_nonneg ?_ _) fun v _ => Real.rpow_le_one ?_ ?_
    (by positivity)
  · exact div_nonneg (by
      unfold paperMeanDensity
      exact FiniteLaw.expect_nonneg _ fun _ => by positivity) (density_nonneg _ _)
  · exact div_nonneg (by
      unfold paperMeanDensity
      exact FiniteLaw.expect_nonneg _ fun _ => by positivity) (density_nonneg _ _)
  · refine div_le_one_of_le₀ ?_ (density_nonneg _ _)
    unfold paperMeanDensity
    rw [FiniteLaw.expect_const]
    unfold density
    simp only [wholeDatum, Nat.cast_one]
    rw [one_div, inv_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact_mod_cast (card_filter_le _ _).trans (card_le_card inter_subset_left)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **One folded energy at unchanged inputs, small modulus** (`prop:record:density-structured`;
see the module docstring). -/
theorem whole_chain {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a densityExponent C0 L A) (ha : 0 ≤ a) (hC0 : 0 ≤ C0)
    (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Λ : ∀ b : BlockAtom Bk PaperJt L, ((Slot → BlockLabel m₀ blk paperTail L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk PaperJt L)) (hE : ∀ b ∉ Es, Λ b = D.R.law paperTail L b)
    (hΛ : ∀ b ∈ Es, IsPositiveRecord (Λ b))
    (hne : ∏ j ∈ Es, crtModuli m₀ blk paperTail L j ≠ 1)
    {qE cE : ℕ} (hDE : ∏ b ∈ Es, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    {σ : ℝ} (hσ : 0 ≤ σ) (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ) :
    |multilinearIntegral (tensorLaw Λ) (fun _ => blockLift m₀ blk paperTail L A)| ≤
      (∏ b ∈ Es, mass (Λ b)) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
            ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a * D.Y L A +
          dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have h0 := prefix_pairwise (hpair L)
  have hT : multilinearIntegral (tensorLaw Λ) (fun _ => blockLift m₀ blk paperTail L A) =
      multilinearIntegral (tensorLaw (crtLaws blk h0 L Λ))
        (fun _ => paperForm (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A
          (wholeDatum L)) := by
    rw [multilinearIntegral_crt blk h0 L]
    congr 1
    funext v y
    rw [blockLift_crtLabel blk L (hpair L) A y, unchangedInput_eq_paperForm]
  rw [hT]
  have hθ : (0 : ℝ) < densityExponent := by unfold densityExponent; norm_num
  have hθ2 : 2 * (densityExponent / 72) ≤ 1 := by unfold densityExponent; norm_num
  have hchg : ∀ v, (fun _ : Slot => True) v → ¬((wholeDatum L).1 *
      ∏ j ∈ Es, crtModuli m₀ blk paperTail L j = 1 ∧
      (wholeDatum L).2.2.1 = blockScale * L) := by
    intro v _ h1
    apply hne
    have := h1.1
    simp only [wholeDatum, one_mul] at this
    exact this
  have hdc := hdcb blk paperTail D.R (A := A) (hpair L) (D.S.p_prime L) (D.S.p_inj L) hL hsc hM0
    Es hDE hqE hcE hcE0 hcQ hcopE hqN (FiniteLaw.uniform Unit) _
    (selectedMarginalsUniform_liftWeight_uniform Es _ (hsel_of_positive_laws h0 Λ Es hΛ))
    (fun _ => (wholeDatum L).1) (fun _ => le_rfl) (fun _ => one_dvd _)
    (fun _ _ => Nat.coprime_one_left _)
    (fun _ => (wholeDatum L).2.2.1) (fun _ => Or.inl rfl)
    (fun _ _ => (wholeDatum L).2.2.2) (fun _ _ => (wholeDatum L).2.1)
    (fun _ => True)
    (fun _ => revealedModel (crtModuli m₀ blk paperTail L) Es A (fun _ => (wholeDatum L).1)
      (fun _ => (wholeDatum L).2.2.1) (fun _ => (wholeDatum L).2.2.2)
      (fun _ => (wholeDatum L).2.1)
      (fun _ => paperCutoff (blockScale * stepEll (crtModuli m₀ blk paperTail L) Es
        (wholeDatum L).1 (wholeDatum L).2.2.1)))
    (fun _ v x _ => by
      funext y
      simp only [revealedModel])
    (fun v hv => absurd trivial hv) hσ hS1
  rw [totalVariation_liftWeight] at hdc
  have hmain := DensityFibre.block_energy_le_structured_data D (hpair L) hcex hθ hθ2 ha hC0 hL
    (le_of_eq (dataY_empty D L)) hsc hM0 Λ Es hE hDE hqE hcE hcE0 hcQ hcopE hqN
    (paperCutoff (blockScale * L)) (fun _ => wholeDatum L) (fun _ => le_rfl)
    (fun _ => one_dvd _) (fun _ _ => Nat.coprime_one_left _) (fun _ => Or.inl rfl)
    (fun _ => True) hchg _ (fun v hv => absurd trivial hv)
    (fun v _ B hB => hrest_block (T := paperTailPrimes) D (fun ℓ hℓ => paperTailPrimes_mono hℓ)
      (paperTailPrimes_prime L) (fun ℓ hℓ => paperTailPrimes_large hℓ) _ hpair Es _ _ le_rfl B)
    hdc (fun b hb hb' => ThetaOne.mixedLp_theta_of_positiveRecord (hΛ b hb) hb')
  refine hmain.trans ?_
  have hY0 : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 := scaleU_nonneg blockScale M0 Qcl stageTau L
  have hprod : (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (Λ b.1) x|) = ∏ b ∈ Es, mass (Λ b) := by
    rw [prod_coe_sort Es (fun b => ∑ x : Slot → BlockLabel m₀ blk paperTail L b,
      |lawDensity (Λ b) x|)]
    exact prod_congr rfl fun b hb => (LargeSums.mass_eq_sum_abs (hΛ b hb)).symm
  rw [hprod]
  have hm0 : 0 ≤ ∏ b ∈ Es, mass (Λ b) := prod_nonneg fun b hb =>
    TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (hΛ b hb).1
  have hpr := mainPrice_whole_le (crtModuli m₀ blk paperTail L) Es (by omega : 1 ≤ L) A a
    densityExponent hθ.le
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hm0
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpr (by linarith)) hY0

/-- **Hölder at unchanged inputs** (`lem:record:density-lp`, first step;
`lem:record:lift-moments`(c); see the module docstring). -/
theorem whole_holder (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
    [∀ L j, NeZero (p L j)]
    (_hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    {L : ℕ} (A : Finset ℤ) {M0 Qcl Qpre N0 N0' : ℕ}
    (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L) (_hL : 1 ≤ L) (_hM0 : 1 ≤ M0)
    (_hp : ∀ j, (p L j).Prime) (_hinj : Injective (p L))
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (_hΛ : ∀ b, IsPositiveRecord (Λ b)),
    |multilinearIntegral (tensorLaw Λ) (fun _ => blockLift m₀ blk p L A)| ≤
      (∏ b, mass (Λ b)) *
        ((M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
          paperCutoff (blockScale * L) ^ ε * ((blockScale : ℝ) * density (blockScale * L) A))) := by
  obtain ⟨C, hC, hc⟩ := input_moment_le_density 36 (by norm_num) ε hε
  refine ⟨C, hC, ?_⟩
  intro J _ _ p _ hpair L A M0 Qcl Qpre N0 N0' hsc hL hM0 hp hinj Λ hΛ
  set Q := paperCutoff (blockScale * L) with hQ
  set F : Unit → Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ :=
    fun _ _ => unchangedInput (crtModuli m₀ blk p L) Q A L with hF
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hQ1 : 1 ≤ Q := one_le_paperCutoff hKL
  have hB : ∀ v, (FiniteLaw.uniform Unit).expect (fun ω =>
        (FiniteLaw.uniform (ResidueSpace (crtModuli m₀ blk p L))).moment 72 (F ω v)) ≤
      (M0 : ℝ) ^ 72 * ((Fintype.card (ResidueSpace (blockModulus m₀ blk)) : ℝ) ^ 72 * C *
        Q ^ ε * ((blockScale : ℝ) * density (blockScale * L) A)) := by
    intro v
    apply FiniteLaw.expect_le_const
    intro ω
    have hFw : F ω v = paperForm (crtModuli m₀ blk p L) Q A (wholeDatum L) :=
      unchangedInput_eq_paperForm _ Q A L
    rw [hFw]
    have hLM : L ≤ (wholeDatum L).2.2.1 := Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    have hcut := cutoff_conditions_of_scale hsc hKL hLM
    have hD0le : (wholeDatum L).1 ≤ M0 := hM0
    have key := hc (blockModulus m₀ blk) (p L) hp hinj Q hQ1 (wholeDatum L).2.2.2
      hL hLM hcut.1 hcut.2 hD0le (wholeDatum L).2.1 A
    simp only [show (2 * 36 : ℕ) = 72 from rfl, Nat.cast_ofNat] at key
    exact key
  have h := LargeSums.expect_abs_tensor_le (FiniteLaw.uniform Unit) Λ hΛ
    (crtLabelEquiv blk (prefix_pairwise (hpair L)) L) id F hB
  simp only [hF, id] at h
  rw [FiniteLaw.expect_const] at h
  refine le_of_eq_of_le ?_ h
  congr 2
  funext v x
  rw [← blockLift_crtLabel blk L (hpair L) A, Equiv.apply_symm_apply]

end Sarkozy.SharpFirst
