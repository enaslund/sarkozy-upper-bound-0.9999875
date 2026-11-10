module

public import Sarkozy.SharpBase.OptAlgebra
public import Sarkozy.DensityChain2.Hfold

@[expose] public section

/-!
# DC2's `hfold` for the four sharp-first differences, with the re-optimized remainder

SH2 (7 November 2026). DC3's `DensityChain2.hfold_envL/R_paper`, `hfold_fixL/R_paper` prove DC2's
per-choice hypothesis `hfold` (of `DensityFibre.env/fixHdiffL/R_of_folded`) with the explicit
remainders `rchEnvL/R`, `rchFixL/R`, built from DC3's witnesses (`HfoldAlgebra.hfold_choice`:
AM–GM ratio `t = √(M₋/M₊)`). That ratio is a ratio of local-density factors of the two halves
of the tag cut; its mean over the index `ω` is not controlled (it involves negative moments of
local densities), so the summation of DC3's `rch` (the field `hr2`) is not available by the
paper's argument (`SharpBase.OptAlgebra`).

Here the same per-piece chain bounds (DC3's `*_foldPlus/Minus_piece_hfold`) are combined by
`SharpBase.hfold_choice_opt`, which re-optimizes the ratio against the whole bounds. The proofs
are DC3's, copied with that one change; the remainders are `rchOptEnvL/R`, `rchOptFixL/R`
(`SharpBase.rchOpt` in place of `rchVal`), whose summands are the paper's cross terms
`√(W M₊ R₋) + √(W M₋ R₊) + √(R₊ R₋)` (`rchOptVal_le_cross`).
-/

namespace Sarkozy.SharpBase

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
open Sarkozy.Param (Params)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The re-optimized `rch` of field 30**: DC3's `rchEnvL` with
`SharpBase.rchOpt` (the AM–GM ratio optimized against the whole bounds) in place of
`HfoldAlgebra.rchVal`. -/
noncomputable def rchOptEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchOpt (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
    ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1))
    (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus)
    (envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus)
    (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
      (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
      density (blockScale * L) A)
    (fun φ => EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
      (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => EnvelopeInputs.foldedPlus (D.FS.cut j)
      (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
      (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
        (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)
    (fun φ => EnvelopeInputs.foldedMinus (D.FS.cut j)
      (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
      (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
        (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)

/-- **DC2's `hfold` for field 30 (`Sh.envM.hdiffL`), re-optimized remainder**
(`lem:sharp-first`, `lem:record:folded-energy`, `prop:record:density-structured`): DC3's
`hfold_envL_paper` with `rch = rchOptEnvL`; DC3's proof, with
`SharpBase.hfold_choice_opt` in place of `hfold_choice`. -/
theorem hfoldOpt_envL_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.envIncL D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.envIncL D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ RecordExpansion.countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, DensityFibre.HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
              stageTau L) * (envLambda hcop L A Jq ω * (conductorPrice pr h
              (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)))) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedPlus (D.FS.cut j)
              (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
              (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedMinus (D.FS.cut j)
              (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
              (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rp φ +
            (∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rm φ) / t) / 2 ≤
            rchOptEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ) := by
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  have hsc := eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) 1 0 0
    (by norm_num [blockScale]) hM0 hQ1
  filter_upwards [hsc, eventually_ge_atTop 2] with L hscL hL
  intro C hC hk A hA hY Jq ω f σ hσ0 j _hj
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hθ : (0 : ℝ) < densityExponent := by unfold densityExponent; norm_num
  have hθ2 : 2 * (densityExponent / 72) ≤ 1 := by unfold densityExponent; norm_num
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hY0 : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  -- the density is positive
  have hα : 0 < density (blockScale * L) A := by
    have hlow0 : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
      mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    have hYpos := lt_of_le_of_lt hlow0 hY
    rcases Finset.eq_empty_or_nonempty A with hA0 | hA0
    · rw [hA0, dataY_empty] at hYpos
      exact absurd hYpos (lt_irrefl 0)
    · exact density_pos_of_nonempty (Nat.mul_pos (by norm_num [blockScale]) (by omega)) hA0
  set u := scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
        ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
          ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  set U := ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) with hU
  have hU0 : 0 ≤ U := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.envPriceL_nonneg D L b
    · exact zero_le_one
  set K₀ := (1 + u) * D.Y L A * U with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (mul_nonneg (by linarith) hY0) hU0
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (envSlots hcop D.index.u L Jq ω v).1)
      (fun v => (envSlots hcop D.index.u L Jq ω v).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (envSlots hcop D.index.u L Jq ω v).1)
      (fun v => (envSlots hcop D.index.u L Jq ω v).2.2.1)
      (fun _ v => (envSlots hcop D.index.u L Jq ω v).2.2.2)
      (fun _ v => (envSlots hcop D.index.u L Jq ω v).2.1))
    (fun _ => True) a densityExponent (density (blockScale * L) A) with hP0def
  have hP0 : P0 = conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      envLambda hcop L A Jq ω := by
    rw [hP0def, envMainPrice_eq hcop (crtModuli m₀ blk paperTail L) (by omega) D.index.u
      D.index.hu ∅ A hA.1 hα a densityExponent Jq ω (fun e => by simp)]
    unfold envLambda EnvelopeInputsBlock.priceExponent stepR
    simp [leastSquare_one]
  have hP0nn : 0 ≤ P0 := envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω id
  have hprod : envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus *
      envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus = P0 ^ 2 :=
    DensityFibre.mainPrice_fold_mul (D.FS.cut j)
      (paperPrice (crtModuli m₀ blk paperTail L) ∅
        (fun v => (envSlots hcop D.index.u L Jq ω v).1)
        (fun v => (envSlots hcop D.index.u L Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A
        (fun v => (envSlots hcop D.index.u L Jq ω v).1)
        (fun v => (envSlots hcop D.index.u L Jq ω v).2.2.1)
        (fun _ v => (envSlots hcop D.index.u L Jq ω v).2.2.2)
        (fun _ v => (envSlots hcop D.index.u L Jq ω v).2.1))
      a densityExponent (density (blockScale * L) A)
  have hΛ0 : 0 ≤ envLambda hcop L A Jq ω := prod_nonneg fun e _ =>
    Real.rpow_nonneg (div_nonneg (by
      unfold queryLocalDensity localDensity
      positivity) (density_nonneg _ _)) _
  have hcond0 : 0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq :=
    conductorPrice_nonneg pr h _ Jq
  have hR : 2 * (K₀ * P0) ≤ 2 * ((1 + u) * (envLambda hcop L A Jq ω *
      (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A * U))) := by
    rw [hP0, hK₀]
    exact le_of_eq (by ring)
  have hR0 : 0 ≤ 2 * ((1 + u) * (envLambda hcop L A Jq ω *
      (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A * U))) := by
    have : 0 ≤ 1 + u := by linarith
    positivity
  -- the selected atoms of an admissible piece are nonempty
  obtain ⟨b₀, hb₀⟩ : ∃ b, σ b ≠ none := by
    by_contra hcon
    push Not at hcon
    exact hσ0 (funext hcon)
  have hEne : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      (DensityFibre.hTermAtoms D L φ).Nonempty := by
    intro φ hφ
    refine ⟨b₀, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    exact hpieceIsMu_false_of_coef D L f σ j b₀ hb₀ (φ b₀) (hφ b₀)
  have hCr : 0 ≤ dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
      (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
      (L : ℝ) ^ (-σ') * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg (dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le)
      (Nat.cast_nonneg _) hC1.le hC71.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  have hBG : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ ∏ b, DensityFibre.bpieceG D L b (φ b) :=
    fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)
  have hw : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ EnvelopeInputs.choiceWeight
      (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ := fun φ =>
    prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))
  have hp : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      ((∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ) →
      EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨hJ, qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact env_foldPlus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN Jq hJ ω hσ' hS1 (fun b hb hb' => hatomP L j b (φ b) (mem_filter.mp hb).2 hb')
  have hm : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      ((∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ) →
      EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) (dec L) j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨hJ, qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact env_foldMinus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN Jq hJ ω hσ' hS1 (fun b hb hb' => hatomM L j b (φ b) (mem_filter.mp hb).2 hb')
  obtain ⟨_, _, _, _, _, h1, h2, h3, h4, h5⟩ := hfold_choice_opt _ _ hK₀0
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _)
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _) hP0nn hprod hR
    hR0 _ _ _ _ _ _ hBG hp hm
  refine ⟨_, _, _, _, _, h1, h2, h3, h4, h5.trans ?_⟩
  unfold rchOptEnvL
  apply Finset.single_le_sum (f := fun j' => rchOpt _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchOpt_nonneg _ hK₀0
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _)
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _) hCr _ _ _ _ _ _
    (fun φ => prod_nonneg fun b _ => mul_nonneg (abs_nonneg _)
      (DensityFibre.bpieceD_nonneg D L b (φ b))) hBG
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)

/-- **The re-optimized `rch` of field 31**: DC3's `rchEnvR` with
`SharpBase.rchOpt` (the AM–GM ratio optimized against the whole bounds) in place of
`HfoldAlgebra.rchVal`. -/
noncomputable def rchOptEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchOpt (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
    ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1))
    (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus)
    (envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus)
    (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
      (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
      density (blockScale * L) A)
    (fun φ => EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
      (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => EnvelopeInputs.foldedPlus (D.FS.cut j)
      (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
      (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
        (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)
    (fun φ => EnvelopeInputs.foldedMinus (D.FS.cut j)
      (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
      (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
        (revealedInputCRT blk hcop D L A Jq)
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)

/-- **DC2's `hfold` for field 31 (`Sh.envM.hdiffR`), re-optimized remainder**
(`lem:sharp-first`, `lem:record:folded-energy`, `prop:record:density-structured`): DC3's
`hfold_envR_paper` with `rch = rchOptEnvR`; DC3's proof, with
`SharpBase.hfold_choice_opt` in place of `hfold_choice`. -/
theorem hfoldOpt_envR_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.envIncR D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.envIncR D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ RecordExpansion.countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, DensityFibre.HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
              stageTau L) * (envLambda hcop L A Jq ω * (conductorPrice pr h
              (EnvelopeInputsBlock.priceExponent a) Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)))) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedPlus (D.FS.cut j)
              (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
              (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedMinus (D.FS.cut j)
              (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
              (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rp φ +
            (∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rm φ) / t) / 2 ≤
            rchOptEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ) := by
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  have hsc := eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) 1 0 0
    (by norm_num [blockScale]) hM0 hQ1
  filter_upwards [hsc, eventually_ge_atTop 2] with L hscL hL
  intro C hC hk A hA hY Jq ω f σ hσ0 j _hj
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hθ : (0 : ℝ) < densityExponent := by unfold densityExponent; norm_num
  have hθ2 : 2 * (densityExponent / 72) ≤ 1 := by unfold densityExponent; norm_num
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hY0 : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  -- the density is positive
  have hα : 0 < density (blockScale * L) A := by
    have hlow0 : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
      mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    have hYpos := lt_of_le_of_lt hlow0 hY
    rcases Finset.eq_empty_or_nonempty A with hA0 | hA0
    · rw [hA0, dataY_empty] at hYpos
      exact absurd hYpos (lt_irrefl 0)
    · exact density_pos_of_nonempty (Nat.mul_pos (by norm_num [blockScale]) (by omega)) hA0
  set u := scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
        ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
          ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  set U := ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) with hU
  have hU0 : 0 ≤ U := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.envPriceR_nonneg D L b
    · exact zero_le_one
  set K₀ := (1 + u) * D.Y L A * U with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (mul_nonneg (by linarith) hY0) hU0
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (envSlots hcop D.index.w L Jq ω v).1)
      (fun v => (envSlots hcop D.index.w L Jq ω v).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (envSlots hcop D.index.w L Jq ω v).1)
      (fun v => (envSlots hcop D.index.w L Jq ω v).2.2.1)
      (fun _ v => (envSlots hcop D.index.w L Jq ω v).2.2.2)
      (fun _ v => (envSlots hcop D.index.w L Jq ω v).2.1))
    (fun _ => True) a densityExponent (density (blockScale * L) A) with hP0def
  have hP0 : P0 = conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
      envLambda hcop L A Jq ω := by
    rw [hP0def, envMainPrice_eq hcop (crtModuli m₀ blk paperTail L) (by omega) D.index.w
      D.index.hw ∅ A hA.1 hα a densityExponent Jq ω (fun e => by simp)]
    unfold envLambda EnvelopeInputsBlock.priceExponent stepR
    simp [leastSquare_one]
  have hP0nn : 0 ≤ P0 := envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω id
  have hprod : envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus *
      envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus = P0 ^ 2 :=
    DensityFibre.mainPrice_fold_mul (D.FS.cut j)
      (paperPrice (crtModuli m₀ blk paperTail L) ∅
        (fun v => (envSlots hcop D.index.w L Jq ω v).1)
        (fun v => (envSlots hcop D.index.w L Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A
        (fun v => (envSlots hcop D.index.w L Jq ω v).1)
        (fun v => (envSlots hcop D.index.w L Jq ω v).2.2.1)
        (fun _ v => (envSlots hcop D.index.w L Jq ω v).2.2.2)
        (fun _ v => (envSlots hcop D.index.w L Jq ω v).2.1))
      a densityExponent (density (blockScale * L) A)
  have hΛ0 : 0 ≤ envLambda hcop L A Jq ω := prod_nonneg fun e _ =>
    Real.rpow_nonneg (div_nonneg (by
      unfold queryLocalDensity localDensity
      positivity) (density_nonneg _ _)) _
  have hcond0 : 0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq :=
    conductorPrice_nonneg pr h _ Jq
  have hR : 2 * (K₀ * P0) ≤ 2 * ((1 + u) * (envLambda hcop L A Jq ω *
      (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A * U))) := by
    rw [hP0, hK₀]
    exact le_of_eq (by ring)
  have hR0 : 0 ≤ 2 * ((1 + u) * (envLambda hcop L A Jq ω *
      (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A * U))) := by
    have : 0 ≤ 1 + u := by linarith
    positivity
  -- the selected atoms of an admissible piece are nonempty
  obtain ⟨b₀, hb₀⟩ : ∃ b, σ b ≠ none := by
    by_contra hcon
    push Not at hcon
    exact hσ0 (funext hcon)
  have hEne : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      (DensityFibre.hTermAtoms D L φ).Nonempty := by
    intro φ hφ
    refine ⟨b₀, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    exact hpieceIsMu_false_of_coef D L f σ j b₀ hb₀ (φ b₀) (hφ b₀)
  have hCr : 0 ≤ dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
      (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
      (L : ℝ) ^ (-σ') * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg (dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le)
      (Nat.cast_nonneg _) hC1.le hC71.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  have hBG : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ ∏ b, DensityFibre.bpieceG D L b (φ b) :=
    fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)
  have hw : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ EnvelopeInputs.choiceWeight
      (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ := fun φ =>
    prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))
  have hp : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      ((∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ) →
      EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨hJ, qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact envR_foldPlus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN Jq hJ ω hσ' hS1 (fun b hb hb' => hatomP L j b (φ b) (mem_filter.mp hb).2 hb')
  have hm : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      ((∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ) →
      EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) (dec L) j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨hJ, qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact envR_foldMinus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN Jq hJ ω hσ' hS1 (fun b hb hb' => hatomM L j b (φ b) (mem_filter.mp hb).2 hb')
  obtain ⟨_, _, _, _, _, h1, h2, h3, h4, h5⟩ := hfold_choice_opt _ _ hK₀0
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _)
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _) hP0nn hprod hR
    hR0 _ _ _ _ _ _ hBG hp hm
  refine ⟨_, _, _, _, _, h1, h2, h3, h4, h5.trans ?_⟩
  unfold rchOptEnvR
  apply Finset.single_le_sum (f := fun j' => rchOpt _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchOpt_nonneg _ hK₀0
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _)
    (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _) hCr _ _ _ _ _ _
    (fun φ => prod_nonneg fun b _ => mul_nonneg (abs_nonneg _)
      (DensityFibre.bpieceD_nonneg D L b (φ b))) hBG
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)

/-- **The re-optimized `rch` of `fixC`, left**: DC3's `rchFixL` with
`SharpBase.rchOpt` (the AM–GM ratio optimized against the whole bounds) in place of
`HfoldAlgebra.rchVal`. -/
noncomputable def rchOptFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchOpt (smallPiece m₀ blk D L)
    ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))
    (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus)
    (fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus)
    (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
      (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
      density (blockScale * L) A)
    (fun φ => EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
      (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => EnvelopeInputs.foldedPlus (D.FS.cut j)
      (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
      (fun v x => pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
        (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)
    (fun φ => EnvelopeInputs.foldedMinus (D.FS.cut j)
      (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
      (fun v x => pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
        (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)

/-- **The re-optimized `rch` of `fixC`, right**: DC3's `rchFixR` with
`SharpBase.rchOpt` (the AM–GM ratio optimized against the whole bounds) in place of
`HfoldAlgebra.rchVal`. -/
noncomputable def rchOptFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchOpt (smallPiece m₀ blk D L)
    ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) * D.Y L A *
      ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1))
    (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus)
    (fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus)
    (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
      (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
      density (blockScale * L) A)
    (fun φ => EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
      (DensityFibre.bpieceD D L) φ)
    (fun φ => ∏ b, DensityFibre.bpieceG D L b (φ b))
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => ∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
      ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
      |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j b.1
        (φ b.1)) x|)
    (fun φ => EnvelopeInputs.foldedPlus (D.FS.cut j)
      (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
      (fun v x => pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
        (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)
    (fun φ => EnvelopeInputs.foldedMinus (D.FS.cut j)
      (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
      (fun v x => pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
        (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
        (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
        ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ)

/-- **DC2's `hfold` for `fixC` (L, `Sh.fixM.hdiffL`), re-optimized remainder**
(`lem:sharp-first`, `lem:record:folded-energy`, `prop:record:density-structured`): DC3's
`hfold_fixL_paper` with `rch = rchOptFixL`; DC3's proof, with
`SharpBase.hfold_choice_opt` in place of `hfold_choice`. -/
theorem hfoldOpt_fixL_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool)
          (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ RecordExpansion.countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, DensityFibre.HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
              stageTau L) * (fixLambda hcop L A S 0 Jq ω * (fixedPrice pr h
              (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)))) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedPlus (D.FS.cut j)
              (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.u D.S.Q.u
                (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedMinus (D.FS.cut j)
              (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.u D.S.Q.u
                (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rp φ +
            (∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rm φ) / t) / 2 ≤
            rchOptFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ) := by
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  have hsc := eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) 1 0 0
    (by norm_num [blockScale]) hM0 hQ1
  filter_upwards [hsc, eventually_ge_atTop 2] with L hscL hL
  intro C hC hk A hA hY S _hS Jq ω f σ hσ0 j _hj
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hθ : (0 : ℝ) < densityExponent := by unfold densityExponent; norm_num
  have hθ2 : 2 * (densityExponent / 72) ≤ 1 := by unfold densityExponent; norm_num
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hY0 : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  -- the density is positive
  have hα : 0 < density (blockScale * L) A := by
    have hlow0 : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
      mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    have hYpos := lt_of_le_of_lt hlow0 hY
    rcases Finset.eq_empty_or_nonempty A with hA0 | hA0
    · rw [hA0, dataY_empty] at hYpos
      exact absurd hYpos (lt_irrefl 0)
    · exact density_pos_of_nonempty (Nat.mul_pos (by norm_num [blockScale]) (by omega)) hA0
  set u := scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
        ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
          ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  set U := ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) with hU
  have hU0 : 0 ≤ U := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
    · exact zero_le_one
  set K₀ := (1 + u) * D.Y L A * U with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (mul_nonneg (by linarith) hY0) hU0
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).1)
      (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).1)
      (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.2.1)
      (fun _ v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.2.2)
      (fun _ v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.1))
    (fun _ => True) a densityExponent (density (blockScale * L) A) with hP0def
  have hP0 : P0 = fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      fixLambda hcop L A S 0 Jq ω := by
    rw [hP0def, fixMainPrice_eq hcop (crtModuli m₀ blk paperTail L) (by omega) D.S.Q.u
      D.S.Q.hu ∅ A hA.1 hα a densityExponent S 0 Jq ω (fun e => by simp)]
    have hK : (0 : ℝ) < (blockScale : ℝ) ^ (2 * densityExponent / 72) :=
      Real.rpow_pos_of_pos (by norm_num [blockScale]) _
    unfold fixedPrice fixLambda EnvelopeInputsBlock.priceExponent stepR
    simp only [prod_empty, mul_one, leastSquare_one, Nat.cast_one, Real.one_rpow, one_mul]
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun e _ => ?_
    split_ifs
    · field_simp
    · ring
  have hP0nn : 0 ≤ P0 :=
    fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω id
  have hprod : fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus *
      fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus = P0 ^ 2 :=
    DensityFibre.mainPrice_fold_mul (D.FS.cut j)
      (paperPrice (crtModuli m₀ blk paperTail L) ∅
        (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).1)
        (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A
        (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).1)
        (fun v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.2.1)
        (fun _ v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.2.2)
        (fun _ v => (fixSlots hcop D.S.Q.u L S 0 Jq ω v).2.1))
      a densityExponent (density (blockScale * L) A)
  have hΛ0 : 0 ≤ fixLambda hcop L A S 0 Jq ω := fixLambda_nonneg hcop L A S 0 Jq ω
  have hcond0 : 0 ≤ fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq :=
    fixedPrice_nonneg pr h _ S Jq
  have hR : 2 * (K₀ * P0) ≤ 2 * ((1 + u) * (fixLambda hcop L A S 0 Jq ω *
      (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A * U))) := by
    rw [hP0, hK₀]
    exact le_of_eq (by ring)
  have hR0 : 0 ≤ 2 * ((1 + u) * (fixLambda hcop L A S 0 Jq ω *
      (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A * U))) := by
    have : 0 ≤ 1 + u := by linarith
    positivity
  -- the selected atoms of an admissible piece are nonempty
  obtain ⟨b₀, hb₀⟩ : ∃ b, σ b ≠ none := by
    by_contra hcon
    push Not at hcon
    exact hσ0 (funext hcon)
  have hEne : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      (DensityFibre.hTermAtoms D L φ).Nonempty := by
    intro φ hφ
    refine ⟨b₀, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    exact hpieceIsMu_false_of_coef D L f σ j b₀ hb₀ (φ b₀) (hφ b₀)
  have hCr : 0 ≤ dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
      (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
      (L : ℝ) ^ (-σ') * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg (dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le)
      (Nat.cast_nonneg _) hC1.le hC71.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  have hBG : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ ∏ b, DensityFibre.bpieceG D L b (φ b) :=
    fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)
  have hw : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ EnvelopeInputs.choiceWeight
      (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ := fun φ =>
    prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))
  have hp : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      smallPiece m₀ blk D L φ →
      EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
        (fun v x => pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact fix_foldPlus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN D.S.Q.u S 0 Jq ω hσ' hS1 (fun b hb hb' => hatomP L j b (φ b) (mem_filter.mp hb).2 hb')
  have hm : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      smallPiece m₀ blk D L φ →
      EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
        (fun v x => pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact fix_foldMinus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN D.S.Q.u S 0 Jq ω hσ' hS1 (fun b hb hb' => hatomM L j b (φ b) (mem_filter.mp hb).2 hb')
  obtain ⟨_, _, _, _, _, h1, h2, h3, h4, h5⟩ := hfold_choice_opt _ _ hK₀0
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _)
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _) hP0nn hprod hR
    hR0 _ _ _ _ _ _ hBG hp hm
  refine ⟨_, _, _, _, _, h1, h2, h3, h4, h5.trans ?_⟩
  unfold rchOptFixL
  apply Finset.single_le_sum (f := fun j' => rchOpt _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchOpt_nonneg _ hK₀0
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _)
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _) hCr _ _ _ _ _ _
    (fun φ => prod_nonneg fun b _ => mul_nonneg (abs_nonneg _)
      (DensityFibre.bpieceD_nonneg D L b (φ b))) hBG
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)

/-- **DC2's `hfold` for `fixC` (R, `Sh.fixM.hdiffR`), re-optimized remainder**
(`lem:sharp-first`, `lem:record:folded-energy`, `prop:record:density-structured`): DC3's
`hfold_fixR_paper` with `rch = rchOptFixR`; DC3's proof, with
`SharpBase.hfold_choice_opt` in place of `hfold_choice`. -/
theorem hfoldOpt_fixR_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
    (hC71 : 0 < C71) (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (ha : 0 ≤ a)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (hne : ∀ β, ∃ i, blk i = β) {σ' : ℝ} (hσ' : 0 ≤ σ')
    (hS1 : ε₀ / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatomP : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1)
    (hatomM : ∀ L j b x, DensityFibre.hpieceIsMu D L b x = false →
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.wrapInc D L) (dec L) j b x)),
      MixedLpBound (variationLaw _ hb) (72 / densityExponent) 1) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S : Finset E, S ≠ ∅ → ∀ Jq ω (f : BlockAtom Bk PaperJt L → Bool)
          (σ : ∀ b, Option (D.FS.Ib L b)),
        σ ≠ (fun _ => none) → ∀ j, 1 ≤ RecordExpansion.countVec (D.FS.tag L) σ j →
        ∃ (t Mp Mm : ℝ) (rp rm : (∀ b, DensityFibre.HPiece D L b) → ℝ), 0 < t ∧
          t * Mp + Mm / t ≤ 2 * ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
              stageTau L) * (fixLambda hcop L A S 1 Jq ω * (fixedPrice pr h
              (EnvelopeInputsBlock.priceExponent a) S Jq *
            D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)))) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedPlus (D.FS.cut j)
              (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.w D.S.Q.w
                (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mp + rp φ) ∧
          (∀ φ, (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
            EnvelopeInputs.foldedMinus (D.FS.cut j)
              (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
              (fun v x => pairInputs D.S.Q.w D.S.Q.w
                (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
                (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
                  ω ω v
                ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
              (∏ b, DensityFibre.bpieceG D L b (φ b)) * Mm + rm φ) ∧
          (t * ∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rp φ +
            (∑ φ, EnvelopeInputs.choiceWeight (DensityFibre.hpieceCoef D L f σ j)
              (DensityFibre.bpieceD D L) φ * rm φ) / t) / 2 ≤
            rchOptFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ) := by
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  have hsc := eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) 1 0 0
    (by norm_num [blockScale]) hM0 hQ1
  filter_upwards [hsc, eventually_ge_atTop 2] with L hscL hL
  intro C hC hk A hA hY S _hS Jq ω f σ hσ0 j _hj
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hθ : (0 : ℝ) < densityExponent := by unfold densityExponent; norm_num
  have hθ2 : 2 * (densityExponent / 72) ≤ 1 := by unfold densityExponent; norm_num
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hY0 : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  -- the density is positive
  have hα : 0 < density (blockScale * L) A := by
    have hlow0 : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
      mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    have hYpos := lt_of_le_of_lt hlow0 hY
    rcases Finset.eq_empty_or_nonempty A with hA0 | hA0
    · rw [hA0, dataY_empty] at hYpos
      exact absurd hYpos (lt_irrefl 0)
    · exact density_pos_of_nonempty (Nat.mul_pos (by norm_num [blockScale]) (by omega)) hA0
  set u := scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
        ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * ((modulus pr h : ℕ) : ℝ) ^ 2 *
          ((cliqueConstant m₀ D.S.ep : ℕ) : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  set U := ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) with hU
  have hU0 : 0 ≤ U := prod_nonneg fun b _ => by
    split_ifs
    · exact TheoremCBlock.Structured.wrapPrice_nonneg D L b
    · exact zero_le_one
  set K₀ := (1 + u) * D.Y L A * U with hK₀
  have hK₀0 : 0 ≤ K₀ := mul_nonneg (mul_nonneg (by linarith) hY0) hU0
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).1)
      (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).1)
      (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.2.1)
      (fun _ v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.2.2)
      (fun _ v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.1))
    (fun _ => True) a densityExponent (density (blockScale * L) A) with hP0def
  have hP0 : P0 = fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
      fixLambda hcop L A S 1 Jq ω := by
    rw [hP0def, fixMainPrice_eq hcop (crtModuli m₀ blk paperTail L) (by omega) D.S.Q.w
      D.S.Q.hw ∅ A hA.1 hα a densityExponent S 1 Jq ω (fun e => by simp)]
    have hK : (0 : ℝ) < (blockScale : ℝ) ^ (2 * densityExponent / 72) :=
      Real.rpow_pos_of_pos (by norm_num [blockScale]) _
    unfold fixedPrice fixLambda EnvelopeInputsBlock.priceExponent stepR
    simp only [prod_empty, mul_one, leastSquare_one, Nat.cast_one, Real.one_rpow, one_mul]
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun e _ => ?_
    split_ifs
    · field_simp
    · ring
  have hP0nn : 0 ≤ P0 :=
    fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω id
  have hprod : fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus *
      fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus = P0 ^ 2 :=
    DensityFibre.mainPrice_fold_mul (D.FS.cut j)
      (paperPrice (crtModuli m₀ blk paperTail L) ∅
        (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).1)
        (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.2.1) L)
      (paperMeanDensity (FiniteLaw.uniform Unit) A
        (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).1)
        (fun v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.2.1)
        (fun _ v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.2.2)
        (fun _ v => (fixSlots hcop D.S.Q.w L S 1 Jq ω v).2.1))
      a densityExponent (density (blockScale * L) A)
  have hΛ0 : 0 ≤ fixLambda hcop L A S 1 Jq ω := fixLambda_nonneg hcop L A S 1 Jq ω
  have hcond0 : 0 ≤ fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq :=
    fixedPrice_nonneg pr h _ S Jq
  have hR : 2 * (K₀ * P0) ≤ 2 * ((1 + u) * (fixLambda hcop L A S 1 Jq ω *
      (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A * U))) := by
    rw [hP0, hK₀]
    exact le_of_eq (by ring)
  have hR0 : 0 ≤ 2 * ((1 + u) * (fixLambda hcop L A S 1 Jq ω *
      (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A * U))) := by
    have : 0 ≤ 1 + u := by linarith
    positivity
  -- the selected atoms of an admissible piece are nonempty
  obtain ⟨b₀, hb₀⟩ : ∃ b, σ b ≠ none := by
    by_contra hcon
    push Not at hcon
    exact hσ0 (funext hcon)
  have hEne : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      (DensityFibre.hTermAtoms D L φ).Nonempty := by
    intro φ hφ
    refine ⟨b₀, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    exact hpieceIsMu_false_of_coef D L f σ j b₀ hb₀ (φ b₀) (hφ b₀)
  have hCr : 0 ≤ dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
      (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
      (L : ℝ) ^ (-σ') * density (blockScale * L) A :=
    mul_nonneg (mul_nonneg (dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le)
      (Nat.cast_nonneg _) hC1.le hC71.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (density_nonneg _ _)
  have hBG : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ ∏ b, DensityFibre.bpieceG D L b (φ b) :=
    fun φ => prod_nonneg fun b _ => DensityFibre.bpieceG_nonneg D L b (φ b)
  have hw : ∀ φ : (∀ b, DensityFibre.HPiece D L b), 0 ≤ EnvelopeInputs.choiceWeight
      (DensityFibre.hpieceCoef D L f σ j) (DensityFibre.bpieceD D L) φ := fun φ =>
    prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))
  have hp : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      smallPiece m₀ blk D L φ →
      EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
        (fun v x => pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact fix_foldPlus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN D.S.Q.w S 1 Jq ω hσ' hS1 (fun b hb hb' => hatomP L j b (φ b) (mem_filter.mp hb).2 hb')
  have hm : ∀ φ : (∀ b, DensityFibre.HPiece D L b),
      (∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0) →
      smallPiece m₀ blk D L φ →
      EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j)
        (fun v x => pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
        (∏ b, DensityFibre.bpieceG D L b (φ b)) *
          (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus) +
        (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) (dec L) j
            b.1 (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
          (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
          density (blockScale * L) A) := by
    intro φ hφ hs
    obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ := hs
    exact fix_foldMinus_piece_hfold hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hscL hM0 dvd_rfl hpar
      hsel (dec L) j f σ φ hφ (prod_crtModuli_ne_one D hne (hEne φ hφ)) hDE hqE hcE hcE0 hcQ hcopE
      hqN D.S.Q.w S 1 Jq ω hσ' hS1 (fun b hb hb' => hatomM L j b (φ b) (mem_filter.mp hb).2 hb')
  obtain ⟨_, _, _, _, _, h1, h2, h3, h4, h5⟩ := hfold_choice_opt _ _ hK₀0
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _)
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _) hP0nn hprod hR
    hR0 _ _ _ _ _ _ hBG hp hm
  refine ⟨_, _, _, _, _, h1, h2, h3, h4, h5.trans ?_⟩
  unfold rchOptFixR
  apply Finset.single_le_sum (f := fun j' => rchOpt _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchOpt_nonneg _ hK₀0
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _)
    (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _) hCr _ _ _ _ _ _
    (fun φ => prod_nonneg fun b _ => mul_nonneg (abs_nonneg _)
      (DensityFibre.bpieceD_nonneg D L b (φ b))) hBG
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)

end Sarkozy.SharpBase
