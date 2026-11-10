module

public import Sarkozy.SharpBase2.PerTerm
public import Sarkozy.SharpBase.HfoldOpt

@[expose] public section

/-!
# The four per-choice bounds of `hdiff` with per-term geometric means

SH2 (7 November 2026). DC3's chain bounds for the folded energies of the pieces
(`DensityChain2.*_foldPlus/Minus_piece_hfold`, assembled in DC3's `hfold_env/fixL/R_paper`,
copied in `SharpBase.HfoldOpt`) are combined here per expanded term
(`SharpBase2.choice_bound_perterm`), as in the paper's proof of `lem:sharp-first`, instead of by
DC2's whole-choice folding. The proofs are DC3's up to the per-piece bounds `hp`, `hm`; the last
step is new. The conclusions are the per-choice hypotheses `hterm` of DC2's
`diff_bound_of_coupled_loc`, with remainders `rchPTEnvL/R`, `rchPTFixL/R`:

* `rchPT`: `∑_φ w_φ pieceRem(φ)` at DC3's per-tag data: main × chain-remainder cross terms and
  chain² at the small pieces, `√𝔈₊ √𝔈₋` at the large pieces;
* **`hterm_envL/R_paper`**, **`hterm_fixL/R_paper`**.
-/

namespace Sarkozy.SharpBase2

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

/-- **The per-term remainder of field 30 (`Sh.envM.hdiffL`)**: DC3's per-tag data summed with
`SharpBase2.rchPT` (per-term geometric means). -/
noncomputable def rchPTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchPT (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **The per-choice bound of field 30 (`Sh.envM.hdiffL`) with per-term geometric means**
(`lem:sharp-first` as in the paper, `lem:record:folded-energy` per expanded term,
`prop:record:density-structured`): DC3's chain bounds (`hfold_envL_paper`), combined by
`choice_bound_perterm`; the remainder is `rchPTEnvL`. -/
theorem hterm_envL_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
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
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.envIncL D L) f σ)))
            (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)| ≤
          ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
            (envLambda hcop L A Jq ω *
              (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
              D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)))) *
            RecordExpansion.tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ +
          rchPTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ) := by
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
  have hM0K : 0 ≤ K₀ * P0 := mul_nonneg hK₀0 hP0nn
  have hprodK : (K₀ * envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldPlus) *
      (K₀ * envFoldP (a := a) m₀ blk hcop D.index.u L A Jq ω (D.FS.cut j).foldMinus) =
        (K₀ * P0) ^ 2 := by
    rw [mul_pow, ← hprod]
    ring
  have hMM : K₀ * P0 ≤ (1 + u) * (envLambda hcop L A Jq ω *
      (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A * U)) :=
    le_of_mul_le_mul_left hR (by norm_num)
  refine (choice_bound_perterm blk (dec L) (TheoremCBlock.Structured.envIncL D L)
    (prefix_pairwise (hpair L)) (DensityFibre.envIncL_nonneg D L) f σ j
    (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)
    (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
    (mul_nonneg hK₀0 (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _))
    (mul_nonneg hK₀0 (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.u L A Jq ω _))
    hM0K hprodK hMM hCr _ _
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hp hm).trans ?_
  refine add_le_add le_rfl ?_
  unfold rchPTEnvL
  apply Finset.single_le_sum (f := fun j' => rchPT _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchPT_nonneg _ _ _ _ _ _ _ _ _ _ _ fun φ => prod_nonneg fun b _ =>
    mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))

/-- **The per-term remainder of field 31 (`Sh.envM.hdiffR`)**: DC3's per-tag data summed with
`SharpBase2.rchPT` (per-term geometric means). -/
noncomputable def rchPTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchPT (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **The per-choice bound of field 31 (`Sh.envM.hdiffR`) with per-term geometric means**
(`lem:sharp-first` as in the paper, `lem:record:folded-energy` per expanded term,
`prop:record:density-structured`): DC3's chain bounds (`hfold_envR_paper`), combined by
`choice_bound_perterm`; the remainder is `rchPTEnvR`. -/
theorem hterm_envR_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
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
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.envIncR D L) f σ)))
            (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)| ≤
          ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
            (envLambda hcop L A Jq ω *
              (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
              D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)))) *
            RecordExpansion.tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ +
          rchPTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ) := by
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
  have hM0K : 0 ≤ K₀ * P0 := mul_nonneg hK₀0 hP0nn
  have hprodK : (K₀ * envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldPlus) *
      (K₀ * envFoldP (a := a) m₀ blk hcop D.index.w L A Jq ω (D.FS.cut j).foldMinus) =
        (K₀ * P0) ^ 2 := by
    rw [mul_pow, ← hprod]
    ring
  have hMM : K₀ * P0 ≤ (1 + u) * (envLambda hcop L A Jq ω *
      (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A * U)) :=
    le_of_mul_le_mul_left hR (by norm_num)
  refine (choice_bound_perterm blk (dec L) (TheoremCBlock.Structured.envIncR D L)
    (prefix_pairwise (hpair L)) (DensityFibre.envIncR_nonneg D L) f σ j
    (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
              (revealedInputCRT blk hcop D L A Jq)
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)
    (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
    (mul_nonneg hK₀0 (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _))
    (mul_nonneg hK₀0 (envFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.index.w L A Jq ω _))
    hM0K hprodK hMM hCr _ _
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hp hm).trans ?_
  refine add_le_add le_rfl ?_
  unfold rchPTEnvR
  apply Finset.single_le_sum (f := fun j' => rchPT _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchPT_nonneg _ _ _ _ _ _ _ _ _ _ _ fun φ => prod_nonneg fun b _ =>
    mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))

/-- **The per-term remainder of `fixC` (L, `Sh.fixM.hdiffL`)**: DC3's per-tag data summed with
`SharpBase2.rchPT` (per-term geometric means). -/
noncomputable def rchPTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchPT (smallPiece m₀ blk D L)
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

/-- **The per-choice bound of `fixC` (L, `Sh.fixM.hdiffL`) with per-term geometric means**
(`lem:sharp-first` as in the paper, `lem:record:folded-energy` per expanded term,
`prop:record:density-structured`): DC3's chain bounds (`hfold_fixL_paper`), combined by
`choice_bound_perterm`; the remainder is `rchPTFixL`. -/
theorem hterm_fixL_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
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
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.wrapInc D L) f σ)))
            (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)| ≤
          ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
            (fixLambda hcop L A S 0 Jq ω *
              (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
              D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)))) *
            RecordExpansion.tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ +
          rchPTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ) := by
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
  have hM0K : 0 ≤ K₀ * P0 := mul_nonneg hK₀0 hP0nn
  have hprodK : (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldPlus) *
      (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.u L A S 0 Jq ω (D.FS.cut j).foldMinus) =
        (K₀ * P0) ^ 2 := by
    rw [mul_pow, ← hprod]
    ring
  have hMM : K₀ * P0 ≤ (1 + u) * (fixLambda hcop L A S 0 Jq ω *
      (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A * U)) :=
    le_of_mul_le_mul_left hR (by norm_num)
  refine (choice_bound_perterm blk (dec L) (TheoremCBlock.Structured.wrapInc D L)
    (prefix_pairwise (hpair L)) (DensityFibre.wrapInc_nonneg D L) f σ j
    (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)
    (smallPiece m₀ blk D L)
    (mul_nonneg hK₀0 (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _))
    (mul_nonneg hK₀0 (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.u L A S 0 Jq ω _))
    hM0K hprodK hMM hCr _ _
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hp hm).trans ?_
  refine add_le_add le_rfl ?_
  unfold rchPTFixL
  apply Finset.single_le_sum (f := fun j' => rchPT _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchPT_nonneg _ _ _ _ _ _ _ _ _ _ _ fun φ => prod_nonneg fun b _ =>
    mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))

/-- **The per-term remainder of `fixC` (R, `Sh.fixM.hdiffR`)**: DC3's per-tag data summed with
`SharpBase2.rchPT` (per-term geometric means). -/
noncomputable def rchPTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) : ℝ :=
  ∑ j : D.FS.Tag, rchPT (smallPiece m₀ blk D L)
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

/-- **The per-choice bound of `fixC` (R, `Sh.fixM.hdiffR`) with per-term geometric means**
(`lem:sharp-first` as in the paper, `lem:record:folded-energy` per expanded term,
`prop:record:density-structured`): DC3's chain bounds (`hfold_fixR_paper`), combined by
`choice_bound_perterm`; the remainder is `rchPTFixR`. -/
theorem hterm_fixR_paper {ε₀ C1 C71 : ℝ} (hdcb : DCBlockProp ε₀ C1 C71) (hC1 : 0 < C1)
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
        |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
            (sharpPiece D L (TheoremCBlock.Structured.wrapInc D L) f σ)))
            (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)| ≤
          ((1 + scaleU blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep) stageTau L) *
            (fixLambda hcop L A S 1 Jq ω *
              (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
              D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)))) *
            RecordExpansion.tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if f b then 0 else D.GB.uprice L b) j σ +
          rchPTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ) := by
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
  have hM0K : 0 ≤ K₀ * P0 := mul_nonneg hK₀0 hP0nn
  have hprodK : (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldPlus) *
      (K₀ * fixFoldP (a := a) m₀ blk hcop D.S.Q.w L A S 1 Jq ω (D.FS.cut j).foldMinus) =
        (K₀ * P0) ^ 2 := by
    rw [mul_pow, ← hprod]
    ring
  have hMM : K₀ * P0 ≤ (1 + u) * (fixLambda hcop L A S 1 Jq ω *
      (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A * U)) :=
    le_of_mul_le_mul_left hR (by norm_num)
  refine (choice_bound_perterm blk (dec L) (TheoremCBlock.Structured.wrapInc D L)
    (prefix_pairwise (hpair L)) (DensityFibre.wrapInc_nonneg D L) f σ j
    (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
              (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L)
              ω ω)
    (smallPiece m₀ blk D L)
    (mul_nonneg hK₀0 (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _))
    (mul_nonneg hK₀0 (fixFoldP_nonneg (a := a) (m₀ := m₀) (blk := blk) hcop D.S.Q.w L A S 1 Jq ω _))
    hM0K hprodK hMM hCr _ _
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
    (fun φ => prod_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hp hm).trans ?_
  refine add_le_add le_rfl ?_
  unfold rchPTFixR
  apply Finset.single_le_sum (f := fun j' => rchPT _ _ _ _ _ _ _ _ _ _ _) _ (mem_univ j)
  intro j' _
  exact rchPT_nonneg _ _ _ _ _ _ _ _ _ _ _ fun φ => prod_nonneg fun b _ =>
    mul_nonneg (abs_nonneg _) (DensityFibre.bpieceD_nonneg D L b (φ b))

end Sarkozy.SharpBase2
