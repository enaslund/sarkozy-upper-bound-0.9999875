module

public import Sarkozy.DensityChain2.PiecePrice

@[expose] public section

/-!
# The per-piece inequality of DC2's `hfold` for `envC` (`lem:sharp-first`)

DC2's `hfold` (in `DensityFibre.envHdiffL_of_folded`) asks, for every admissible piece `φ`,
`𝔈₊(φ) ≤ (∏_𝔟 bpieceG_𝔟(φ_𝔟)) M₊ + r₊(φ)` with `M₊` independent of `φ`. This file proves it in
that shape for every piece to which the chain applies (`q_E ≤ N^τ`):

`𝔈₊(φ) ≤ (∏ bpieceG) · (1 + u_L) Y ∏_f u_𝔟 · Π_∅(envSlots ∘ φ₊) + ∏_E ‖Λ_𝔟‖ · C_dc L^{-σ} α`,

where `Π_∅(envSlots ∘ φ₊)` is the main price of the plus-folded slot data with no selected atom,
the same for every piece. It combines `env_foldPlus_piece_paper` (the chain),
`mainPrice_split` (`Π = sq(D_E)^a Π_∅`) and `piecePrice_plus_le` (the piece prices).

The choice of `t`, `M_±` and `Λ`, the pieces with `q_E > N^τ`, and the assembly of `hfold` are in
`HfoldAlgebra` and `Hfold`; the summation of `rch` is open (see the report, §4).
-/

namespace Sarkozy.DensityChain2

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The per-piece inequality of `hfold` (plus fold, `envC`, left increments)**, for a piece
with `q_E ≤ N^τ` (the modulus conditions) and `D_E ≠ 1`. -/
theorem env_foldPlus_piece_hfold {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ' : ℝ} (hσ : 0 ≤ σ') (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.envIncL D L) dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) dec j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * D.Y L A *
          (∏ b, if f b then TheoremCBlock.Structured.envPriceL D L b else 1) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.1))
            (fun _ => True) a θ (density (blockScale * L) A)) +
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) dec j b.1
            (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ') * density (blockScale * L) A) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hQ : ∀ b, IsPositiveRecord (TheoremCBlock.Structured.envIncL D L b) :=
    fun b => isPositiveRecord_envIncL D L b
  have hchain := env_foldPlus_piece_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (TheoremCBlock.Structured.envIncL D L) hQ dec j φ hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω
    hσ hS1 hatom
  -- the slot moduli of the folded data are coprime to `D_E`
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcopv : ∀ v, ((envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).1).Coprime
      (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) := by
    intro v
    apply Nat.Coprime.prod_right
    intro k _
    rw [envSlots_fst hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)]
    unfold envD0
    split
    · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
    · exact Nat.coprime_one_left _
  rw [mainPrice_split _ Es _ _ L _ a θ _ hcopv] at hchain
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  have hprice := piecePrice_plus_le D L (hpair L) (TheoremCBlock.Structured.envIncL D L) hQ dec j
    f σ φ hφ hselF (TheoremCBlock.Structured.envPriceL D L)
    (fun b => envIncL_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
  set G := ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
    |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) dec j b.1
      (φ b.1)) x| with hG
  set Ssq := ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a with hSsq
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).1)
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).1)
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
      (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
      (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldPlus v)).2.1))
    (fun _ => True) a θ (density (blockScale * L) A) with hP0
  set U := ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) with hU
  set BG := ∏ b, DensityFibre.bpieceG D L b (φ b) with hBG
  set uL := scaleU blockScale M0 Qcl stageTau L with huL
  set Cr := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
    (L : ℝ) ^ (-σ') * density (blockScale * L) A with hCr
  have hY : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 : 0 ≤ uL := by
    rw [huL]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  have hP0nn : 0 ≤ P0 := by
    rw [hP0]
    unfold mainPrice paperPrice paperMeanDensity
    refine mul_nonneg (prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
      (prod_nonneg fun v _ => Real.rpow_nonneg (div_nonneg ?_ (density_nonneg _ _)) _)
    unfold FiniteLaw.expect
    exact sum_nonneg fun _ _ => mul_nonneg (FiniteLaw.nonneg _ _) (by positivity)
  have hmain : G * ((1 + uL) * (Ssq * P0) * D.Y L A) ≤ BG * ((1 + uL) * D.Y L A * U * P0) := by
    have hk : 0 ≤ (1 + uL) * D.Y L A * P0 := mul_nonneg (mul_nonneg (by linarith) hY) hP0nn
    calc G * ((1 + uL) * (Ssq * P0) * D.Y L A) = (G * Ssq) * ((1 + uL) * D.Y L A * P0) := by ring
      _ ≤ (BG * U) * ((1 + uL) * D.Y L A * P0) := mul_le_mul_of_nonneg_right hprice hk
      _ = BG * ((1 + uL) * D.Y L A * U * P0) := by ring
  calc _ ≤ |EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncL D L) dec j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| := le_abs_self _
    _ ≤ G * ((1 + uL) * (Ssq * P0) * D.Y L A + Cr) := hchain
    _ = G * ((1 + uL) * (Ssq * P0) * D.Y L A) + G * Cr := by ring
    _ ≤ BG * ((1 + uL) * D.Y L A * U * P0) + G * Cr := by linarith [hmain]

/-- **The per-piece inequality of `hfold` (minus fold, `envC`, left increments)**, for a piece
with `q_E ≤ N^τ` (the modulus conditions) and `D_E ≠ 1`. -/
theorem env_foldMinus_piece_hfold {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ' : ℝ} (hσ : 0 ≤ σ') (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.envIncL D L) dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) dec j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * D.Y L A *
          (∏ b, if f b then TheoremCBlock.Structured.envPriceL D L b else 1) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.1))
            (fun _ => True) a θ (density (blockScale * L) A)) +
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) dec j b.1
            (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ') * density (blockScale * L) A) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hQ : ∀ b, IsPositiveRecord (TheoremCBlock.Structured.envIncL D L b) :=
    fun b => isPositiveRecord_envIncL D L b
  have hchain := env_foldMinus_piece_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (TheoremCBlock.Structured.envIncL D L) hQ dec j φ hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω
    hσ hS1 hatom
  -- the slot moduli of the folded data are coprime to `D_E`
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcopv : ∀ v, ((envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).1).Coprime
      (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) := by
    intro v
    apply Nat.Coprime.prod_right
    intro k _
    rw [envSlots_fst hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)]
    unfold envD0
    split
    · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
    · exact Nat.coprime_one_left _
  rw [mainPrice_split _ Es _ _ L _ a θ _ hcopv] at hchain
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  have hprice := piecePrice_minus_le D L (hpair L) (TheoremCBlock.Structured.envIncL D L) hQ dec j
    f σ φ hφ hselF (TheoremCBlock.Structured.envPriceL D L)
    (fun b => envIncL_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
  set G := ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
    |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) dec j b.1
      (φ b.1)) x| with hG
  set Ssq := ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a with hSsq
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).1)
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).1)
      (fun v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
      (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
      (fun _ v => (envSlots hcop D.index.u L Jq ω ((D.FS.cut j).foldMinus v)).2.1))
    (fun _ => True) a θ (density (blockScale * L) A) with hP0
  set U := ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) with hU
  set BG := ∏ b, DensityFibre.bpieceG D L b (φ b) with hBG
  set uL := scaleU blockScale M0 Qcl stageTau L with huL
  set Cr := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
    (L : ℝ) ^ (-σ') * density (blockScale * L) A with hCr
  have hY : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 : 0 ≤ uL := by
    rw [huL]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  have hP0nn : 0 ≤ P0 := by
    rw [hP0]
    unfold mainPrice paperPrice paperMeanDensity
    refine mul_nonneg (prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
      (prod_nonneg fun v _ => Real.rpow_nonneg (div_nonneg ?_ (density_nonneg _ _)) _)
    unfold FiniteLaw.expect
    exact sum_nonneg fun _ _ => mul_nonneg (FiniteLaw.nonneg _ _) (by positivity)
  have hmain : G * ((1 + uL) * (Ssq * P0) * D.Y L A) ≤ BG * ((1 + uL) * D.Y L A * U * P0) := by
    have hk : 0 ≤ (1 + uL) * D.Y L A * P0 := mul_nonneg (mul_nonneg (by linarith) hY) hP0nn
    calc G * ((1 + uL) * (Ssq * P0) * D.Y L A) = (G * Ssq) * ((1 + uL) * D.Y L A * P0) := by ring
      _ ≤ (BG * U) * ((1 + uL) * D.Y L A * P0) := mul_le_mul_of_nonneg_right hprice hk
      _ = BG * ((1 + uL) * D.Y L A * U * P0) := by ring
  calc _ ≤ |EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncL D L) dec j)
        (fun v x => pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| := le_abs_self _
    _ ≤ G * ((1 + uL) * (Ssq * P0) * D.Y L A + Cr) := hchain
    _ = G * ((1 + uL) * (Ssq * P0) * D.Y L A) + G * Cr := by ring
    _ ≤ BG * ((1 + uL) * D.Y L A * U * P0) + G * Cr := by linarith [hmain]

/-- **The per-piece inequality of `hfold` (plus fold, `fixC`, wrapping increments)**, for a piece
with `q_E ≤ N^τ` (the modulus conditions) and `D_E ≠ 1`. -/
theorem fix_foldPlus_piece_hfold {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (u : E → reservedCut.Half) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ' : ℝ} (hσ : 0 ≤ σ') (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.wrapInc D L) dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) dec j)
        (fun v x => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * D.Y L A *
          (∏ b, if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.1))
            (fun _ => True) a θ (density (blockScale * L) A)) +
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) dec j b.1
            (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ') * density (blockScale * L) A) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hQ : ∀ b, IsPositiveRecord (TheoremCBlock.Structured.wrapInc D L b) :=
    fun b => isPositiveRecord_wrapInc D L b
  have hchain := fix_foldPlus_piece_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (TheoremCBlock.Structured.wrapInc D L) hQ dec j φ hne hDE hqE hcE hcE0 hcQ hcopE hqN u S t Jq
    ω hσ hS1 hatom
  -- the slot moduli of the folded data are coprime to `D_E`
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcopv : ∀ v, ((fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).1).Coprime
      (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) := by
    intro v
    apply Nat.Coprime.prod_right
    intro k _
    rw [fixSlots_fst hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)]
    unfold fixD0
    split
    · split_ifs
      · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
      · exact Nat.coprime_one_left _
    · exact Nat.coprime_one_left _
  rw [mainPrice_split _ Es _ _ L _ a θ _ hcopv] at hchain
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  have hprice := piecePrice_plus_le D L (hpair L) (TheoremCBlock.Structured.wrapInc D L) hQ dec j
    f σ φ hφ hselF (TheoremCBlock.Structured.wrapPrice D L)
    (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
  set G := ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
    |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) dec j b.1
      (φ b.1)) x| with hG
  set Ssq := ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a with hSsq
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).1)
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).1)
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
      (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
      (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldPlus v)).2.1))
    (fun _ => True) a θ (density (blockScale * L) A) with hP0
  set U := ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) with hU
  set BG := ∏ b, DensityFibre.bpieceG D L b (φ b) with hBG
  set uL := scaleU blockScale M0 Qcl stageTau L with huL
  set Cr := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
    (L : ℝ) ^ (-σ') * density (blockScale * L) A with hCr
  have hY : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 : 0 ≤ uL := by
    rw [huL]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  have hP0nn : 0 ≤ P0 := by
    rw [hP0]
    unfold mainPrice paperPrice paperMeanDensity
    refine mul_nonneg (prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
      (prod_nonneg fun v _ => Real.rpow_nonneg (div_nonneg ?_ (density_nonneg _ _)) _)
    unfold FiniteLaw.expect
    exact sum_nonneg fun _ _ => mul_nonneg (FiniteLaw.nonneg _ _) (by positivity)
  have hmain : G * ((1 + uL) * (Ssq * P0) * D.Y L A) ≤ BG * ((1 + uL) * D.Y L A * U * P0) := by
    have hk : 0 ≤ (1 + uL) * D.Y L A * P0 := mul_nonneg (mul_nonneg (by linarith) hY) hP0nn
    calc G * ((1 + uL) * (Ssq * P0) * D.Y L A) = (G * Ssq) * ((1 + uL) * D.Y L A * P0) := by ring
      _ ≤ (BG * U) * ((1 + uL) * D.Y L A * P0) := mul_le_mul_of_nonneg_right hprice hk
      _ = BG * ((1 + uL) * D.Y L A * U * P0) := by ring
  calc _ ≤ |EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.wrapInc D L) dec j)
        (fun v x => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| := le_abs_self _
    _ ≤ G * ((1 + uL) * (Ssq * P0) * D.Y L A + Cr) := hchain
    _ = G * ((1 + uL) * (Ssq * P0) * D.Y L A) + G * Cr := by ring
    _ ≤ BG * ((1 + uL) * D.Y L A * U * P0) + G * Cr := by linarith [hmain]

/-- **The per-piece inequality of `hfold` (minus fold, `fixC`, wrapping increments)**, for a piece
with `q_E ≤ N^τ` (the modulus conditions) and `D_E ≠ 1`. -/
theorem fix_foldMinus_piece_hfold {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (u : E → reservedCut.Half) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ' : ℝ} (hσ : 0 ≤ σ') (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.wrapInc D L) dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) dec j)
        (fun v x => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * D.Y L A *
          (∏ b, if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
              (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.1))
            (fun _ => True) a θ (density (blockScale * L) A)) +
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) dec j b.1
            (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ') * density (blockScale * L) A) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hQ : ∀ b, IsPositiveRecord (TheoremCBlock.Structured.wrapInc D L b) :=
    fun b => isPositiveRecord_wrapInc D L b
  have hchain := fix_foldMinus_piece_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (TheoremCBlock.Structured.wrapInc D L) hQ dec j φ hne hDE hqE hcE hcE0 hcQ hcopE hqN u S t Jq
    ω hσ hS1 hatom
  -- the slot moduli of the folded data are coprime to `D_E`
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcopv : ∀ v, ((fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).1).Coprime
      (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) := by
    intro v
    apply Nat.Coprime.prod_right
    intro k _
    rw [fixSlots_fst hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)]
    unfold fixD0
    split
    · split_ifs
      · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
      · exact Nat.coprime_one_left _
    · exact Nat.coprime_one_left _
  rw [mainPrice_split _ Es _ _ L _ a θ _ hcopv] at hchain
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  have hprice := piecePrice_minus_le D L (hpair L) (TheoremCBlock.Structured.wrapInc D L) hQ dec j
    f σ φ hφ hselF (TheoremCBlock.Structured.wrapPrice D L)
    (fun b => wrapInc_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
  set G := ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
    |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) dec j b.1
      (φ b.1)) x| with hG
  set Ssq := ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a with hSsq
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).1)
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).1)
      (fun v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
      (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
      (fun _ v => (fixSlots hcop u L S t Jq ω ((D.FS.cut j).foldMinus v)).2.1))
    (fun _ => True) a θ (density (blockScale * L) A) with hP0
  set U := ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) with hU
  set BG := ∏ b, DensityFibre.bpieceG D L b (φ b) with hBG
  set uL := scaleU blockScale M0 Qcl stageTau L with huL
  set Cr := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
    (L : ℝ) ^ (-σ') * density (blockScale * L) A with hCr
  have hY : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 : 0 ≤ uL := by
    rw [huL]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  have hP0nn : 0 ≤ P0 := by
    rw [hP0]
    unfold mainPrice paperPrice paperMeanDensity
    refine mul_nonneg (prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
      (prod_nonneg fun v _ => Real.rpow_nonneg (div_nonneg ?_ (density_nonneg _ _)) _)
    unfold FiniteLaw.expect
    exact sum_nonneg fun _ _ => mul_nonneg (FiniteLaw.nonneg _ _) (by positivity)
  have hmain : G * ((1 + uL) * (Ssq * P0) * D.Y L A) ≤ BG * ((1 + uL) * D.Y L A * U * P0) := by
    have hk : 0 ≤ (1 + uL) * D.Y L A * P0 := mul_nonneg (mul_nonneg (by linarith) hY) hP0nn
    calc G * ((1 + uL) * (Ssq * P0) * D.Y L A) = (G * Ssq) * ((1 + uL) * D.Y L A * P0) := by ring
      _ ≤ (BG * U) * ((1 + uL) * D.Y L A * P0) := mul_le_mul_of_nonneg_right hprice hk
      _ = BG * ((1 + uL) * D.Y L A * U * P0) := by ring
  calc _ ≤ |EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.wrapInc D L) dec j)
        (fun v x => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| := le_abs_self _
    _ ≤ G * ((1 + uL) * (Ssq * P0) * D.Y L A + Cr) := hchain
    _ = G * ((1 + uL) * (Ssq * P0) * D.Y L A) + G * Cr := by ring
    _ ≤ BG * ((1 + uL) * D.Y L A * U * P0) + G * Cr := by linarith [hmain]

/-- **The per-piece inequality of `hfold` (plus fold, `envC`, right increments)**, for a piece
with `q_E ≤ N^τ` (the modulus conditions) and `D_E ≠ 1`. -/
theorem envR_foldPlus_piece_hfold {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ' : ℝ} (hσ : 0 ≤ σ') (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLp D L
        (TheoremCBlock.Structured.envIncR D L) dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) dec j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * D.Y L A *
          (∏ b, if f b then TheoremCBlock.Structured.envPriceR D L b else 1) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.1))
            (fun _ => True) a θ (density (blockScale * L) A)) +
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) dec j b.1
            (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ') * density (blockScale * L) A) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hQ : ∀ b, IsPositiveRecord (TheoremCBlock.Structured.envIncR D L b) :=
    fun b => isPositiveRecord_envIncR D L b
  have hchain := envR_foldPlus_piece_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (TheoremCBlock.Structured.envIncR D L) hQ dec j φ hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω
    hσ hS1 hatom
  -- the slot moduli of the folded data are coprime to `D_E`
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcopv : ∀ v, ((envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).1).Coprime
      (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) := by
    intro v
    apply Nat.Coprime.prod_right
    intro k _
    rw [envSlots_fst hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)]
    unfold envD0
    split
    · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
    · exact Nat.coprime_one_left _
  rw [mainPrice_split _ Es _ _ L _ a θ _ hcopv] at hchain
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  have hprice := piecePrice_plus_le D L (hpair L) (TheoremCBlock.Structured.envIncR D L) hQ dec j
    f σ φ hφ hselF (TheoremCBlock.Structured.envPriceR D L)
    (fun b => envIncR_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
  set G := ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
    |lawDensity (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) dec j b.1
      (φ b.1)) x| with hG
  set Ssq := ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a with hSsq
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).1)
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).1)
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.1)
      (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.2.2)
      (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldPlus v)).2.1))
    (fun _ => True) a θ (density (blockScale * L) A) with hP0
  set U := ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) with hU
  set BG := ∏ b, DensityFibre.bpieceG D L b (φ b) with hBG
  set uL := scaleU blockScale M0 Qcl stageTau L with huL
  set Cr := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
    (L : ℝ) ^ (-σ') * density (blockScale * L) A with hCr
  have hY : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 : 0 ≤ uL := by
    rw [huL]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  have hP0nn : 0 ≤ P0 := by
    rw [hP0]
    unfold mainPrice paperPrice paperMeanDensity
    refine mul_nonneg (prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
      (prod_nonneg fun v _ => Real.rpow_nonneg (div_nonneg ?_ (density_nonneg _ _)) _)
    unfold FiniteLaw.expect
    exact sum_nonneg fun _ _ => mul_nonneg (FiniteLaw.nonneg _ _) (by positivity)
  have hmain : G * ((1 + uL) * (Ssq * P0) * D.Y L A) ≤ BG * ((1 + uL) * D.Y L A * U * P0) := by
    have hk : 0 ≤ (1 + uL) * D.Y L A * P0 := mul_nonneg (mul_nonneg (by linarith) hY) hP0nn
    calc G * ((1 + uL) * (Ssq * P0) * D.Y L A) = (G * Ssq) * ((1 + uL) * D.Y L A * P0) := by ring
      _ ≤ (BG * U) * ((1 + uL) * D.Y L A * P0) := mul_le_mul_of_nonneg_right hprice hk
      _ = BG * ((1 + uL) * D.Y L A * U * P0) := by ring
  calc _ ≤ |EnvelopeInputs.foldedPlus (D.FS.cut j)
        (DensityFibre.bpieceLp D L (TheoremCBlock.Structured.envIncR D L) dec j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| := le_abs_self _
    _ ≤ G * ((1 + uL) * (Ssq * P0) * D.Y L A + Cr) := hchain
    _ = G * ((1 + uL) * (Ssq * P0) * D.Y L A) + G * Cr := by ring
    _ ≤ BG * ((1 + uL) * D.Y L A * U * P0) + G * Cr := by linarith [hmain]

/-- **The per-piece inequality of `hfold` (minus fold, `envC`, right increments)**, for a piece
with `q_E ≤ N^τ` (the modulus conditions) and `D_E ≠ 1`. -/
theorem envR_foldMinus_piece_hfold {ε C1 C71 : ℝ} (hdcb : DCBlockProp ε C1 C71)
    (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    {θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (hcex : IsLeastCounterexample D.Y a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 2 ≤ L)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0) (hMod : modulus pr h ∣ M0)
    (hpar : ParityCondition D.S.ep) (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β)
    (dec : EnvelopeInputsBlock.DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hne : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b ≠ 1)
    {qE cE : ℕ}
    (hDE : ∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk paperTail L b = qE * cE)
    (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl)
    (hcopE : qE.Coprime cE) (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    {σ' : ℝ} (hσ : 0 ≤ σ') (hS1 : ε / 20 - Sarkozy.AnalyticStage.γ / 40 ≤ -σ')
    (hatom : ∀ b ∈ DensityFibre.hTermAtoms D L φ,
      ∀ hb : 0 < totalVariation (lawDensity (DensityFibre.bpieceLm D L
        (TheoremCBlock.Structured.envIncR D L) dec j b (φ b))),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) dec j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) * D.Y L A *
          (∏ b, if f b then TheoremCBlock.Structured.envPriceR D L b else 1) *
          mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).1)
              (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
              (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.1))
            (fun _ => True) a θ (density (blockScale * L) A)) +
      (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
          ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
          |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) dec j b.1
            (φ b.1)) x|) *
        (dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
            (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
            (L : ℝ) ^ (-σ') * density (blockScale * L) A) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hQ : ∀ b, IsPositiveRecord (TheoremCBlock.Structured.envIncR D L b) :=
    fun b => isPositiveRecord_envIncR D L b
  have hchain := envR_foldMinus_piece_paper hcop hdcb D hpair hcex hθ hθ2 ha hC0 hL hsc hM0 hMod
    (TheoremCBlock.Structured.envIncR D L) hQ dec j φ hne hDE hqE hcE hcE0 hcQ hcopE hqN Jq hJ ω
    hσ hS1 hatom
  -- the slot moduli of the folded data are coprime to `D_E`
  have hmpos : 0 < modulus pr h := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcopv : ∀ v, ((envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).1).Coprime
      (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) := by
    intro v
    apply Nat.Coprime.prod_right
    intro k _
    rw [envSlots_fst hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)]
    unfold envD0
    split
    · exact Nat.Coprime.coprime_dvd_left (revealedModulus_dvd _) (hcopM_of_data D L k)
    · exact Nat.coprime_one_left _
  rw [mainPrice_split _ Es _ _ L _ a θ _ hcopv] at hchain
  have hselF := hselF_of_parity D (prefix_pairwise (hpair 0)) hpar hsel L
  have hprice := piecePrice_minus_le D L (hpair L) (TheoremCBlock.Structured.envIncR D L) hQ dec j
    f σ φ hφ hselF (TheoremCBlock.Structured.envPriceR D L)
    (fun b => envIncR_price_le D L b (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hselF b))
  set G := ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk paperTail L b.1,
    |lawDensity (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) dec j b.1
      (φ b.1)) x| with hG
  set Ssq := ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a with hSsq
  set P0 := mainPrice (paperPrice (crtModuli m₀ blk paperTail L) ∅
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).1)
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1) L)
    (paperMeanDensity (FiniteLaw.uniform Unit) A
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).1)
      (fun v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.1)
      (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.2.2)
      (fun _ v => (envSlots hcop D.index.w L Jq ω ((D.FS.cut j).foldMinus v)).2.1))
    (fun _ => True) a θ (density (blockScale * L) A) with hP0
  set U := ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) with hU
  set BG := ∏ b, DensityFibre.bpieceG D L b (φ b) with hBG
  set uL := scaleU blockScale M0 Qcl stageTau L with huL
  set Cr := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ M0
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 *
    (L : ℝ) ^ (-σ') * density (blockScale * L) A with hCr
  have hY : 0 ≤ D.Y L A := le_trans (mul_nonneg (mul_nonneg hC0
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg (density_nonneg _ _) _))
    hcex.lower.le
  have hu0 : 0 ≤ uL := by
    rw [huL]
    unfold scaleU
    have h1 : (1 : ℝ) ≤ 1 + (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
        ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by
      have : 0 ≤ (blockScale : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
          ((blockScale * L : ℕ) : ℝ) ^ (2 * stageTau - 1) := by positivity
      linarith
    linarith [one_le_pow₀ (n := 72) h1]
  have hP0nn : 0 ≤ P0 := by
    rw [hP0]
    unfold mainPrice paperPrice paperMeanDensity
    refine mul_nonneg (prod_nonneg fun v _ => Real.rpow_nonneg (by positivity) _)
      (prod_nonneg fun v _ => Real.rpow_nonneg (div_nonneg ?_ (density_nonneg _ _)) _)
    unfold FiniteLaw.expect
    exact sum_nonneg fun _ _ => mul_nonneg (FiniteLaw.nonneg _ _) (by positivity)
  have hmain : G * ((1 + uL) * (Ssq * P0) * D.Y L A) ≤ BG * ((1 + uL) * D.Y L A * U * P0) := by
    have hk : 0 ≤ (1 + uL) * D.Y L A * P0 := mul_nonneg (mul_nonneg (by linarith) hY) hP0nn
    calc G * ((1 + uL) * (Ssq * P0) * D.Y L A) = (G * Ssq) * ((1 + uL) * D.Y L A * P0) := by ring
      _ ≤ (BG * U) * ((1 + uL) * D.Y L A * P0) := mul_le_mul_of_nonneg_right hprice hk
      _ = BG * ((1 + uL) * D.Y L A * U * P0) := by ring
  calc _ ≤ |EnvelopeInputs.foldedMinus (D.FS.cut j)
        (DensityFibre.bpieceLm D L (TheoremCBlock.Structured.envIncR D L) dec j)
        (fun v x => pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk paperTail L) (paperCutoff (blockScale * L)) A L) ω ω v
          ((crtLabelEquiv blk (prefix_pairwise (hpair L)) L).symm x)) φ| := le_abs_self _
    _ ≤ G * ((1 + uL) * (Ssq * P0) * D.Y L A + Cr) := hchain
    _ = G * ((1 + uL) * (Ssq * P0) * D.Y L A) + G * Cr := by ring
    _ ≤ BG * ((1 + uL) * D.Y L A * U * P0) + G * Cr := by linarith [hmain]

end Sarkozy.DensityChain2
