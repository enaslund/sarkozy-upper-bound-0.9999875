module

public import Sarkozy.SharpBase2.HtermPT
public import Sarkozy.SharpSums.Split

@[expose] public section

/-!
# The four remainders `rchPT*` split into the three error terms of `lem:sharp-first`

SUM (7 November 2026). SH2's per-choice remainders `rchPTEnvL/R`, `rchPTFixL/R`
(`SharpBase2.HtermPT`) are sums over the tags `j` of `rchPT` at DC3's per-tag data. This file
defines, for each of them and each tag, the three parts of `SharpSums.Split`:

* `crossPT*` (main × chain-remainder cross terms), `chainPT*` (chain²), `largePT*` (the large
  pieces `√𝔈₊ √𝔈₋`), generated from the definitions of `rchPT*` with `rchPT` replaced by
  `rchCross`, `rchChain`, `rchLarge` (same arguments);
* **`rchPT*_eq_parts`**: `rchPT* = ∑_j (√C cross + C chain + large)`, `C = crDC … ≥ 0`;
* `crDC`: the constant `C = C_dc L^{-σ'} α` of the chain remainders (`lem:record:density-dc`);
* `expect2_le_of_pt`: the two expectations of a pointwise split.
-/

namespace Sarkozy.SharpSums

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.SharpBase2
open Sarkozy.Param (Params)

section Generic

variable {Φ : Type} [Fintype Φ]

/-- The cross part of `rchPT`, with `rchPT`'s arguments (`crossPart` at `M_± = K₀ P_±`). -/
noncomputable def rchCross (small : Φ → Prop) (K₀ Pp Pm _Cr : ℝ) (w BG Gp Gm _Fp _Fm : Φ → ℝ) :
    ℝ :=
  crossPart small (K₀ * Pp) (K₀ * Pm) w BG Gp Gm

/-- The chain² part of `rchPT`, with `rchPT`'s arguments. -/
noncomputable def rchChain (small : Φ → Prop) (_K₀ _Pp _Pm _Cr : ℝ)
    (w _BG Gp Gm _Fp _Fm : Φ → ℝ) : ℝ :=
  chainPart small w Gp Gm

/-- The large-piece part of `rchPT`, with `rchPT`'s arguments. -/
noncomputable def rchLarge (small : Φ → Prop) (_K₀ _Pp _Pm _Cr : ℝ)
    (w _BG _Gp _Gm Fp Fm : Φ → ℝ) : ℝ :=
  largePart small w Fp Fm

/-- `rchPT = √C rchCross + C rchChain + rchLarge` (`rchPT_eq_split`). -/
theorem rchPT_eq_parts (small : Φ → Prop) (K₀ Pp Pm : ℝ) {Cr : ℝ} (hCr : 0 ≤ Cr)
    (w BG Gp Gm Fp Fm : Φ → ℝ) :
    rchPT small K₀ Pp Pm Cr w BG Gp Gm Fp Fm =
      Real.sqrt Cr * rchCross small K₀ Pp Pm Cr w BG Gp Gm Fp Fm +
        Cr * rchChain small K₀ Pp Pm Cr w BG Gp Gm Fp Fm +
          rchLarge small K₀ Pp Pm Cr w BG Gp Gm Fp Fm :=
  rchPT_eq_split small K₀ Pp Pm hCr w BG Gp Gm Fp Fm

end Generic

/-- **The two expectations of a pointwise split**: if `F ≤ X + Y + c` pointwise, then
`E_x E_y F ≤ E_x E_y X + E_x E_y Y + c`. -/
theorem expect2_le_of_pt {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂] (μ : FiniteLaw Ω₁)
    (ν : FiniteLaw Ω₂) (F X Y : Ω₁ → Ω₂ → ℝ) (c : ℝ) (h : ∀ x y, F x y ≤ X x y + Y x y + c) :
    μ.expect (fun x => ν.expect (F x)) ≤
      μ.expect (fun x => ν.expect (X x)) + μ.expect (fun x => ν.expect (Y x)) + c := by
  have h1 : ∀ x, ν.expect (F x) ≤ ν.expect (X x) + ν.expect (Y x) + c := by
    intro x
    have := ν.expect_mono (h x)
    rw [ν.expect_add (fun y => X x y + Y x y) (fun _ => c), ν.expect_add, ν.expect_const] at this
    exact this
  have := μ.expect_mono h1
  rw [μ.expect_add (fun x => ν.expect (X x) + ν.expect (Y x)) (fun _ => c), μ.expect_add,
    μ.expect_const] at this
  exact this

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The constant of the chain remainders** `C = C_dc L^{-σ'} α` (`lem:record:density-dc`), as it
appears in the four `rchPT*`. -/
noncomputable def crDC (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ) : ℝ :=
  dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ (modulus pr h)
    (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 * (L : ℝ) ^ (-σ') *
    density (blockScale * L) A

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The cross part of `rchPTEnvL` at the tag `j`**
(`lem:sharp-first`: the main × chain-remainder cross terms). -/
noncomputable def crossPTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchCross (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **The chain part of `rchPTEnvL` at the tag `j`**
(`lem:sharp-first`: the chain² terms). -/
noncomputable def chainPTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchChain (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **The large part of `rchPTEnvL` at the tag `j`**
(`lem:sharp-first`: the large-piece geometric means). -/
noncomputable def largePTEnvL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchLarge (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **`rchPTEnvL` is the sum of the three error terms** of `lem:sharp-first` over the
tags. -/
theorem rchPTEnvL_eq_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b))
    (hCr : 0 ≤ crDC D C1 C71 σ' L A) :
    rchPTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ =
      ∑ j : D.FS.Tag, (Real.sqrt (crDC D C1 C71 σ' L A) *
        crossPTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ j +
        crDC D C1 C71 σ' L A * chainPTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ j +
          largePTEnvL hcop D hpair dec C1 C71 σ' L A Jq ω f σ j) := by
  unfold rchPTEnvL crossPTEnvL chainPTEnvL largePTEnvL
  exact sum_congr rfl fun j _ => rchPT_eq_parts _ _ _ _ hCr _ _ _ _ _ _

/-- **The cross part of `rchPTEnvR` at the tag `j`**
(`lem:sharp-first`: the main × chain-remainder cross terms). -/
noncomputable def crossPTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchCross (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **The chain part of `rchPTEnvR` at the tag `j`**
(`lem:sharp-first`: the chain² terms). -/
noncomputable def chainPTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchChain (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **The large part of `rchPTEnvR` at the tag `j`**
(`lem:sharp-first`: the large-piece geometric means). -/
noncomputable def largePTEnvR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchLarge (fun φ => (∀ e, (Jq e none : ℕ) ≠ 0) ∧ smallPiece m₀ blk D L φ)
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

/-- **`rchPTEnvR` is the sum of the three error terms** of `lem:sharp-first` over the
tags. -/
theorem rchPTEnvR_eq_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b))
    (hCr : 0 ≤ crDC D C1 C71 σ' L A) :
    rchPTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ =
      ∑ j : D.FS.Tag, (Real.sqrt (crDC D C1 C71 σ' L A) *
        crossPTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ j +
        crDC D C1 C71 σ' L A * chainPTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ j +
          largePTEnvR hcop D hpair dec C1 C71 σ' L A Jq ω f σ j) := by
  unfold rchPTEnvR crossPTEnvR chainPTEnvR largePTEnvR
  exact sum_congr rfl fun j _ => rchPT_eq_parts _ _ _ _ hCr _ _ _ _ _ _

/-- **The cross part of `rchPTFixL` at the tag `j`**
(`lem:sharp-first`: the main × chain-remainder cross terms). -/
noncomputable def crossPTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchCross (smallPiece m₀ blk D L)
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

/-- **The chain part of `rchPTFixL` at the tag `j`**
(`lem:sharp-first`: the chain² terms). -/
noncomputable def chainPTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchChain (smallPiece m₀ blk D L)
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

/-- **The large part of `rchPTFixL` at the tag `j`**
(`lem:sharp-first`: the large-piece geometric means). -/
noncomputable def largePTFixL (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchLarge (smallPiece m₀ blk D L)
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

/-- **`rchPTFixL` is the sum of the three error terms** of `lem:sharp-first` over the
tags. -/
theorem rchPTFixL_eq_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b))
    (hCr : 0 ≤ crDC D C1 C71 σ' L A) :
    rchPTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ =
      ∑ j : D.FS.Tag, (Real.sqrt (crDC D C1 C71 σ' L A) *
        crossPTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j +
        crDC D C1 C71 σ' L A * chainPTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j +
          largePTFixL hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j) := by
  unfold rchPTFixL crossPTFixL chainPTFixL largePTFixL
  exact sum_congr rfl fun j _ => rchPT_eq_parts _ _ _ _ hCr _ _ _ _ _ _

/-- **The cross part of `rchPTFixR` at the tag `j`**
(`lem:sharp-first`: the main × chain-remainder cross terms). -/
noncomputable def crossPTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchCross (smallPiece m₀ blk D L)
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

/-- **The chain part of `rchPTFixR` at the tag `j`**
(`lem:sharp-first`: the chain² terms). -/
noncomputable def chainPTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchChain (smallPiece m₀ blk D L)
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

/-- **The large part of `rchPTFixR` at the tag `j`**
(`lem:sharp-first`: the large-piece geometric means). -/
noncomputable def largePTFixR (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) : ℝ :=
  rchLarge (smallPiece m₀ blk D L)
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

/-- **`rchPTFixR` is the sum of the three error terms** of `lem:sharp-first` over the
tags. -/
theorem rchPTFixR_eq_parts (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (dec : ∀ L, EnvelopeInputsBlock.DecFamily D L) (C1 C71 σ' : ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (f : BlockAtom Bk PaperJt L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b))
    (hCr : 0 ≤ crDC D C1 C71 σ' L A) :
    rchPTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ =
      ∑ j : D.FS.Tag, (Real.sqrt (crDC D C1 C71 σ' L A) *
        crossPTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j +
        crDC D C1 C71 σ' L A * chainPTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j +
          largePTFixR hcop D hpair dec C1 C71 σ' L A S Jq ω f σ j) := by
  unfold rchPTFixR crossPTFixR chainPTFixR largePTFixR
  exact sum_congr rfl fun j _ => rchPT_eq_parts _ _ _ _ hCr _ _ _ _ _ _

end Sarkozy.SharpSums
