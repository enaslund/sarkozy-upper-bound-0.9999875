module

public import Sarkozy.EnvelopeInputsParam.EnvelopeCoupledNonneg
public import Sarkozy.EnvelopeInputsParam.RevealExpansion

@[expose] public section






open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
  ReflectionCut

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-! ## The sharp first-stage terms -/

/-- **The per-term inputs of `SharpFirstTerms`** (`lem:sharp-first`, `lem:record:first-stage`
Step 2, in the form of `lem:density:coupled`): the hypotheses of
`sharpFirstTerms_of_coupledPieces_uniform`. At every least counterexample, for every nonempty
choice `σ` of differences, every tag `j` present in `σ` and every choice `f` of coupled pieces
with nonzero coefficients (the sharp differences of tag `j` kept whole, the other atoms expanded
into `μ` and positive spectators),
`|Y[⊗_𝔟 K_𝔟(f_𝔟)]| ≤ (∏_𝔟 g_𝔟(f_𝔟)) (1 + ε_L) Y + (∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α`. -/
structure SharpFirstInputs (D : TheoremCParam.ComparisonData a m₀ p pr h E) where
  /-- The relative error `ε_L → 0`. -/
  ε : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ ε L
  hεt : Tendsto ε atTop (𝓝 0)
  /-- The constant of the density-linear remainders. -/
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  /-- The coupled per-term bounds (`lem:density:coupled` for one term). -/
  hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CPiece D L b),
      (∀ b, cpieceCoef D L σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => cpieceK D L b (f b)) (atomLift m₀ p L A)| ≤
        (∏ b, cpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) +
          (∏ b, cpieceM D L b (f b)) * remainder c₁ L A)

omit [DecidableEq P] in
/-- **`SharpFirstTerms` from its per-term inputs** (`lem:sharp-first`, `lem:density:coupled`),
at every exponent `a ≥ 0`: `sharpFirstTerms_of_coupledPieces_uniform`. -/
theorem SharpFirstInputs.sharpFirstTerms {D : TheoremCParam.ComparisonData a m₀ p pr h E}
    (I : SharpFirstInputs D) (ha : 0 ≤ a) : D.SharpFirstTerms :=
  sharpFirstTerms_of_coupledPieces_uniform D ha I.ε I.hε0 I.hεt I.hc₁ I.hcoup

/-! ## The envelope bound (E1) -/

/-- **The per-term inputs of `EnvelopeBoundNonneg`** (`lem:bracket-energy` for the selection
envelopes, with `lem:sharp-first` and `lem:density:coupled`; `def:robust`): the hypotheses of
`envelopeBoundNonneg_of_coupledPieces_uniform`. At every least counterexample and every selection
`ω`:
* `hsub`, the subset terms (input 1 of WP-R's `envelopeBound_of_terms`), with the remainders
  `∏_f mass(∑κu) c₁ L^{-σ} α` of `prop:record:density-structured`;
* `hcoup`, the coupled per-term bounds of the sharp-first terms under the selected envelopes (the
  sharp differences of the tag kept whole, the selected envelopes kept whole as packets), with
  the remainders `(∏_𝔟 m_𝔟(f_𝔟)) c₁ L^{-σ} α`. -/
structure EnvelopeBoundInputs (D : TheoremCParam.ComparisonData a m₀ p pr h E) where
  /-- The relative error `ε_L → 0`. -/
  εE : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ εE L
  hεt : Tendsto εE atTop (𝓝 0)
  /-- The constant of the density-linear remainders. -/
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  /-- The subset terms. -/
  hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∀ ω : Choice (D.CL.T L), IsSelection ω → ∀ f : PaperAtom J L → Bool,
      |diagonalIntegral (tensorLaw fun b => if f b then
          (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
        else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (atomLift m₀ p L A)| ≤
        ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCParam.selectionFactor a p D.S.selPre L b) *
          D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
        (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
          remainder c₁ L A)
  /-- The coupled per-term bounds under the selected envelopes. -/
  hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∀ ω : Choice (D.CL.T L), IsSelection ω →
      ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
      1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
      (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
      |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (atomLift m₀ p L A)| ≤
        (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) +
          (∏ b, ecpieceM D L b (f b)) * remainder c₁ L A)

omit [DecidableEq P] in
/-- **`EnvelopeBoundNonneg` from its per-term inputs** (`lem:bracket-energy`,
`lem:density:coupled`, `def:robust`), at every exponent `a ≥ 0`:
`envelopeBoundNonneg_of_coupledPieces_uniform`. -/
theorem EnvelopeBoundInputs.envelopeBoundNonneg {D : TheoremCParam.ComparisonData a m₀ p pr h E}
    (I : EnvelopeBoundInputs D) (ha : 0 ≤ a) : D.EnvelopeBoundNonneg :=
  envelopeBoundNonneg_of_coupledPieces_uniform D ha I.εE I.hε0 I.hεt I.hc₁ I.hsub I.hcoup

omit [DecidableEq P] in
/-- **`EnvelopeBound` from the same inputs** (the plain form of (E1), for
`TheoremCParam.ComparisonData.theoremC_reduced`): I1's `envelopeBound_of_coupledPieces_uniform`
at a free exponent. -/
theorem EnvelopeBoundInputs.envelopeBound {D : TheoremCParam.ComparisonData a m₀ p pr h E}
    (I : EnvelopeBoundInputs D) (ha : 0 ≤ a) : D.EnvelopeBound :=
  envelopeBound_of_coupledPieces_uniform D ha I.εE I.hε0 I.hεt I.hc₁ I.hsub I.hcoup

/-! ## The envelope energies -/

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The per-term inputs of `EnvelopeEnergies`** (`lem:envelope-energy` with `𝒮 = ℰ_k`,
`lem:hyb:moment`): the hypotheses of `envelopeEnergies_of_inputs` other than `ha` and
`IndexMomentBound`. For every depth vector `𝒥`, interval vector `ω` and subset `f` of atoms, the
energy of the revealed half-functions, written as the multilinear integral with the slot inputs
`pairInputs` (the revealed input of each query at its two endpoints, `F_A` elsewhere), is at most
`(B + z_L) Π_{𝒥} Y ∏_{𝔟 ∈ f} u_𝔟 + r_{𝒥,ω,f}`, with the conductor price
`Π_𝒥 = ∏_e (K sq(D_{𝒥_e}))^{2a/d}`; the remainders `r` average to a density-linear remainder. -/
structure EnvelopeEnergyInputs (D : TheoremCParam.ComparisonData a m₀ p pr h E) where
  /-- The relative error `z_L → 0`. -/
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  /-- The constant of the density-linear remainders. -/
  c : ℝ
  hc : 0 ≤ c
  /-- The remainders of the left and right per-term bounds. -/
  rL : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ
  rR : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ
  /-- The per-term bounds for the source half-functions. -/
  htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral (tensorLaw
          fun b => if f b then TheoremCParam.Structured.envIncL D L b else D.GB.N L b)
          (pairInputs D.index.u D.index.u (revealedInput hcop D L A Jq)
            (revealedInput hcop D L A Jq) (atomLift m₀ p L A) ω ω)| ≤
        (D.B + z L) * conductorPrice pr h (priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.envPriceL D L b else 1) + rL L A Jq ω f)
  /-- The per-term bounds for the target half-functions. -/
  htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral (tensorLaw
          fun b => if f b then TheoremCParam.Structured.envIncR D L b else D.GB.N L b)
          (pairInputs D.index.w D.index.w (revealedInput hcop D L A Jq)
            (revealedInput hcop D L A Jq) (atomLift m₀ p L A) ω ω)| ≤
        (D.B + z L) * conductorPrice pr h (priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.envPriceR D L b else 1) + rR L A Jq ω f)
  /-- The remainder summation, left. -/
  hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A Jq ω f)) ≤ remainder c L A)
  /-- The remainder summation, right. -/
  hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A Jq ω f)) ≤ remainder c L A)

/-- **`EnvelopeEnergies` from its per-term inputs** (`lem:envelope-energy`, `lem:hyb:moment`), at
every exponent `a ≥ 0`, given I1's `IndexMomentBound`: `envelopeEnergies_of_inputs`. -/
theorem EnvelopeEnergyInputs.envelopeEnergies {D : TheoremCParam.ComparisonData a m₀ p pr h E}
    (I : EnvelopeEnergyInputs hcop D) (ha : 0 ≤ a) (hRI : IndexMomentBound D) :
    D.EnvelopeEnergies hcop :=
  envelopeEnergies_of_inputs hcop D ha hRI I.z I.hz0 I.hzt I.hc I.rL I.rR I.htermL I.htermR
    I.hremL I.hremR

/-- **The per-term inputs of `FixedIntervalEnvelopeEnergies`** (`lem:envelope-energy` at fixed
intervals, `lem:hyb:moment`): the hypotheses of `fixedIntervalEnvelopeEnergies_of_inputs` other
than `ha` and `IndexMomentBound`. For every nonempty set `𝒮` of active queries, depth vector `𝒥`,
interval vector `ω` and subset `f` of atoms, the energy of the revealed fixed-interval
half-functions is at most `(B + z_L) Π_𝒮 Y ∏_{𝔟 ∈ f} w_𝔟 + r`, with the price
`Π_𝒮 = ∏_{e ∈ 𝒮} K^{2θ/d} (K sq(D_{𝒥_e}))^{2a/d}`; the remainders average to a density-linear
remainder. -/
structure FixedIntervalInputs (D : TheoremCParam.ComparisonData a m₀ p pr h E) where
  /-- The relative error `z_L → 0`. -/
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  /-- The constant of the density-linear remainders. -/
  c : ℝ
  hc : 0 ≤ c
  /-- The remainders of the left and right per-term bounds. -/
  rL : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ
  rR : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ
  /-- The per-term bounds for the source half-functions. -/
  htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral (tensorLaw
          fun b => if f b then TheoremCParam.Structured.wrapInc D L b else D.GB.N L b)
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapSourceInput m₀ p pr h hcop L A S))
            (revealedSlot Jq (wrapSourceInput m₀ p pr h hcop L A S)) (atomLift m₀ p L A)
            ω ω)| ≤
        (D.B + z L) * fixedPrice pr h (priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.wrapPrice D L b else 1) + rL L A S Jq ω f)
  /-- The per-term bounds for the target half-functions. -/
  htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral (tensorLaw
          fun b => if f b then TheoremCParam.Structured.wrapInc D L b else D.GB.N L b)
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapTargetInput m₀ p pr h hcop L A S))
            (revealedSlot Jq (wrapTargetInput m₀ p pr h hcop L A S)) (atomLift m₀ p L A)
            ω ω)| ≤
        (D.B + z L) * fixedPrice pr h (priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.wrapPrice D L b else 1) + rR L A S Jq ω f)
  /-- The remainder summation, left. -/
  hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A S Jq ω f)) ≤ remainder c L A)
  /-- The remainder summation, right. -/
  hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A S Jq ω f)) ≤ remainder c L A)

/-- **`FixedIntervalEnvelopeEnergies` from its per-term inputs** (`lem:envelope-energy` at fixed
intervals, `lem:hyb:moment`), at every exponent `a ≥ 0`, given I1's `IndexMomentBound`:
`fixedIntervalEnvelopeEnergies_of_inputs`. -/
theorem FixedIntervalInputs.fixedIntervalEnvelopeEnergies
    {D : TheoremCParam.ComparisonData a m₀ p pr h E} (I : FixedIntervalInputs hcop D)
    (ha : 0 ≤ a) (hRI : IndexMomentBound D) : D.FixedIntervalEnvelopeEnergies hcop :=
  fixedIntervalEnvelopeEnergies_of_inputs hcop D ha hRI I.z I.hz0 I.hzt I.hc I.rL I.rR I.htermL
    I.htermR I.hremL I.hremR

end Sarkozy.EnvelopeInputsParam
