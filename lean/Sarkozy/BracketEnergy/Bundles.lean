module

public import Sarkozy.BracketEnergy.Bracket

@[expose] public section

/-!
# `envC` and `fixC` from `lem:bracket-energy`: the bracket removed from the per-term inputs

B5's bundles `EnvelopeEnergyInputsCRT` (`envC`) and `FixedIntervalInputsCRT` (`fixC`)
(`lem:envelope-energy`, `lem:hyb:moment`) ask, per depth vector `𝒥`, index `ω` and set `f` of
atoms, a bound `|E_{⊗(f ? Q : Ñ)}| ≤ (B + z) Π_𝒥 Y ∏_{f} u + r` on a revealed-input energy whose
outside law is the bracket `Ñ` of (CP3). The paper's proof of `lem:envelope-energy` bounds each such
energy by "the small-union part of the proof of `lem:bracket-energy`". This file does that proof
(`bracket_term_le`) term by term, so the two bundles are built from inputs **whose outside law is
`μ`**, plus the sharp-first difference:

* `EnvelopeBracketInputs` (for `envC`) and `FixedBracketInputs` (for `fixC`). Per side (source
  `L`, target `R`):
  - `hfirst`: for every `g ⊥ f`, the energy of `⊗_{f} Q ⊗ ⊗_{g} (Ñ₀ − μ) ⊗ μ_{−f−g}` with the
    same revealed inputs is at most `(1 + z) Π_𝒥 Y ∏_{f} u ∏_{g} u' + r₁`
    (`lem:bracket-energy`, first bound, i.e. `prop:record:density-structured` with the structured
    slot data of the query endpoints, for the positive selected measure
    `⊗_{f} Q ⊗ ⊗_{g} (Ñ₀ − μ)`, `u'_𝔟 = GB.uprice` the price of the reserved records);
  - `hdiff`: `|E_{f ? Q : Ñ} − E_{f ? Q : Ñ₀}| ≤ (R_err + z) Π_𝒥 Y ∏_{f} u + r₂`
    (`lem:sharp-first` with `ρ = Ñ₀` on the first-stage atoms outside `f`, and the same inputs);
  - `hrem`: the remainders, summed over `f` and `g ⊥ f`, average to at most `c L^{-σ} α`.
* **`EnvelopeBracketInputs.toCRT`**, **`FixedBracketInputs.toCRT`**: B5's bundles, with
  `z' = e^{U₀} z + z` and `r = ∑_{g ⊥ f} r₁ + r₂`. The factor is `B = e^{U₀} + R_err` exactly.
* `EnvelopeEnergyInputsCRT.ofExcess`, `FixedIntervalInputsCRT.ofExcess`: the remainders of B5's
  bundles are signed, so each bundle is equivalent to one averaged inequality (the average over
  `𝒥, ω` of `∑_f (|E_f| − (B + z) Π Y ∏ u)` is at most `c L^{-σ} α`); the same holds for the new
  bundles. See the report for why this matters: the paper bounds the energy at fixed `𝒥` after
  the average over the residues, not at every `ω`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- At a counterexample `Y > 0`. -/
theorem Y_nonneg_of_cex (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {L : ℕ}
    {A : Finset ℤ} {C : ℝ} (hC : 1 ≤ C)
    (hY : C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
      density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent <
        D.Y L A) : 0 ≤ D.Y L A := by
  refine le_of_lt (lt_of_le_of_lt ?_ hY)
  exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg (density_nonneg _ _) _)

omit [DecidableEq P] in
/-- `e^{U₀} z + z → 0`. -/
theorem tendsto_bracket_z (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) {z : ℕ → ℝ}
    (hzt : Tendsto z atTop (𝓝 0)) :
    Tendsto (fun L => Real.exp D.GB.U₀ * z L + z L) atTop (𝓝 0) := by
  simpa using (hzt.const_mul (Real.exp D.GB.U₀)).add hzt

/-! ## `envC` -/

/-- **The per-term inputs of `envC` with the bracket removed** (`lem:envelope-energy` with
`𝒮 = ℰ_k`, through the proof of `lem:bracket-energy`). For each side: the first bound of
`lem:bracket-energy` for the terms with outside law `μ` (`hfirst`), the sharp-first difference
`Ñ − Ñ₀` (`hdiff`), and the remainder summation (`hrem`). All energies are on the cyclic
coordinates with the revealed inputs of B5's `EnvelopeEnergyInputsCRT`. -/
structure EnvelopeBracketInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  c : ℝ
  hc : 0 ≤ c
  r1L : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
      (BlockAtom Bk J L → Bool) → ℝ
  r1R : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
      (BlockAtom Bk J L → Bool) → ℝ
  r2L : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  r2R : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  /-- `lem:bracket-energy`, first bound, outside law `μ`, source inputs. -/
  hfirstL : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f g : BlockAtom Bk J L → Bool), g ∈ validChoices f →
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.envIncL D L b else
            if g b then recLaw D L b else muLaw D L b))
          (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (1 + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) *
          ∏ b, (if g b then D.GB.uprice L b else 1) + r1L L A Jq ω f g)
  /-- `lem:bracket-energy`, first bound, outside law `μ`, target inputs. -/
  hfirstR : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f g : BlockAtom Bk J L → Bool), g ∈ validChoices f →
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.envIncR D L b else
            if g b then recLaw D L b else muLaw D L b))
          (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (1 + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) *
          ∏ b, (if g b then D.GB.uprice L b else 1) + r1R L A Jq ω f g)
  /-- `lem:sharp-first` for `Ñ − Ñ₀`, source inputs. -/
  hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
          (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
        multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N₀ L b))
          (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
          D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) +
          r2L L A Jq ω f)
  /-- `lem:sharp-first` for `Ñ − Ñ₀`, target inputs. -/
  hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
          (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
        multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N₀ L b))
          (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
          D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) +
          r2R L A Jq ω f)
  hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, (∑ g ∈ validChoices f, r1L L A Jq ω f g + r2L L A Jq ω f))) ≤
      remainder c L A)
  hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, (∑ g ∈ validChoices f, r1R L A Jq ω f g + r2R L A Jq ω f))) ≤
      remainder c L A)

/-- The main term `Π_𝒥 Y ∏_{f} u` is nonnegative. -/
theorem envMain_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (hY : 0 ≤ D.Y L A)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (f : BlockAtom Bk J L → Bool) (u : BlockAtom Bk J L → ℝ) (hu : ∀ b, 0 ≤ u b) :
    0 ≤ conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
      ∏ b, (if f b then u b else 1) :=
  mul_nonneg (mul_nonneg (conductorPrice_nonneg pr h _ Jq) hY)
    (prod_nonneg fun b _ => by split_ifs; exacts [hu b, zero_le_one])

/-- **`envC` from `lem:bracket-energy`** (`lem:envelope-energy`, proof): B5's
`EnvelopeEnergyInputsCRT`, with `z' = e^{U₀} z + z` and `r = ∑_{g ⊥ f} r₁ + r₂`. -/
noncomputable def EnvelopeBracketInputs.toCRT {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)}
    (I : EnvelopeBracketInputs hcop D hpair) : EnvelopeEnergyInputsCRT hcop D hpair where
  z := fun L => Real.exp D.GB.U₀ * I.z L + I.z L
  hz0 := fun L => add_nonneg (mul_nonneg (Real.exp_pos _).le (I.hz0 L)) (I.hz0 L)
  hzt := tendsto_bracket_z D I.hzt
  c := I.c
  hc := I.hc
  rL := fun L A Jq ω f => ∑ g ∈ validChoices f, I.r1L L A Jq ω f g + I.r2L L A Jq ω f
  rR := fun L A Jq ω f => ∑ g ∈ validChoices f, I.r1R L A Jq ω f g + I.r2R L A Jq ω f
  htermL := by
    filter_upwards [I.hfirstL, I.hdiffL] with L h1 h2
    intro C hC hk A hA hY Jq ω f
    have hK := envMain_nonneg D L A (Y_nonneg_of_cex D hC hY) Jq f _
      (TheoremCBlock.Structured.envPriceL_nonneg D L)
    have h := bracket_term_le blk D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.envIncL D L) f _ hK (I.hz0 L) (I.r1L L A Jq ω f)
      (h1 C hC hk A hA hY Jq ω f) (h2 C hC hk A hA hY Jq ω f)
    calc _ ≤ _ := h
      _ = _ := by ring
  htermR := by
    filter_upwards [I.hfirstR, I.hdiffR] with L h1 h2
    intro C hC hk A hA hY Jq ω f
    have hK := envMain_nonneg D L A (Y_nonneg_of_cex D hC hY) Jq f _
      (TheoremCBlock.Structured.envPriceR_nonneg D L)
    have h := bracket_term_le blk D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.envIncR D L) f _ hK (I.hz0 L) (I.r1R L A Jq ω f)
      (h1 C hC hk A hA hY Jq ω f) (h2 C hC hk A hA hY Jq ω f)
    calc _ ≤ _ := h
      _ = _ := by ring
  hremL := I.hremL
  hremR := I.hremR

/-! ## `fixC` -/

/-- **The per-term inputs of `fixC` with the bracket removed** (`lem:envelope-energy` at fixed
intervals, through the proof of `lem:bracket-energy`), as `EnvelopeBracketInputs` for B5's
`FixedIntervalInputsCRT`: increments `wrapInc`, prices `wrapPrice`, the fixed-interval price
`Π_𝒮`, and the wrapped revealed inputs, for every nonempty `𝒮`. -/
structure FixedBracketInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  c : ℝ
  hc : 0 ≤ c
  r1L : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
      (BlockAtom Bk J L → Bool) → ℝ
  r1R : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) →
      (BlockAtom Bk J L → Bool) → ℝ
  r2L : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  r2R : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  /-- `lem:bracket-energy`, first bound, outside law `μ`, source inputs. -/
  hfirstL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f g : BlockAtom Bk J L → Bool), g ∈ validChoices f →
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else
            if g b then recLaw D L b else muLaw D L b))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (1 + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
          ∏ b, (if g b then D.GB.uprice L b else 1) + r1L L A S Jq ω f g)
  /-- `lem:bracket-energy`, first bound, outside law `μ`, target inputs. -/
  hfirstR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f g : BlockAtom Bk J L → Bool), g ∈ validChoices f →
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else
            if g b then recLaw D L b else muLaw D L b))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (1 + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) *
          ∏ b, (if g b then D.GB.uprice L b else 1) + r1R L A S Jq ω f g)
  /-- `lem:sharp-first` for `Ñ − Ñ₀`, source inputs. -/
  hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
        multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
          D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
          r2L L A S Jq ω f)
  /-- `lem:sharp-first` for `Ñ − Ñ₀`, target inputs. -/
  hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
        multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
          if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
          D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
          r2R L A S Jq ω f)
  hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, (∑ g ∈ validChoices f, r1L L A S Jq ω f g + r2L L A S Jq ω f))) ≤
      remainder c L A)
  hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, (∑ g ∈ validChoices f, r1R L A S Jq ω f g + r2R L A S Jq ω f))) ≤
      remainder c L A)

omit [DecidableEq P] in
/-- The fixed-interval main term `Π_𝒮 Y ∏_{f} u` is nonnegative. -/
theorem fixMain_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (hY : 0 ≤ D.Y L A) (S : Finset E)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (f : BlockAtom Bk J L → Bool) (u : BlockAtom Bk J L → ℝ) (hu : ∀ b, 0 ≤ u b) :
    0 ≤ fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
      ∏ b, (if f b then u b else 1) :=
  mul_nonneg (mul_nonneg (fixedPrice_nonneg pr h _ S Jq) hY)
    (prod_nonneg fun b _ => by split_ifs; exacts [hu b, zero_le_one])

/-- **`fixC` from `lem:bracket-energy`** (`lem:envelope-energy` at fixed intervals, proof): B5's
`FixedIntervalInputsCRT`, with `z' = e^{U₀} z + z` and `r = ∑_{g ⊥ f} r₁ + r₂`. -/
noncomputable def FixedBracketInputs.toCRT {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)}
    (I : FixedBracketInputs hcop D hpair) : FixedIntervalInputsCRT hcop D hpair where
  z := fun L => Real.exp D.GB.U₀ * I.z L + I.z L
  hz0 := fun L => add_nonneg (mul_nonneg (Real.exp_pos _).le (I.hz0 L)) (I.hz0 L)
  hzt := tendsto_bracket_z D I.hzt
  c := I.c
  hc := I.hc
  rL := fun L A S Jq ω f => ∑ g ∈ validChoices f, I.r1L L A S Jq ω f g + I.r2L L A S Jq ω f
  rR := fun L A S Jq ω f => ∑ g ∈ validChoices f, I.r1R L A S Jq ω f g + I.r2R L A S Jq ω f
  htermL := by
    filter_upwards [I.hfirstL, I.hdiffL] with L h1 h2
    intro C hC hk A hA hY S hS Jq ω f
    have hK := fixMain_nonneg D L A (Y_nonneg_of_cex D hC hY) S Jq f _
      (TheoremCBlock.Structured.wrapPrice_nonneg D L)
    have h := bracket_term_le blk D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.wrapInc D L) f _ hK (I.hz0 L) (I.r1L L A S Jq ω f)
      (h1 C hC hk A hA hY S hS Jq ω f) (h2 C hC hk A hA hY S hS Jq ω f)
    calc _ ≤ _ := h
      _ = _ := by ring
  htermR := by
    filter_upwards [I.hfirstR, I.hdiffR] with L h1 h2
    intro C hC hk A hA hY S hS Jq ω f
    have hK := fixMain_nonneg D L A (Y_nonneg_of_cex D hC hY) S Jq f _
      (TheoremCBlock.Structured.wrapPrice_nonneg D L)
    have h := bracket_term_le blk D L (prefix_pairwise (hpair L))
      (TheoremCBlock.Structured.wrapInc D L) f _ hK (I.hz0 L) (I.r1R L A S Jq ω f)
      (h1 C hC hk A hA hY S hS Jq ω f) (h2 C hC hk A hA hY S hS Jq ω f)
    calc _ ≤ _ := h
      _ = _ := by ring
  hremL := I.hremL
  hremR := I.hremR

end Sarkozy.BracketEnergy
