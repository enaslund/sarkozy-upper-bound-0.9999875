module

public import Sarkozy.EnvelopeEnergiesPaper.CRTInputs

@[expose] public section

/-!
# G1's bundles `env` and `fix` on the cyclic coordinates

`EnvelopeEnergyInputsCRT` and `FixedIntervalInputsCRT` are G1's `EnvelopeEnergyInputs` and
`FixedIntervalInputs` (`lem:envelope-energy`, `lem:hyb:moment`) with every per-term energy stated on
the cyclic coordinates `G_N ≅ ∏_𝔟 ℤ/crtModuli_𝔟` of `BlockCRT`: the laws are `crtLaws` of the
block-atom laws, the inputs are the cyclic inputs `revealedInputCRT`, `wrapInputCRT` and
`unchangedInput crtModuli`. The scalars, remainders and remainder summations are G1's, unchanged.
`toG1` gives G1's bundle (`env_term_crt`, `fix_term_crt_source`, `fix_term_crt_target`). The only
extra input is the pairwise coprimality of the joined moduli at every scale, which holds for the
paper's data (`CancellationSteps.paper_hcopE`).

**Non-vacuity.** Each bundle is equivalent to G1's (the energies are equal term by term), so it is
satisfiable exactly when G1's is.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.EnvelopeInputs
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

/-- **G1's `EnvelopeEnergyInputs` on the cyclic coordinates** (`lem:envelope-energy` with
`𝒮 = ℰ_k`, `lem:hyb:moment`). -/
structure EnvelopeEnergyInputsCRT (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  c : ℝ
  hc : 0 ≤ c
  rL : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  rR : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  /-- The per-term bounds for the source half-functions, on the cyclic coordinates. -/
  htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
          fun b => if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
          (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.B + z L) * conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) + rL L A Jq ω f)
  /-- The per-term bounds for the target half-functions, on the cyclic coordinates. -/
  htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
          fun b => if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
          (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
            (revealedInputCRT blk hcop D L A Jq)
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.B + z L) * conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) + rR L A Jq ω f)
  hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A Jq ω f)) ≤ remainder c L A)
  hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A Jq ω f)) ≤ remainder c L A)

/-- **To G1's bundle**: the energies agree term by term (`env_term_crt`). -/
noncomputable def EnvelopeEnergyInputsCRT.toG1 {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)}
    (I : EnvelopeEnergyInputsCRT hcop D hpair) :
    EnvelopeInputsBlock.EnvelopeEnergyInputs hcop D where
  z := I.z
  hz0 := I.hz0
  hzt := I.hzt
  c := I.c
  hc := I.hc
  rL := I.rL
  rR := I.rR
  htermL := by
    filter_upwards [I.htermL] with L hL
    intro C hC hk A hA hY Jq ω f
    rw [env_term_crt blk hcop D L (hpair L)]
    exact hL C hC hk A hA hY Jq ω f
  htermR := by
    filter_upwards [I.htermR] with L hL
    intro C hC hk A hA hY Jq ω f
    rw [env_term_crt blk hcop D L (hpair L)]
    exact hL C hC hk A hA hY Jq ω f
  hremL := I.hremL
  hremR := I.hremR

/-- **G1's `FixedIntervalInputs` on the cyclic coordinates** (`lem:envelope-energy` at fixed
intervals, `lem:hyb:moment`). -/
structure FixedIntervalInputsCRT (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  c : ℝ
  hc : 0 ≤ c
  rL : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  rR : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  /-- The per-term bounds for the source half-functions, on the cyclic coordinates. -/
  htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
          fun b => if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.B + z L) * fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) + rL L A S Jq ω f)
  /-- The per-term bounds for the target half-functions, on the cyclic coordinates. -/
  htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L
          fun b => if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
            (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
        (D.B + z L) * fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) + rR L A S Jq ω f)
  hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A S Jq ω f)) ≤ remainder c L A)
  hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
      (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A S Jq ω f)) ≤ remainder c L A)

/-- **To G1's bundle**: the energies agree term by term (`fix_term_crt_source`,
`fix_term_crt_target`). -/
noncomputable def FixedIntervalInputsCRT.toG1 {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)}
    (I : FixedIntervalInputsCRT hcop D hpair) : EnvelopeInputsBlock.FixedIntervalInputs hcop D where
  z := I.z
  hz0 := I.hz0
  hzt := I.hzt
  c := I.c
  hc := I.hc
  rL := I.rL
  rR := I.rR
  htermL := by
    filter_upwards [I.htermL] with L hL
    intro C hC hk A hA hY S hS Jq ω f
    rw [fix_term_crt_source blk hcop L (hpair L)]
    exact hL C hC hk A hA hY S hS Jq ω f
  htermR := by
    filter_upwards [I.htermR] with L hL
    intro C hC hk A hA hY S hS Jq ω f
    rw [fix_term_crt_target blk hcop L (hpair L)]
    exact hL C hC hk A hA hY S hS Jq ω f
  hremL := I.hremL
  hremR := I.hremR

end Sarkozy.EnvelopeEnergiesPaper
