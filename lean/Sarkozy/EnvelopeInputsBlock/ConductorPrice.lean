module

public import Sarkozy.EnvelopeInputs.ConductorPrice
public import Sarkozy.TheoremCBlock.StructuredEnvelopeEnergyGlue

@[expose] public section




open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputsBlock

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison

section TheoremC

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (a) in
/-- The price exponent `w = 2a/d` of the conductor price (`a` the free exponent, `d = 72`). -/
noncomputable def priceExponent : ℝ := 2 * a / 72

theorem priceExponent_nonneg (ha : 0 ≤ a) : 0 ≤ priceExponent a := by
  unfold priceExponent
  exact div_nonneg (mul_nonneg zero_le_two ha) (by norm_num)

/-- **The meaning of `R_I`** (`def:hyb:coupled`(g)): the conductor moment
`E_J (K sq(D_J))^{2a/d}` of every query of WP-FI's index law is at most `D.S.index.R_I`. By
`expect_queryPrice` the moment of the query `e` is `K^w ∏_q momentFactor (pr q) (h q) δ_{e,q} w`
(`lem:hyb:moment`). `IndexLaw.R_I` is otherwise unconstrained, so this is the one hypothesis
that ties it to the tails. -/
def IndexMomentBound (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) : Prop :=
  ∀ e, (blockScale : ℝ) ^ (priceExponent a) *
    ∏ q, momentFactor (pr q) (h q) (D.S.index.t e q).tail (priceExponent a) ≤ D.S.index.R_I

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **`EnvelopeEnergies` with the conductor price** (`lem:envelope-energy`, `lem:hyb:moment`):
WP-R's `Structured.envelopeEnergies_of_terms` with `Π_{𝒥,ω} = ∏_e (K sq(D_{𝒥_e}))^{2a/d}`, the
moment hypothesis `hmom` discharged by `lem:hyb:moment` (`expect_conductorPrice_le`) from
`IndexMomentBound`. Remaining inputs: the per-term bounds `htermL`, `htermR` with this price,
and the remainder summations `hremL`, `hremR`. -/
theorem envelopeEnergies_of_conductor (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (hRI : IndexMomentBound D)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rL rR : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |reservedCut.form
          (tensorLaw fun b => if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b)
          (TheoremCBlock.Structured.revealL hcop D L A Jq ω)
              (TheoremCBlock.Structured.revealL hcop D L A Jq ω)| ≤
        (D.B + z L) * conductorPrice pr h (priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1) + rL L A Jq ω f))
    (htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |reservedCut.form
          (tensorLaw fun b => if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b)
          (TheoremCBlock.Structured.revealR hcop D L A Jq ω)
              (TheoremCBlock.Structured.revealR hcop D L A Jq ω)| ≤
        (D.B + z L) * conductorPrice pr h (priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1) + rR L A Jq ω f))
    (hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A Jq ω f)) ≤ remainder c L A))
    (hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A Jq ω f)) ≤ remainder c L A)) :
    D.EnvelopeEnergies hcop := by
  refine TheoremCBlock.Structured.envelopeEnergies_of_terms hcop D z hz0 hzt hc
    (fun _ Jq _ => conductorPrice pr h (priceExponent a) Jq)
    (fun _ Jq _ => conductorPrice_nonneg pr h (priceExponent a) Jq)
        (fun L => ?_) rL rR htermL htermR
    hremL hremR
  simp only [FiniteLaw.expect_const]
  exact expect_conductorPrice_le pr h D.S.pr_prime D.S.pr_inj (priceExponent_nonneg ha) D.index.t
    (fun e => hRI e)

/-- **`FixedIntervalEnvelopeEnergies` with the conductor price** (`lem:envelope-energy` at fixed
intervals, `lem:hyb:moment`): WP-R's `Structured.fixedIntervalEnvelopeEnergies_of_terms` with
`Π_𝒮 = ∏_{e ∈ 𝒮} K^{2θ/d} (K sq(D_{𝒥_e}))^{2a/d}`, the moment hypothesis discharged
(`expect_fixedPrice_le`) from `IndexMomentBound`. -/
theorem fixedIntervalEnvelopeEnergies_of_conductor
    (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a) (hRI : IndexMomentBound D)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rL rR : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ)
    (htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |reservedCut.form
          (tensorLaw fun b => if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (TheoremCBlock.wrapSourceHalf m₀ blk p pr h hcop D.S.Q.u L A S) ω)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (TheoremCBlock.wrapSourceHalf m₀ blk p pr h hcop D.S.Q.u L A S) ω)| ≤
        (D.B + z L) * fixedPrice pr h (priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) + rL L A S Jq ω f))
    (htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : BlockAtom Bk J L → Bool),
      |reservedCut.form
          (tensorLaw fun b => if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (TheoremCBlock.wrapTargetHalf m₀ blk p pr h hcop D.S.Q.w L A S) ω)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (TheoremCBlock.wrapTargetHalf m₀ blk p pr h hcop D.S.Q.w L A S) ω)| ≤
        (D.B + z L) * fixedPrice pr h (priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1) + rR L A S Jq ω f))
    (hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rL L A S Jq ω f)) ≤ remainder c L A))
    (hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rR L A S Jq ω f)) ≤ remainder c L A)) :
    D.FixedIntervalEnvelopeEnergies hcop := by
  refine TheoremCBlock.Structured.fixedIntervalEnvelopeEnergies_of_terms hcop D z hz0 hzt hc
    (fun _ S Jq _ => fixedPrice pr h (priceExponent a) S Jq)
    (fun _ S Jq _ => fixedPrice_nonneg pr h (priceExponent a) S Jq) (fun L S => ?_) rL rR htermL
    htermR hremL hremR
  simp only [FiniteLaw.expect_const]
  exact expect_fixedPrice_le pr h D.S.pr_prime D.S.pr_inj (priceExponent_nonneg ha) S
    (fun e => coordTails blockScale pr h (D.S.index.t e)) (fun e => hRI e)

end TheoremC

end Sarkozy.EnvelopeInputsBlock
