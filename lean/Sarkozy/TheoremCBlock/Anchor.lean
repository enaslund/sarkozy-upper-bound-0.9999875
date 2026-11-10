module

public import Sarkozy.TheoremCBlock.MainEnvelope
public import Sarkozy.TheoremCParam.Anchor

@[expose] public section

/-!
# Theorem C (reduced form) on the block atoms at the formal exponent `a₀`

`Sarkozy.TheoremCParam.Anchor` for the block atoms of `Sarkozy.BlockFrame` (K0): the comparison
data carry one selection factor per prefix block (`def:price`).

`Sarkozy.TheoremCParam.ComparisonData.theoremC_reduced` and its two siblings at the anchor
exponents `Params.anchor = Params.ofDecay a₀`, `a₀ = 8896611739/10¹³`, with the conclusion in
the target's form `Target.SarkozyBound Param.anchorSaving`. The side conditions `hP` and `0 ≤ a₀`
are discharged (`Params.anchor_valid`). The comparison data `D : ComparisonData a₀ …` carry
the prices at `a₀`: the selection factor is `p^{2a₀}` at a tail prime and `D.S.selPre β` at the
prefix block `β`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCBlock

open Sarkozy.TheoremC
open Sarkozy.BlockFrame
open Sarkozy.Param (Params)

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : ComparisonData Params.anchorDecay m₀ blk p pr h E)
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Theorem C at the formal exponent** (`thm:comparison` in the closing form used by
`thm:density:induction`, at `a = a₀`; reduced form). For comparison data `D` at the price
exponent `a₀` with `𝓔 ≥ Ψ` and closing number `Θ(𝓔) < 1`, and the remaining analytic inputs
(`EnvelopeBound`, `SharpFirstTerms`, `DensityCancellation` = `lem:record:density-can`,
`FixedIntervalEnvelopeEnergies`, `EnvelopeEnergies`, the unit mixed `L³⁶` bound of the large
prime laws), every square-difference-free `A ⊆ [1, N]` has `|A| ≤ C N^{1−ε′}`,
`ε′ = Target.epsAnchor`. All of these inputs are hypotheses, at the exponent `a₀`. -/
theorem theoremC_reduced_anchor {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound Param.anchorSaving :=
  Param.anchor_powerSavingBound_iff.mp
    (D.theoremC_reduced hcop Params.anchor_valid TheoremCParam.ComparisonData.anchorDecay_nonneg
      h𝓔 hΘ hE1 hSF hDC hfix henv hunit)

/-- **Theorem C, first conclusion, at the formal exponent**: `α^{72} ≤ 𝒴(L, A) ≤ C L^{-a₀} α^ϑ`
under the hypotheses of `theoremC_reduced_anchor`. -/
theorem theoremC_energy_reduced_anchor {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.ScaledEnergyEstimate Params.anchor D.Y :=
  D.theoremC_energy_reduced hcop Params.anchor_valid
    TheoremCParam.ComparisonData.anchorDecay_nonneg h𝓔 hΘ hE1 hSF hDC hfix henv hunit

/-- **Theorem C with the (CP5) class bounds at the formal exponent** (reduced form). -/
theorem theoremC_classes_reduced_anchor (CB : ClassBounds Params.anchorDecay m₀ blk p D.CL) {𝓔 : ℝ}
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hΘ : D.Theta 𝓔 < 1) (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms) (hDC : DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound Param.anchorSaving :=
  Param.anchor_powerSavingBound_iff.mp
    (D.theoremC_classes_reduced hcop Params.anchor_valid
      TheoremCParam.ComparisonData.anchorDecay_nonneg CB hΨ hΘ hE1 hCB hSF hDC hfix henv hunit)

end ComparisonData

end Sarkozy.TheoremCBlock
