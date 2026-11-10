module

public import Sarkozy.TheoremC.Energy
public import Sarkozy.TheoremC.Classes
public import Sarkozy.TheoremC.Cancellation
public import Sarkozy.TheoremC.WrapTerms

@[expose] public section

/-!
# Theorem C with the reduced hypotheses

`theoremC` (`Main.lean`) takes five conclusions of Section 10 lemmas as hypotheses. Two of
them are derived in this package:

* `NonwrappingCancellation` (the nonwrapping terms of `lem:record:wrap-expansion`) from
  `DensityCancellation`, the paper's `lem:record:density-can` over the PaperFrame objects
  (`Cancellation.lean`, `nonwrappingCancellation_of_densityCancellation'`; the coefficient
  bound `∏_𝔟 |ν|_𝔟 ≤ 𝔳_ν e^{P+S}` is proved from (CP2)–(CP4), `coefficient_bound`);
* `WrappingTerms` (the fully wrapping terms) from `lem:record:common-mean`(b) (WP-S) and
  `FixedIntervalEnvelopeEnergies`, `lem:envelope-energy` at fixed intervals with
  `T_Q = S + A` (`WrapTerms.lean`, `wrappingTerms_of_envelope`).

The theorems below are Theorem C with these substitutions. Their hypotheses beyond the
comparison data are:

1. `DensityCancellation` — `lem:record:density-can`, one of the two analytic inputs;
2. `EnvelopeBound` — (E1) for the envelopes of the selections (`lem:bracket-energy`);
3. `SharpFirstTerms` — the per-term bounds of `lem:sharp-first`;
4. `EnvelopeEnergies` and `FixedIntervalEnvelopeEnergies` — `lem:envelope-energy` in its two
   uses (uniform intervals with `Q = M_s − Ñ`; fixed intervals with `Q = ∑ π̃ D`);
5. `hunit` — the unit mixed `L³⁶` bound of the large-prime reference laws (endgame).

Items 2–4 are lemmas of Section 10 whose analytic input is
`prop:record:density-structured`; their reductions to it are not formalized.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.TheoremC

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] (D : ComparisonData m₀ p pr h E)
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The five closing estimates of Theorem C, reduced** (no (CP5) classes). -/
theorem closingEstimates_reduced {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hE1 : D.EnvelopeBound)
    (hSF : D.SharpFirstTerms) (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop) :
    Nonempty (ClosingEstimates D.Y (Fintype.card E) D.L₀ D.Jc D.W
      (jointConstantC (Fintype.card E) 𝓔 D.MC.m)) :=
  D.closingEstimates hcop h𝓔 hE1 hSF (D.nonwrappingCancellation_of_densityCancellation' hcop hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv

/-- **Theorem C** (`thm:comparison`), reduced form: comparison data with
`𝓔 ≥ B(e^S cosh A − 1)` and `Θ < 1` give `s(N) ≤ C N^{1−ε}`. -/
theorem theoremC_reduced {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    PowerSavingBound :=
  D.theoremC hcop h𝓔 hΘ hE1 hSF (D.nonwrappingCancellation_of_densityCancellation' hcop hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv hunit

/-- **Theorem C, first conclusion**, reduced form: `α^{72} ≤ 𝒴(L, A) ≤ C L^{-a} α^θ`. -/
theorem theoremC_energy_reduced {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    ScaledEnergyEstimate D.Y :=
  D.theoremC_energy hcop h𝓔 hΘ hE1 hSF (D.nonwrappingCancellation_of_densityCancellation' hcop hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv hunit

/-- **Theorem C with the (CP5) class bounds**, reduced form. -/
theorem theoremC_classes_reduced (CB : ClassBounds m₀ p D.CL) {𝓔 : ℝ}
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hΘ : D.Theta 𝓔 < 1) (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms) (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    PowerSavingBound :=
  D.theoremC_classes hcop CB hΨ hΘ hE1 hCB hSF
    (D.nonwrappingCancellation_of_densityCancellation' hcop hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv hunit

end ComparisonData

end Sarkozy.TheoremC
