module

public import Sarkozy.TheoremC.MainEnvelope
public import Sarkozy.TheoremCParam.Energy
public import Sarkozy.TheoremCParam.Classes
public import Sarkozy.TheoremCParam.Cancellation
public import Sarkozy.TheoremCParam.WrapTerms

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] (D : ComparisonData a m₀ p pr h E)
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The five closing estimates of Theorem C, reduced** (no (CP5) classes). -/
theorem closingEstimates_reduced (ha : 0 ≤ a) {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hE1 : D.EnvelopeBound)
    (hSF : D.SharpFirstTerms) (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop) :
    Nonempty (Param.ClosingEstimates (Params.ofDecay a) D.Y (Fintype.card E) D.L₀ D.Jc D.W
      (jointConstantC (Fintype.card E) 𝓔 D.MC.m)) :=
  D.closingEstimates hcop h𝓔 hE1 hSF (D.nonwrappingCancellation_of_densityCancellation' hcop ha hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv

/-- **Theorem C** (`thm:comparison`), reduced form: comparison data with
`𝓔 ≥ B(e^S cosh A − 1)` and `Θ < 1` give `s(N) ≤ C N^{1−ε}`. -/
theorem theoremC_reduced (hP : (Params.ofDecay a).Valid) (ha : 0 ≤ a)
    {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.PowerSavingBound (Params.ofDecay a) :=
  D.theoremC hcop hP h𝓔 hΘ hE1 hSF (D.nonwrappingCancellation_of_densityCancellation' hcop ha hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv hunit

/-- **Theorem C, first conclusion**, reduced form: `α^{72} ≤ 𝒴(L, A) ≤ C L^{-a} α^θ`. -/
theorem theoremC_energy_reduced (hP : (Params.ofDecay a).Valid) (ha : 0 ≤ a)
    {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.ScaledEnergyEstimate (Params.ofDecay a) D.Y :=
  D.theoremC_energy hcop hP h𝓔 hΘ hE1 hSF
      (D.nonwrappingCancellation_of_densityCancellation' hcop ha hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv hunit

/-- **Theorem C with the (CP5) class bounds**, reduced form. -/
theorem theoremC_classes_reduced (hP : (Params.ofDecay a).Valid) (ha : 0 ≤ a)
    (CB : ClassBounds a m₀ p D.CL) {𝓔 : ℝ}
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hΘ : D.Theta 𝓔 < 1) (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms) (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.PowerSavingBound (Params.ofDecay a) :=
  D.theoremC_classes hcop hP CB hΨ hΘ hE1 hCB hSF
    (D.nonwrappingCancellation_of_densityCancellation' hcop ha hDC)
    (D.wrappingTerms_of_envelope hcop hfix) henv hunit

end ComparisonData

end Sarkozy.TheoremCParam
