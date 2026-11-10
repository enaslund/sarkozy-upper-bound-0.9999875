module

public import Sarkozy.TheoremCBlock.Main
public import Sarkozy.TheoremC.Energy
public import Sarkozy.TheoremCParam.Energy

@[expose] public section



open Filter Finset Function
open scoped Topology

namespace Sarkozy.TheoremCBlock

open Sarkozy.TheoremC
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.Comparison Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

namespace ComparisonData

variable {m₀ blk p} {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ}
  [∀ q, NeZero (pr q ^ h q)] {E : Type} [Fintype E] [DecidableEq E]
  (D : ComparisonData a m₀ blk p pr h E) (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Theorem C, first conclusion**: under the hypotheses of `theoremC`, there is a constant
`C` with `α^{72} ≤ 𝒴(L, A) ≤ C L^{-a} α^θ` for every `L ≥ 1` and every
square-difference-free `A ⊆ [KL]`. -/
theorem theoremC_energy (hP : (Params.ofDecay a).Valid) {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.ScaledEnergyEstimate (Params.ofDecay a) D.Y := by
  obtain ⟨e⟩ := D.closingEstimates hcop h𝓔 hE1 hSF hcan hwr henv
  exact Param.ScaledEnergyEstimate.transfer
    (fun L A _ => (energyFirst_blockRefLaws m₀ blk p D.R.μ₀ D.R.μp L A).symm)
    (Param.prefixedFunctional_scaledEnergyEstimate_theta m₀ p hP D.S.p_prime D.S.p_inj
      (blockAssembly m₀ blk D.R.μ₀) D.R.μp (blockAssembly_unif m₀ blk D.R.μ₀ D.R.unif₀)
      (blockAssembly_rp m₀ blk D.R.μ₀ D.R.rp₀).slot D.R.unifp
      (fun q _ hq => (D.R.rpp q hq).slot) hunit (by rw [D.jointTheta_eq_Theta]; exact hΘ)
      (e.transfer fun L A _ => energyFirst_blockRefLaws m₀ blk p D.R.μ₀ D.R.μp L A))

end ComparisonData

end Sarkozy.TheoremCBlock
