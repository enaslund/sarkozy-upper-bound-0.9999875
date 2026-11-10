module

public import Sarkozy.OpsVariance.Conjunct
public import Sarkozy.MainFinal2.Bundles

@[expose] public section

/-!
# The field `ClassStepsOps.H` from its three conjuncts

`MainFinal2/Bundles.lean`, `structure ClassStepsOps`, field `H`: at every least counterexample,
the operator data of every degree class, the variance steps of every variance class, and the summed
remainders. `classStepsOpsH_of_conjuncts` combines the three conjuncts, each given at the
counterexamples, into `H` (the filters intersect). Its second argument has exactly the type of the
conclusion of `varConjunct`, `varConjunct_noCredit` (`Conjunct.lean`) and of their versions at the
obligations' data (`varConjunct_front`, `varConjunct_noCredit_front`), so the variance part of `ops`
is plugged in by this theorem. `classStepsOps_of_conjuncts` builds the structure.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.MainFinal2
open Sarkozy.Param (Params)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

omit [DecidableEq P] in
/-- **`ClassStepsOps.H` from its three conjuncts**, each at the least counterexamples. -/
theorem classStepsOpsH_of_conjuncts (cd : ClassData D.CL) {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
    (Z : ∀ L, Finset ℤ → Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ) (z : ℕ → ℝ) (K c₀ : ℝ)
    (rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ)
    (hdeg : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      ∀ n : {n // n ∈ cd.N}, Nonempty (EnvelopeSteps.DegreeOps reservedCut (cd.clsSel L (.inl n))
        (EnvelopeSteps.termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A)
        (∑ j, wc L (.inl n) j * Z L A j) (D.Y L A) (z L) K))
    (hvar : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      ∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v))
        (EnvelopeSteps.termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A)
        (∑ j, wc L (.inr v) j * Z L A j) (D.Y L A) (z L) K))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      ∑ ω ∈ cd.sel L, rr L A ω ≤ Comparison.remainder c₀ L A) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (∀ n : {n // n ∈ cd.N}, Nonempty (EnvelopeSteps.DegreeOps reservedCut (cd.clsSel L (.inl n))
        (EnvelopeSteps.termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A)
        (∑ j, wc L (.inl n) j * Z L A j) (D.Y L A) (z L) K)) ∧
      (∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v))
        (EnvelopeSteps.termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A)
        (∑ j, wc L (.inr v) j * Z L A j) (D.Y L A) (z L) K)) ∧
      ∑ ω ∈ cd.sel L, rr L A ω ≤ Comparison.remainder c₀ L A := by
  filter_upwards [hdeg, hvar, hrem] with L h1 h2 h3
  intro C hC hind A hA hcount
  exact ⟨h1 C hC hind A hA hcount, h2 C hC hind A hA hcount, h3 C hC hind A hA hcount⟩

omit [DecidableEq P] in
/-- **`ClassStepsOps` from its data and the three conjuncts** of `H`. -/
noncomputable def classStepsOps_of_conjuncts (cd : ClassData D.CL) (Θ : ℕ → Type)
    [∀ L, Fintype (Θ L)] (Z : ∀ L, Finset ℤ → Θ L → ℝ) (wc : ∀ L, cd.ι L → Θ L → ℝ)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ) (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L)
    (hz : Tendsto z atTop (𝓝 0)) (K c₀ : ℝ) (hc₀ : 0 ≤ c₀)
    (rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (hrr0 : ∀ L A ω, 0 ≤ rr L A ω)
    (hdeg : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      ∀ n : {n // n ∈ cd.N}, Nonempty (EnvelopeSteps.DegreeOps reservedCut (cd.clsSel L (.inl n))
        (EnvelopeSteps.termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A)
        (∑ j, wc L (.inl n) j * Z L A j) (D.Y L A) (z L) K))
    (hvar : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      ∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v))
        (EnvelopeSteps.termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A)
        (∑ j, wc L (.inr v) j * Z L A j) (D.Y L A) (z L) K))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      ∑ ω ∈ cd.sel L, rr L A ω ≤ Comparison.remainder c₀ L A) :
    ClassStepsOps cd Θ Z wc ρ where
  z := z
  hz0 := hz0
  hz := hz
  K := K
  c₀ := c₀
  hc₀ := hc₀
  rr := rr
  hrr0 := hrr0
  H := classStepsOpsH_of_conjuncts cd Z wc ρ z K c₀ rr hdeg hvar hrem

end Sarkozy.OpsVariance
