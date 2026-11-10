module

public import Sarkozy.EnvelopesPaper.Mean
public import Sarkozy.EnvelopesPaper.Summability

@[expose] public section

/-!
# Non-vacuity of the inputs of `Sarkozy.EnvelopesPaper`

The three input structures are satisfiable for every Gram bracket `GB` and comparison law `CL`;
their content is in their numbers (the side sums `hTs` against `T^{ledger}`, the size of the mean
credit `m` demanded by `hm`, and the bounds `σ_CL`, `σ_K`), not in their shape:

* `EnvelopeRefinement`: `trivialRefinement GB CL` (`Matching.lean`);
* `MeanInputs`: `MeanInputs.zero F`, with `m = 0`, for every refinement `F` (the cores are positive
  at `ι`, so their mean energies are nonnegative: `energyMean_nonneg`);
* `SummabilityInputs`: `SummabilityInputs.ofTrivial`, with `σ_K = 0`, for the trivial refinement,
  from any weighted bound `σ_CL` of the (CP4) prices.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopesPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.Comparison
open Sarkozy.RecordExpansion (symTotal skewTotal)

/-- The mean energy of a product of laws positive at `ι` is nonnegative. -/
theorem energyMean_nonneg {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
    {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]
    (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)
    (C : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ) (hC : ∀ L b, reservedCut.Positive (C L b))
    (L : ℕ) (A : Finset ℤ) : 0 ≤ energyMean F C L A :=
  (ReflectionCut.Positive.tensor (hC L)).nonneg _

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R} {GB : GramBracket a m₀ blk p S₀ FS}
  {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}

variable (a) in
/-- **`MeanInputs` is satisfiable** for every refinement, with the mean credit `m = 0`. -/
noncomputable def MeanInputs.zero (F : EnvelopeRefinement GB CL) : MeanInputs a F where
  m := 0
  bound := by
    refine ⟨fun _ => 0, tendsto_const_nhds, 0, le_refl 0, ?_⟩
    unfold Param.AtCounterexamples
    filter_upwards with L
    intro _ _ _ A _ _
    have h1 := energyMean_nonneg (blockLift m₀ blk p) F.coreL F.coreL_positive L A
    have h2 := energyMean_nonneg (blockLift m₀ blk p) F.coreR F.coreR_positive L A
    have h0 : Sarkozy.Comparison.remainder 0 L A = 0 := by
      unfold Sarkozy.Comparison.remainder
      ring
    rw [h0]
    linarith

omit [∀ L, DecidableEq (J L)] in
/-- **`SummabilityInputs` is satisfiable** for the trivial refinement, from any weighted bound of
the (CP4) prices, with `σ_K = 0`. -/
noncomputable def SummabilityInputs.ofTrivial (σ : ℝ)
    (hσ : ∀ L, ∑ b, oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) *
      (symTotal (CL.π L) b + skewTotal (CL.π L) b) ≤ σ) :
    SummabilityInputs pp ep (trivialRefinement GB CL) where
  σCL := σ
  hCL := hσ
  σK := 0
  hK L := by
    apply le_of_eq
    apply sum_eq_zero
    intro b _
    change _ * ((∑ i : Empty, _) + ∑ i : Empty, _) = 0
    simp

end Sarkozy.EnvelopesPaper
