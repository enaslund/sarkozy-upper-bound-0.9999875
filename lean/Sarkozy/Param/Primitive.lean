module

public import Sarkozy.Param.Criterion
public import Sarkozy.Comparison.Final

@[expose] public section

/-!
# The parametrized endgame with the closing ledgers

Parametrized copies of the ledger forms of the endgame:

* `powerSavingBound_of_jointClosing`, `powerSavingBound_of_rawComparison_ledger`: the composite
  ledger `Sarkozy.ClosingLedger` (`Sarkozy/Induction.lean`, `Sarkozy/RelativeErrors.lean`);
* `powerSavingBound_of_rawComparison_primitive`, `powerSavingBound_of_closingEstimates_primitive`:
  the primitive ledger `Sarkozy.Comparison.PrimitiveLedger` of `tab:four-routes-ledger`
  (`Sarkozy/Comparison/ClosingNumerics.lean`, `Sarkozy/Comparison/Final.lean`);
* `PrefixedResidueModel.powerSavingBound_of_closingEstimates`: the prefixed residue model
  (`Sarkozy/Comparison/Final.lean`), where reflection and the global moment bound are proved.

**Scope of the ledgers.** The closing numbers `ClosingLedger.theta` and `PrimitiveLedger.theta`
are formulas in their entries; the entries are hypotheses. The wrapping term
`PrimitiveLedger.W` uses the wrap factor `K^{−1+ϑ/36}` at the paper's `(ϑ, K)`, so the primitive
forms are stated for `Params.ofDecay a` (the paper's `(ϑ, K, σ, η)`, free `a`). The numerical
bounds `PrimitiveLedger.Bounds` are the outward-rounded entries of `tab:four-routes-ledger`,
computed in the paper at the record `a = \FourRoutesA`. Whether the primitive totals at another
`a`, such as the anchor `a₀`, satisfy the same bounds is not decided here: it is a hypothesis.
The general form `Sarkozy.Param.powerSavingBound_of_closingEstimates` takes the closing number
`jointTheta k L₀ J W H < 1` itself as the hypothesis.
-/

open Filter
open scoped Topology

namespace Sarkozy.Param

open Sarkozy.Comparison (jointTheta PrimitiveLedger)

variable {P : Params}

/-- The joint-closing form of the scalar induction with the composite ledger
(`Sarkozy.powerSavingBound_of_jointClosing` in general). -/
theorem powerSavingBound_of_jointClosing (hP : P.Valid)
    {l : ClosingLedger} (hledger : l.Bounds)
    {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hC : 0 < C)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hinit : ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt P Y C L)
    (hrec : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt P Y C k) →
      ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
        C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A →
        Y L A ≤ (l.theta + error L A) * Y L A)
    (herror : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → error L A ≤ closingMargin) :
    PowerSavingBound P := by
  apply powerSavingBound_of_scaledEnergyEstimate hP
  apply scaledEnergyEstimate_of_contraction P hC hreflection hinit hrec
  intro L hL hlarge A hA
  exact ClosingLedger.perturbed_lt_one hledger (herror L hL hlarge A hA)

/-- The raw-comparison endgame with the composite ledger
(`Sarkozy.powerSavingBound_of_rawComparison` in general). -/
theorem powerSavingBound_of_rawComparison_ledger (hP : P.Valid)
    {l : ClosingLedger} (hledger : l.Bounds)
    {Y : ℕ → Finset ℤ → ℝ} {M E : ℝ} {q : ℕ → ℝ}
    (hM : 0 < M) (hE : 0 ≤ E)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound P Y M) (hrec : RawComparison P Y q E)
    (hq : Tendsto q atTop (𝓝 l.theta)) : PowerSavingBound P :=
  powerSavingBound_of_rawComparison hP hM hE (ClosingLedger.theta_lt_one hledger)
    hreflection hglobal hrec hq

/-- The raw-comparison endgame with the primitive ledger of `tab:four-routes-ledger`, at the
paper's `(ϑ, K, σ, η)` and a free price exponent `a`
(`Sarkozy.Comparison.powerSavingBound_of_rawComparison_primitive` in general). -/
theorem powerSavingBound_of_rawComparison_primitive {a : ℝ} (hP : (Params.ofDecay a).Valid)
    {l : PrimitiveLedger} (hledger : l.Bounds)
    {Y : ℕ → Finset ℤ → ℝ} {M E : ℝ} {q : ℕ → ℝ}
    (hM : 0 < M) (hE : 0 ≤ E)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound (Params.ofDecay a) Y M)
    (hrec : RawComparison (Params.ofDecay a) Y q E)
    (hq : Tendsto q atTop (𝓝 l.theta)) : PowerSavingBound (Params.ofDecay a) :=
  powerSavingBound_of_rawComparison hP hM hE (l.theta_lt_one hledger) hreflection hglobal hrec hq

/-- **The parametrized endgame with the primitive ledger**, at the paper's `(ϑ, K, σ, η)` and a
free price exponent `a` (`Sarkozy.Comparison.powerSavingBound_of_closingEstimates_primitive` in
general): six queries, joint constant `l.jointConstant`, and the fourteen primitive bounds of
`tab:four-routes-ledger` as hypotheses (`cert:four-routes-closing`, `eq:final-joint-closing`). -/
theorem powerSavingBound_of_closingEstimates_primitive {a : ℝ} (hP : (Params.ofDecay a).Valid)
    {Y : ℕ → Finset ℤ → ℝ} {M : ℝ} {l : PrimitiveLedger} (hledger : l.Bounds) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound (Params.ofDecay a) Y M)
    (e : ClosingEstimates (Params.ofDecay a) Y 6 l.L₀ l.J l.W l.jointConstant) :
    PowerSavingBound (Params.ofDecay a) :=
  powerSavingBound_of_closingEstimates hP (l.jointTheta_lt_one hledger) hM hreflection hglobal e

/-- **The parametrized endgame for the prefixed residue model**, at the paper's `(ϑ, K, σ, η)`
and a free price exponent `a`, with the closing number as a hypothesis. The reflection lower
bound and the global moment bound are proved for this model class, as in
`Sarkozy.Comparison.PrefixedResidueModel.powerSavingBound_of_closingEstimates`: they do not
involve `a`. -/
theorem PrefixedResidueModel.powerSavingBound_of_closingEstimates_theta {a : ℝ}
    (hP : (Params.ofDecay a).Valid)
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {X₀ : Type} [AddCommGroup X₀] [Fintype X₀]
    (model : Sarkozy.PrefixedResidueModel p X₀) (ha : model.Arithmetic p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {C : ℝ} (hC : 0 < C)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    {k : ℕ} {L₀ J W H : ℝ} (hθ : jointTheta k L₀ J W H < 1)
    (e : ClosingEstimates (Params.ofDecay a) (model.toFourierModel p X₀).energy k L₀ J W H) :
    PowerSavingBound (Params.ofDecay a) := by
  obtain ⟨D, hD, hlift⟩ := model.exists_liftMomentBound p X₀ ha
  have hr := model.regular p X₀ hprefix hzero hm hp
  exact powerSavingBound_of_closingEstimates hP hθ (mul_pos hC (pow_pos hD 2))
    (fun L hL A _ => (model.toFourierModel p X₀).density_pow_le_energy hr L hL A)
    ((model.toFourierModel p X₀).globalMomentBound_of_mixed hC.le hmixed hlift) e

/-- The energy form for the prefixed residue model, free price exponent
(`Sarkozy.TheoremC.prefixedResidueModel_scaledEnergyEstimate_theta` in general):
`α^{72} ≤ Y ≤ C L^{-a} α^ϑ` for the model's energy. -/
theorem PrefixedResidueModel.scaledEnergyEstimate_of_closingEstimates_theta {a : ℝ}
    (hP : (Params.ofDecay a).Valid)
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {X₀ : Type} [AddCommGroup X₀] [Fintype X₀]
    (model : Sarkozy.PrefixedResidueModel p X₀) (ha : model.Arithmetic p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {C : ℝ} (hC : 0 < C)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    {k : ℕ} {L₀ J W H : ℝ} (hθ : jointTheta k L₀ J W H < 1)
    (e : ClosingEstimates (Params.ofDecay a) (model.toFourierModel p X₀).energy k L₀ J W H) :
    ScaledEnergyEstimate (Params.ofDecay a) (model.toFourierModel p X₀).energy := by
  obtain ⟨D, hD, hlift⟩ := model.exists_liftMomentBound p X₀ ha
  have hr := model.regular p X₀ hprefix hzero hm hp
  exact scaledEnergyEstimate_of_closingEstimates hP hθ (mul_pos hC (pow_pos hD 2))
    (fun L hL A _ => (model.toFourierModel p X₀).density_pow_le_energy hr L hL A)
    ((model.toFourierModel p X₀).globalMomentBound_of_mixed hC.le hmixed hlift) e

/-- The prefixed residue model with the primitive ledger
(`Sarkozy.Comparison.PrefixedResidueModel.powerSavingBound_of_closingEstimates` in general). -/
theorem PrefixedResidueModel.powerSavingBound_of_closingEstimates {a : ℝ}
    (hP : (Params.ofDecay a).Valid)
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {X₀ : Type} [AddCommGroup X₀] [Fintype X₀]
    (model : Sarkozy.PrefixedResidueModel p X₀) (ha : model.Arithmetic p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {C : ℝ} (hC : 0 < C)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    {l : PrimitiveLedger} (hledger : l.Bounds)
    (e : ClosingEstimates (Params.ofDecay a) (model.toFourierModel p X₀).energy 6 l.L₀ l.J l.W
      l.jointConstant) : PowerSavingBound (Params.ofDecay a) :=
  PrefixedResidueModel.powerSavingBound_of_closingEstimates_theta hP model ha hprefix hzero hm hp
    hC hmixed (l.jointTheta_lt_one hledger) e

end Sarkozy.Param
