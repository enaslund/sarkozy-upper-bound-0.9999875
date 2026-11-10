module

public import Sarkozy.Comparison.ClosingNumerics
public import Sarkozy.Comparison.Criterion
public import Sarkozy.FourierArithmetic.PrefixedModel

/-!
# The conditional main theorem at the level of the closing criterion

The final joint closing `eq:final-joint-closing` is the closing number of
`cor:joint-closing` with `k = 6` queries and joint constant
`H = (63/64) E + (1 - m₁)/64 - Δ_mid - Δ_u + R_u`.
Combined with `Sarkozy.Comparison.PrimitiveLedger.theta_lt_cap` and the robust
closing criterion `Sarkozy.Comparison.ClosingEstimates.rawComparison`, this replaces
two hypotheses of the earlier endgame:

* the `RawComparison` recurrence is replaced by the five robust estimates of the
  closing criterion (wrap, frame, envelope, first stage, joint); and
* the eleven composite ledger bounds (which include `E`, `J`, `W`) are replaced by
  the fourteen primitive totals of `tab:four-routes-ledger`, with the exponential,
  hyperbolic and power evaluations certified in Lean.

The five estimates, the primitive totals, the reference law's structural
properties and its mixed `L³⁶` bound remain hypotheses.
-/

@[expose] public section

open scoped Topology

namespace Sarkozy.Comparison

namespace PrimitiveLedger

variable (l : PrimitiveLedger)

/-- The joint comparison-and-mean constant of the final closing. -/
noncomputable def jointConstant : ℝ :=
  (63 / 64 : ℝ) * l.E + (1 - l.m₁) / 64 -
    (l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) -
    l.deltaUpper + l.upperError

/-- `eq:final-joint-closing` is the joint closing number with six queries. -/
theorem jointTheta_eq : jointTheta 6 l.L₀ l.J l.W l.jointConstant = l.theta := by
  unfold jointTheta jointConstant theta
  norm_num
  ring

theorem jointTheta_lt_one (h : l.Bounds) :
    jointTheta 6 l.L₀ l.J l.W l.jointConstant < 1 := by
  rw [jointTheta_eq]
  exact l.theta_lt_one h

end PrimitiveLedger

/-- **Conditional main theorem, closing-criterion form.** For any energy functional
with the reflection lower bound and the global second-density moment bound, the
five robust closing estimates at the paper's six-query closing data and the
primitive ledger bounds give `s(N) ≤ C N^(1-ε)`, `ε = 1814179/141970826000`. -/
theorem powerSavingBound_of_closingEstimates_primitive
    {Y : ℕ → Finset ℤ → ℝ} {M : ℝ} {l : PrimitiveLedger} (hledger : l.Bounds) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound Y M)
    (e : ClosingEstimates Y 6 l.L₀ l.J l.W l.jointConstant) : PowerSavingBound :=
  powerSavingBound_of_closingEstimates (l.jointTheta_lt_one hledger) hM hreflection hglobal e

/-- **Conditional main theorem for the prefixed residue model.** This is
`Sarkozy.PrefixedResidueModel.powerSavingBound` with the raw comparison replaced by
the five robust closing estimates and the composite ledger replaced by the
primitive one. The Fourier lift's moment estimate is proved for this model class. -/
theorem PrefixedResidueModel.powerSavingBound_of_closingEstimates
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
    (e : ClosingEstimates (model.toFourierModel p X₀).energy 6 l.L₀ l.J l.W
      l.jointConstant) : PowerSavingBound := by
  obtain ⟨D, hD, hlift⟩ := model.exists_liftMomentBound p X₀ ha
  have hr := model.regular p X₀ hprefix hzero hm hp
  exact powerSavingBound_of_closingEstimates_primitive hledger (mul_pos hC (pow_pos hD 2))
    (fun L hL A _ => (model.toFourierModel p X₀).density_pow_le_energy hr L hL A)
    ((model.toFourierModel p X₀).globalMomentBound_of_mixed hC.le hmixed hlift) e

end Sarkozy.Comparison
