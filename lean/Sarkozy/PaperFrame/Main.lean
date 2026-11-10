module

public import Sarkozy.PaperFrame.Inputs
public import Sarkozy.Comparison.PaperMain

@[expose] public section

/-!
# The conditional main theorem with the concrete closing energies

`Sarkozy.Comparison.paperMain_powerSavingBound` assumes `ClosingEstimates` for the paper's
functional, a structure whose auxiliary energies (`Yfs, Yν, Jν, eL, eR, VL, VR`) are
existential fields. `paperMain_powerSavingBound_concrete` replaces them by the concrete
energies of `Sarkozy.Comparison.ConcreteFrame`, built from

* the paper's atoms (`PaperFrame.Atoms`: the prefix and the tail primes),
* the paper's lift `F = F_A` and inputs `φ = ψ = g^{I_b,M₀,s}` (`PaperFrame.Inputs`),
* the paper's coupled index (interval coordinate and prime-power residues; transitions
  interval shift ⊗ convolutions by the increment laws), with the hypotheses `hT, hT0` of
  `CoupledIndex` discharged from the residue-tail bound `hnorm`,
* per-atom first-stage laws `λ`, envelopes `M_L, M_R` and comparison laws `ν`.

The frame estimate `eq:cp:mean-step` is discharged from the brackets (CP6) and the mean
identities (`lem:twointerval`, `expect_atomInput`). The remaining hypotheses are the
per-atom laws with their brackets, `hnorm`, the reference-law hypotheses of
`paperMain_powerSavingBound` (marginals, reflection positivity, unit mixed `L^36` norm of
the large-prime laws), the primitive closing ledger, and the four inequalities
`wrap, envelope (L and R), firstStage, joint` about the concrete energies.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The conditional main theorem with the concrete closing energies.**

For the paper's group, lift, inputs and coupled index (see the module docstring), the
following hypotheses imply `PowerSavingBound`:

* the reference law `paperLaw m₀ p μ₀ μp = μ₀ ⊗ ⊗_{p tail} μ_p` satisfies the hypotheses
  of `paperMain_powerSavingBound`, and the primitive ledger bounds hold;
* the increment laws `μ_{e,q}` are probability laws whose convolutions are bounded on the
  exact-conductor spaces by the tails `t` (`hnorm`, `lem:imp:padic-envelope`);
* the per-atom laws `(M_L, ν, M_R)` form brackets at the reserved cut (CP6);
* the wrap, envelope, first-stage and joint estimates hold for the concrete energies
  (with the stated error terms).

The frame estimate is proved. -/
theorem paperMain_powerSavingBound_concrete (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {l : PrimitiveLedger} (hledger : l.Bounds)
    (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (hμ : ∀ e q r, 0 ≤ μ e q r)
    (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (lam ML ν MR : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (εwrap εenv εfirst εjoint : ℕ → ℝ) (cwrap cenv cfirst cjoint : ℝ)
    (hεwrap : Tendsto εwrap atTop (𝓝 0)) (hεenv : Tendsto εenv atTop (𝓝 0))
    (hεfirst : Tendsto εfirst atTop (𝓝 0)) (hεjoint : Tendsto εjoint atTop (𝓝 0))
    (hcwrap : 0 ≤ cwrap) (hcenv : 0 ≤ cenv) (hcfirst : 0 ≤ cfirst) (hcjoint : 0 ≤ cjoint)
    (wrap : AtCounterexamples (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ p) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ p pr h hcop L A e)
            (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A +
          (2 ^ 6 * l.W + εwrap L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder cwrap L A)
    (envelopeL : AtCounterexamples (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * l.J + εenv L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder cenv L A)
    (envelopeR : AtCounterexamples (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * l.J + εenv L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder cenv L A)
    (firstStage : AtCounterexamples (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) fun L A =>
      (1 - l.L₀ - εfirst L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A -
          remainder cfirst L A ≤ energyFirst lam (atomLift m₀ p) L A)
    (joint : AtCounterexamples (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ p) L A - energyComparison ν (atomLift m₀ p) L A) -
          (energyMean (atomLift m₀ p) ML L A + energyMean (atomLift m₀ p) MR L A) / 2 ≤
        (2 ^ 6 * l.jointConstant - 1 + εjoint L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder cjoint L A) :
    PowerSavingBound :=
  paperMain_powerSavingBound m₀ p hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit hledger
    (ClosingEstimates.ofConcrete (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) lam ML ν MR
      (fun L A e => atomInput m₀ p pr h hcop L A e) (fun L A e => atomInput m₀ p pr h hcop L A e)
      (atomLift m₀ p) hbr (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
      (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
      εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint
      hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint)

end Sarkozy.PaperFrame
