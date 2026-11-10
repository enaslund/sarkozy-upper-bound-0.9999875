module

public import Sarkozy.PaperFrame.Assembly
public import Sarkozy.PaperFrame.TailFamily

@[expose] public section

/-!
# The concrete main theorem for the paper's tail family

`paperMain_powerSavingBound_canonical` is `paperMain_powerSavingBound_concrete_ref` for the
paper's tail `𝒯_N = {p prime : P₄ ≤ p, p^{20} ≤ N}` (`tailPrimes P₄`, with `J L = ↥𝒯_{KL}` and
`p L j = j`): the hypotheses that the tail moduli are distinct primes are discharged.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  (P4 : ℕ)
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The concrete main theorem for the paper's tail family.** All hypotheses of
`paperMain_powerSavingBound_concrete_ref` except the primality and distinctness of the tail
moduli, which hold for `tailPrimes P₄`. -/
theorem paperMain_powerSavingBound_canonical
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
    (lam ML ν MR : ∀ L b, ((Slot → AtomLabel m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (εwrap εenv εfirst εjoint : ℕ → ℝ) (cwrap cenv cfirst cjoint : ℝ)
    (hεwrap : Tendsto εwrap atTop (𝓝 0)) (hεenv : Tendsto εenv atTop (𝓝 0))
    (hεfirst : Tendsto εfirst atTop (𝓝 0)) (hεjoint : Tendsto εjoint atTop (𝓝 0))
    (hcwrap : 0 ≤ cwrap) (hcenv : 0 ≤ cenv) (hcfirst : 0 ≤ cfirst) (hcjoint : 0 ≤ cjoint)
    (wrap : AtCounterexamples (energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) pr h hcop L A e)
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A +
          (2 ^ 6 * l.W + εwrap L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A +
          remainder cwrap L A)
    (envelopeL : AtCounterexamples (energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A ≤
        (2 ^ 6 * l.J + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A +
          remainder cenv L A)
    (envelopeR : AtCounterexamples (energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A ≤
        (2 ^ 6 * l.J + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A +
          remainder cenv L A)
    (firstStage : AtCounterexamples (energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))))
      fun L A =>
        (1 - l.L₀ - εfirst L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A -
          remainder cfirst L A ≤ energyFirst lam (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A)
    (joint : AtCounterexamples (energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A - energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A) -
          (energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) ML L A + energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) MR L A) / 2 ≤
        (2 ^ 6 * l.jointConstant - 1 + εjoint L) *
            energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A + remainder cjoint L A) :
    PowerSavingBound :=
  paperMain_powerSavingBound_concrete_ref m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))
    pr h hcop (fun L j => tailPrimes_prime P4 L j.1 j.2) (fun _ => Subtype.val_injective)
    μ₀ μp hm₀ hp₀ hmp hpp hunit hledger μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr
    εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint
    hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint

end Sarkozy.PaperFrame
