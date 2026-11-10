module

public import Sarkozy.PaperFrame.Main
public import Sarkozy.PaperFrame.Bridge
public import Sarkozy.PaperFrame.Reference

@[expose] public section

/-!
# Assembly: the expansion for the paper's objects and the main theorem over one atom set

* `paper_signedIndexForm_sub_eq`: `eq:record:expansion` for the paper's coupled index,
  inputs and lift, `J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} I_{ν,𝒮}`, with the coupled
  forms `I_{ν,𝒮}` in WP-S's operator form (the hypothesis `hexp` of
  `Sarkozy.Comparison.wrap_summation`, before the split of `I_{ν,𝒮}` by the wrapping
  queries). The mean identity it needs is `expect_atomInput`.
* `paperMain_powerSavingBound_concrete_ref`: the concrete main theorem with the paper's
  functional written as the frame energy of the reference laws over the same atoms,
  `Y = energyFirst refLaws F_A` (`energyFirst_refLaws`). Every closing hypothesis then
  compares energies of the same lift `F_A` on the same atoms under different per-atom
  laws (reference `μ`, first stage `λ`, comparison `ν`, envelopes `M_L, M_R`).
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

/-- `eq:record:expansion` for the paper's objects: with the paper's coupled index, inputs
`g^{I_b,M₀,s}` at both ends and lift `F_A`, for every comparison law `ν`,
`J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} I_{ν,𝒮}`. -/
theorem paper_signedIndexForm_sub_eq (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ν : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ) :
    signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
        (fun L A e => atomInput m₀ p pr h hcop L A e)
        (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A -
        2 ^ Fintype.card E * energyComparison ν (atomLift m₀ p) L A =
      ∑ S ∈ (univ : Finset E).powerset.filter (fun S => S ≠ ∅),
        (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
          (FiniteLaw.uniform (E → ∀ j, CoordSpace blockScale pr h j)).expect (fun ω =>
            reservedCut.form (tensorLaw (ν L))
              (productHalf u (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A) ω)
              (act (piKron (fun e => if e ∈ S then
                  piKron (coordTransition blockScale pr h (μ e))
                else meanMatrix (∀ j, CoordSpace blockScale pr h j)))
                (productHalf w (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A)) ω)) :=
  signedIndexForm_sub_eq (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
    (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p)
    (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y) L A

/-- **The concrete main theorem over one atom set.** Identical to
`paperMain_powerSavingBound_concrete`, with the paper's functional written as the frame
energy `energyFirst refLaws F_A` of the reference laws over the same atoms
(`energyFirst_refLaws`), so that every closing inequality compares energies of the same
lift on the same atoms. -/
theorem paperMain_powerSavingBound_concrete_ref (hp : ∀ L j, (p L j).Prime)
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
    (wrap : AtCounterexamples (energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ p) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ p pr h hcop L A e)
            (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A +
          (2 ^ 6 * l.W + εwrap L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A +
          remainder cwrap L A)
    (envelopeL : AtCounterexamples (energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * l.J + εenv L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A +
          remainder cenv L A)
    (envelopeR : AtCounterexamples (energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * l.J + εenv L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A +
          remainder cenv L A)
    (firstStage : AtCounterexamples (energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p))
      fun L A =>
        (1 - l.L₀ - εfirst L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A -
          remainder cfirst L A ≤ energyFirst lam (atomLift m₀ p) L A)
    (joint : AtCounterexamples (energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p)) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ p) L A - energyComparison ν (atomLift m₀ p) L A) -
          (energyMean (atomLift m₀ p) ML L A + energyMean (atomLift m₀ p) MR L A) / 2 ≤
        (2 ^ 6 * l.jointConstant - 1 + εjoint L) *
            energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A + remainder cjoint L A) :
    PowerSavingBound := by
  have hY : energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp)
      (atomLift m₀ p) = prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) :=
    funext fun L => funext fun A => energyFirst_refLaws m₀ p μ₀ μp L A
  rw [hY] at wrap envelopeL envelopeR firstStage joint
  exact paperMain_powerSavingBound_concrete m₀ p pr h hcop hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit
    hledger μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr εwrap εenv εfirst εjoint cwrap cenv
    cfirst cjoint hεwrap hεenv hεfirst hεjoint hcwrap hcenv hcfirst hcjoint wrap envelopeL
    envelopeR firstStage joint

end Sarkozy.PaperFrame
