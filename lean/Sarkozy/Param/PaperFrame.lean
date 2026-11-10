module

public import Sarkozy.Param.PaperMain
public import Sarkozy.Param.Anchor
public import Sarkozy.Param.Compat
public import Sarkozy.PaperFrame.Canonical

@[expose] public section

/-!
# The concrete main theorems of `Sarkozy/PaperFrame/` for a free price exponent

Parametrized copies of the PaperFrame chain

`paperMain_powerSavingBound_canonical` → `_concrete_ref` → `_concrete` →
`Sarkozy.Comparison.paperMain_powerSavingBound`

(`Sarkozy/PaperFrame/Canonical.lean`, `Assembly.lean`, `Main.lean`), at `Params.ofDecay a`: the
paper's `(ϑ, K, σ, η)` with a free price exponent `a`. The statements were produced from the
hard-coded ones by a mechanical substitution (`AtCounterexamples` ↦ `AtCounterexamples
(Params.ofDecay a)`, `remainder` ↦ `remainder (Params.ofDecay a)`, `PowerSavingBound` ↦
`PowerSavingBound (Params.ofDecay a)`, plus the side condition `hP`). The `_theta` forms also
replace the primitive ledger by arbitrary closing data `(Lc, Jc, Wc, Hc)` with the hypothesis
`jointTheta 6 Lc Jc Wc Hc < 1`.

* `paperMain_powerSavingBound_concrete_theta`, `paperMain_powerSavingBound_concrete_ref_theta`,
  `paperMain_powerSavingBound_canonical_theta`: the chain with arbitrary closing data.
* `paperMain_powerSavingBound_canonical`: the ledger form, as in the hard-coded theorem.
* `sarkozyBound_epsAnchor_canonical`: **the concrete main theorem at the formal exponent**,
  concluding `Target.SarkozyBound Param.anchorSaving`.
* `paperMain_powerSavingBound_canonical_viaParam`, `…_concrete_ref_viaParam`,
  `…_concrete_viaParam`, `comparison_paperMain_powerSavingBound_viaParam`: the four hard-coded
  theorems of the chain, re-proved (same statements, by `type_of%`) from the parametrized chain
  at the record exponent.

The frame estimate (`eq:cp:mean-step`) is proved, as in the hard-coded chain. The remaining
hypotheses are those listed in `Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete`: the
reference-law hypotheses, `hnorm` (`lem:imp:padic-envelope`), the brackets (CP6), and the wrap,
envelope, first-stage and joint estimates (`lem:record:wrap-expansion`, `lem:envelope-energy`,
`lem:record:first-stage`, `cor:joint-closing`), now at the exponents `Params.ofDecay a`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.Param

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.PaperFrame
open Sarkozy.Comparison (jointTheta PrimitiveLedger energyFirst energyComparison energyMean
  signedIndexForm inclusionEnergyL inclusionEnergyR paperLaw)

section General

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The conditional main theorem with the concrete closing energies, free price exponent**
(`Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete` at `Params.ofDecay a`, arbitrary
closing data). The frame estimate is proved; the four closing inequalities, `hnorm`, the
brackets and the reference-law hypotheses are hypotheses. -/
theorem paperMain_powerSavingBound_concrete_theta {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {Lc Jc Wc Hc : ℝ} (hθ : jointTheta 6 Lc Jc Wc Hc < 1)
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
    (wrap : AtCounterexamples (Params.ofDecay a) (prefixedFunctional m₀ p
        (paperLaw m₀ p μ₀ μp)) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ p) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ p pr h hcop L A e)
            (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A +
          (2 ^ 6 * Wc + εwrap L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder (Params.ofDecay a) cwrap L A)
    (envelopeL : AtCounterexamples (Params.ofDecay a) (prefixedFunctional m₀ p
        (paperLaw m₀ p μ₀ μp)) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * Jc + εenv L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder (Params.ofDecay a) cenv L A)
    (envelopeR : AtCounterexamples (Params.ofDecay a) (prefixedFunctional m₀ p
        (paperLaw m₀ p μ₀ μp)) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * Jc + εenv L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder (Params.ofDecay a) cenv L A)
    (firstStage : AtCounterexamples (Params.ofDecay a) (prefixedFunctional m₀ p
        (paperLaw m₀ p μ₀ μp)) fun L A =>
      (1 - Lc - εfirst L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A -
          remainder (Params.ofDecay a) cfirst L A ≤ energyFirst lam (atomLift m₀ p) L A)
    (joint : AtCounterexamples (Params.ofDecay a) (prefixedFunctional m₀ p
        (paperLaw m₀ p μ₀ μp)) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ p) L A - energyComparison ν (atomLift m₀ p) L A) -
          (energyMean (atomLift m₀ p) ML L A + energyMean (atomLift m₀ p) MR L A) / 2 ≤
        (2 ^ 6 * Hc - 1 + εjoint L) * prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) L A +
          remainder (Params.ofDecay a) cjoint L A) :
    PowerSavingBound (Params.ofDecay a) :=
  Sarkozy.Param.paperMain_powerSavingBound_theta m₀ p hP hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit hθ
    (Sarkozy.Param.ClosingEstimates.ofConcrete (Params.ofDecay a)
        (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) lam ML ν MR
      (fun L A e => atomInput m₀ p pr h hcop L A e) (fun L A e => atomInput m₀ p pr h hcop L A e)
      (atomLift m₀ p) hbr (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
      (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
      εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint
      hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint)

/-- **The concrete main theorem over one atom set, free price exponent**
(`Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete_ref` at `Params.ofDecay a`, arbitrary
closing data), with the paper's functional written as the frame energy of the reference laws. -/
theorem paperMain_powerSavingBound_concrete_ref_theta {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {Lc Jc Wc Hc : ℝ} (hθ : jointTheta 6 Lc Jc Wc Hc < 1)
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
    (wrap : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p)) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ p) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ p pr h hcop L A e)
            (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A +
          (2 ^ 6 * Wc + εwrap L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A +
          remainder (Params.ofDecay a) cwrap L A)
    (envelopeL : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p)) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * Jc + εenv L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A +
          remainder (Params.ofDecay a) cenv L A)
    (envelopeR : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p)) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A ≤
        (2 ^ 6 * Jc + εenv L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A +
          remainder (Params.ofDecay a) cenv L A)
    (firstStage : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p))
      fun L A =>
        (1 - Lc - εfirst L) * energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A -
          remainder (Params.ofDecay a) cfirst L A ≤ energyFirst lam (atomLift m₀ p) L A)
    (joint : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀ p μ₀ μp)
        (atomLift m₀ p)) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ p) L A - energyComparison ν (atomLift m₀ p) L A) -
          (energyMean (atomLift m₀ p) ML L A + energyMean (atomLift m₀ p) MR L A) / 2 ≤
        (2 ^ 6 * Hc - 1 + εjoint L) *
            energyFirst (refLaws m₀ p μ₀ μp) (atomLift m₀ p) L A + remainder
                (Params.ofDecay a) cjoint L A) :
    PowerSavingBound (Params.ofDecay a) := by
  have hY : energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (refLaws m₀ p μ₀ μp)
      (atomLift m₀ p) = prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp) :=
    funext fun L => funext fun A => energyFirst_refLaws m₀ p μ₀ μp L A
  rw [hY] at wrap envelopeL envelopeR firstStage joint
  exact Sarkozy.Param.paperMain_powerSavingBound_concrete_theta m₀ p pr h hcop hP hp hinj μ₀ μp
    hm₀ hp₀ hmp hpp hunit hθ μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr εwrap εenv εfirst
    εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint hcwrap hcenv hcfirst hcjoint
    wrap envelopeL envelopeR firstStage joint

/-- **Compatibility**: the hard-coded `Sarkozy.Comparison.paperMain_powerSavingBound` (same
statement, by `type_of%`) is `paperMain_powerSavingBound` at the record exponent. -/
theorem comparison_paperMain_powerSavingBound_viaParam :
    type_of% @Sarkozy.Comparison.paperMain_powerSavingBound := by
  intro J₀ _ _ m₀ _ J _ _ p _ hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit l hledger e
  exact powerSavingBound_paper.mp (paperMain_powerSavingBound (a := Sarkozy.decay) m₀ p
    Params.paper_valid hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit hledger e.toParam)

/-- **Compatibility**: the hard-coded `Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete`
(same statement, by `type_of%`) is `paperMain_powerSavingBound_concrete_theta` at the record
exponent and the ledger's closing data. -/
theorem paperMain_powerSavingBound_concrete_viaParam :
    type_of% @Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ _ pr h _ hcop E _ _ hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit l
    hledger μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr εwrap εenv εfirst εjoint cwrap cenv cfirst
    cjoint hεwrap hεenv hεfirst hεjoint hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR
    firstStage joint
  exact powerSavingBound_paper.mp (paperMain_powerSavingBound_concrete_theta (a := Sarkozy.decay)
    m₀ p pr h hcop Params.paper_valid hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit
    (l.jointTheta_lt_one hledger) μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr εwrap εenv εfirst
    εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint hcwrap hcenv hcfirst hcjoint
    wrap envelopeL envelopeR firstStage joint)

/-- **Compatibility**: the hard-coded `Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete_ref`
(same statement, by `type_of%`) is `paperMain_powerSavingBound_concrete_ref_theta` at the record
exponent and the ledger's closing data. -/
theorem paperMain_powerSavingBound_concrete_ref_viaParam :
    type_of% @Sarkozy.PaperFrame.paperMain_powerSavingBound_concrete_ref := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ _ pr h _ hcop E _ _ hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit l
    hledger μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr εwrap εenv εfirst εjoint cwrap cenv cfirst
    cjoint hεwrap hεenv hεfirst hεjoint hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR
    firstStage joint
  exact powerSavingBound_paper.mp (paperMain_powerSavingBound_concrete_ref_theta
    (a := Sarkozy.decay) m₀ p pr h hcop Params.paper_valid hp hinj μ₀ μp hm₀ hp₀ hmp hpp hunit
    (l.jointTheta_lt_one hledger) μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr εwrap εenv εfirst
    εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint hcwrap hcenv hcfirst hcjoint
    wrap envelopeL envelopeR firstStage joint)

end General

section Canonical

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  (P4 : ℕ)
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The concrete main theorem for the paper's tail family, free price exponent**
(`Sarkozy.PaperFrame.paperMain_powerSavingBound_canonical` at `Params.ofDecay a`, arbitrary
closing data `(Lc, Jc, Wc, Hc)` with `jointTheta 6 Lc Jc Wc Hc < 1`). The tail is
`𝒯_N = {p prime : P₄ ≤ p, p^{20} ≤ N}`; its primality and distinctness are discharged. -/
theorem paperMain_powerSavingBound_canonical_theta {a : ℝ} (hP : (Params.ofDecay a).Valid)
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {Lc Jc Wc Hc : ℝ} (hθ : jointTheta 6 Lc Jc Wc Hc < 1)
    (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (hμ : ∀ e q r, 0 ≤ μ e q r)
    (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (lam ML ν MR : ∀ L b, ((Slot → AtomLabel m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
        (j : ℕ)) L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (εwrap εenv εfirst εjoint : ℕ → ℝ) (cwrap cenv cfirst cjoint : ℝ)
    (hεwrap : Tendsto εwrap atTop (𝓝 0)) (hεenv : Tendsto εenv atTop (𝓝 0))
    (hεfirst : Tendsto εfirst atTop (𝓝 0)) (hεjoint : Tendsto εjoint atTop (𝓝 0))
    (hcwrap : 0 ≤ cwrap) (hcenv : 0 ≤ cenv) (hcfirst : 0 ≤ cfirst) (hcjoint : 0 ≤ cjoint)
    (wrap : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
          (j : ℕ))) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ)) pr h hcop L A e)
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
                (fun _ j => (j : ℕ))) L A +
          (2 ^ 6 * Wc + εwrap L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ))) L A +
          remainder (Params.ofDecay a) cwrap L A)
    (envelopeL : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) L A ≤
        (2 ^ 6 * Jc + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
            (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A +
          remainder (Params.ofDecay a) cenv L A)
    (envelopeR : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) L A ≤
        (2 ^ 6 * Jc + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
            (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A +
          remainder (Params.ofDecay a) cenv L A)
    (firstStage : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))))
      fun L A =>
        (1 - Lc - εfirst L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A -
          remainder (Params.ofDecay a) cfirst L A ≤ energyFirst lam (atomLift m₀
              (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A)
    (joint : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
          (j : ℕ))) L A - energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
          (fun _ j => (j : ℕ))) L A) -
          (energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) ML L A + energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ))) MR L A) / 2 ≤
        (2 ^ 6 * Hc - 1 + εjoint L) *
            energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp)
                (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ))) L A + remainder (Params.ofDecay a) cjoint L A) :
    PowerSavingBound (Params.ofDecay a) :=
  Sarkozy.Param.paperMain_powerSavingBound_concrete_ref_theta m₀ (J := fun L => ↥(tailPrimes P4 L))
    (fun _ j =>
        (j : ℕ)) pr h hcop hP (fun L j => tailPrimes_prime P4 L j.1 j.2) (fun _ =>
        Subtype.val_injective)
    μ₀ μp hm₀ hp₀ hmp hpp hunit hθ μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr
    εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint
    hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint

/-- The concrete main theorem for the paper's tail family with the primitive ledger, free price
exponent (`Sarkozy.PaperFrame.paperMain_powerSavingBound_canonical` in general). -/
theorem paperMain_powerSavingBound_canonical {a : ℝ} (hP : (Params.ofDecay a).Valid)
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
    (lam ML ν MR : ∀ L b, ((Slot → AtomLabel m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
        (j : ℕ)) L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (εwrap εenv εfirst εjoint : ℕ → ℝ) (cwrap cenv cfirst cjoint : ℝ)
    (hεwrap : Tendsto εwrap atTop (𝓝 0)) (hεenv : Tendsto εenv atTop (𝓝 0))
    (hεfirst : Tendsto εfirst atTop (𝓝 0)) (hεjoint : Tendsto εjoint atTop (𝓝 0))
    (hcwrap : 0 ≤ cwrap) (hcenv : 0 ≤ cenv) (hcfirst : 0 ≤ cfirst) (hcjoint : 0 ≤ cjoint)
    (wrap : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
          (j : ℕ))) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ)) pr h hcop L A e)
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
                (fun _ j => (j : ℕ))) L A +
          (2 ^ 6 * l.W + εwrap L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ))) L A +
          remainder (Params.ofDecay a) cwrap L A)
    (envelopeL : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) L A ≤
        (2 ^ 6 * l.J + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
            (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A +
          remainder (Params.ofDecay a) cenv L A)
    (envelopeR : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) L A ≤
        (2 ^ 6 * l.J + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
            (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A +
          remainder (Params.ofDecay a) cenv L A)
    (firstStage : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))))
      fun L A =>
        (1 - l.L₀ - εfirst L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
            (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A -
          remainder (Params.ofDecay a) cfirst L A ≤ energyFirst lam (atomLift m₀
              (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A)
    (joint : AtCounterexamples (Params.ofDecay a) (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
          (j : ℕ))) L A - energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
          (fun _ j => (j : ℕ))) L A) -
          (energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) ML L A + energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ))) MR L A) / 2 ≤
        (2 ^ 6 * l.jointConstant - 1 + εjoint L) *
            energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp)
                (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ))) L A + remainder (Params.ofDecay a) cjoint L A) :
    PowerSavingBound (Params.ofDecay a) :=
  paperMain_powerSavingBound_canonical_theta m₀ P4 pr h hcop hP μ₀ μp hm₀ hp₀ hmp hpp hunit
    (l.jointTheta_lt_one hledger) μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr
    εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint
    hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint

/-- **The concrete main theorem at the formal exponent** `ε′ = Target.epsAnchor = a₀/(72 − ϑ)`
(`thm:main` via `thm:density:induction` at `a = a₀`): the hypotheses of
`paperMain_powerSavingBound_canonical_theta` at the anchor exponents `Params.anchor`, with the
closing number `jointTheta 6 Lc Jc Wc Hc < 1` as a hypothesis, give
`Target.SarkozyBound Param.anchorSaving`. The closing data at `a₀` (`Lc, Jc, Wc, Hc`, and with them
the four closing inequalities) are hypotheses; the paper's ledger `tab:four-routes-ledger` was
computed at the record `a`. -/
theorem sarkozyBound_epsAnchor_canonical
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {Lc Jc Wc Hc : ℝ} (hθ : jointTheta 6 Lc Jc Wc Hc < 1)
    (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (hμ : ∀ e q r, 0 ≤ μ e q r)
    (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (lam ML ν MR : ∀ L b, ((Slot → AtomLabel m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
        (j : ℕ)) L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (εwrap εenv εfirst εjoint : ℕ → ℝ) (cwrap cenv cfirst cjoint : ℝ)
    (hεwrap : Tendsto εwrap atTop (𝓝 0)) (hεenv : Tendsto εenv atTop (𝓝 0))
    (hεfirst : Tendsto εfirst atTop (𝓝 0)) (hεjoint : Tendsto εjoint atTop (𝓝 0))
    (hcwrap : 0 ≤ cwrap) (hcenv : 0 ≤ cenv) (hcfirst : 0 ≤ cfirst) (hcjoint : 0 ≤ cjoint)
    (wrap : AtCounterexamples Params.anchor (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      2 ^ 6 * energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
          (j : ℕ))) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ)) pr h hcop L A e)
            (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
                (fun _ j => (j : ℕ))) L A +
          (2 ^ 6 * Wc + εwrap L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ))) L A +
          remainder Params.anchor cwrap L A)
    (envelopeL : AtCounterexamples Params.anchor (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) L A ≤
        (2 ^ 6 * Jc + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
            (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A +
          remainder Params.anchor cenv L A)
    (envelopeR : AtCounterexamples Params.anchor (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
          (fun L A e => atomInput m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ)) pr h hcop L A e) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) L A ≤
        (2 ^ 6 * Jc + εenv L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L))
            (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A +
          remainder Params.anchor cenv L A)
    (firstStage : AtCounterexamples Params.anchor (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))))
      fun L A =>
        (1 - Lc - εfirst L) * energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ)) μ₀ μp) (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
            (j : ℕ))) L A -
          remainder Params.anchor cfirst L A ≤ energyFirst lam (atomLift m₀
              (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ))) L A)
    (joint : AtCounterexamples Params.anchor (energyFirst (refLaws m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp) (atomLift m₀
        (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)))) fun L A =>
      (2 ^ 6 - 1) * (energyFirst lam (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
          (j : ℕ))) L A - energyComparison ν (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
          (fun _ j => (j : ℕ))) L A) -
          (energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
              (j : ℕ))) ML L A + energyMean (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L))
              (fun _ j => (j : ℕ))) MR L A) / 2 ≤
        (2 ^ 6 * Hc - 1 + εjoint L) *
            energyFirst (refLaws m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j => (j : ℕ)) μ₀ μp)
                (atomLift m₀ (J := fun L => ↥(tailPrimes P4 L)) (fun _ j =>
                (j : ℕ))) L A + remainder Params.anchor cjoint L A) :
    Target.SarkozyBound Param.anchorSaving :=
  anchor_powerSavingBound_iff.mp (paperMain_powerSavingBound_canonical_theta m₀ P4 pr h hcop
    Params.anchor_valid μ₀ μp hm₀ hp₀ hmp hpp hunit hθ μ hμ hμ1 t hnorm u w hu hw lam ML ν MR hbr
    εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint
    hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint)

/-- **Compatibility**: the hard-coded `Sarkozy.PaperFrame.paperMain_powerSavingBound_canonical`
(same statement, by `type_of%`) is the parametrized chain at the record exponent. -/
theorem paperMain_powerSavingBound_canonical_viaParam :
    type_of% @Sarkozy.PaperFrame.paperMain_powerSavingBound_canonical := by
  intro J₀ _ _ m₀ _ P4 P _ _ pr h _ hcop E _ _ μ₀ μp hm₀ hp₀ hmp hpp hunit l hledger μ hμ hμ1 t
    hnorm u w hu hw lam ML ν MR hbr εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap
    hεenv hεfirst hεjoint hcwrap hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint
  have h' := paperMain_powerSavingBound_canonical (a := Sarkozy.decay) m₀ P4 pr h hcop
    Params.paper_valid μ₀ μp hm₀ hp₀ hmp hpp hunit hledger μ hμ hμ1 t hnorm u w hu hw lam ML ν MR
    hbr εwrap εenv εfirst εjoint cwrap cenv cfirst cjoint hεwrap hεenv hεfirst hεjoint hcwrap
    hcenv hcfirst hcjoint wrap envelopeL envelopeR firstStage joint
  unfold PowerSavingBound Sarkozy.PowerSavingBound at *
  rwa [Params.ofDecay_saving, ← Sarkozy.saving_eq] at h'

end Canonical

end Sarkozy.Param
