module

public import Sarkozy.BracketEnergy.EnvFirst
public import Sarkozy.DensityFibre.FoldedChoice

@[expose] public section

/-!
# The folded energies of the baseline route are structured energies

The baseline proof of `lem:sharp-first` (`DensityFibre.FoldedChoice`, `FoldedFields`) applies
`prop:record:density-structured` "once to each folded energy". This file makes that step
available formally, for the revealed inputs of `envC` and `fixC`.

* `foldedPlus_eq_crt`, `foldedMinus_eq_crt`: a folded energy on the block labels, with inputs
  `G ∘ crt⁻¹`, is the multilinear energy on the cyclic coordinates of the crt-pulled folded laws
  with the **folded inputs** `v ↦ G(φ_±(v))`.
* `block_energy_le_structured_data`: B9's revealed-input chain on the block atoms
  (`data_block_energy_le_structured`) for **arbitrary slot data**.
* **`env_fold_le_chain`**, **`fix_fold_le_chain`**: for any fold map `φ : Slot → Slot`, the energy
  with the folded pair inputs of `envC` (resp. `fixC`) is bounded by the chain. The slot data are
  `envSlots ∘ φ` (resp. `fixSlots ∘ φ`), and the chain's per-term inputs (`hrest`, `hdc`,
  `hun`, `hatom`, the modulus conditions) are at the folded data.

With `φ = φ_±` of the cut `c_j`, these bound the folded energies `𝔈_±(φ)` in the hypothesis
`hfold` of `FoldedFields`. It remains to match the chain's main price with `(∏ g) M_±` (B9's
`termPrice_le` / `envMainPrice_eq` pattern at the folded data) and to average over the residues.

At `ϑ = 1` the moment input `hatom` (unit mixed `L^{72}`) follows from uniform one-slot
marginals (`mixedLpBound_of_uniform_marginals`). The folded laws (diagonal laws of half marginals
of positive records with uniform marginals) have them.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.Structured Sarkozy.Functional
  Sarkozy.FourierArithmetic Sarkozy.PaperFrame Sarkozy.BlockFrame Sarkozy.IndexSupport
  Sarkozy.TheoremC

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Transport

variable (blk)

omit [DecidableEq P] in
/-- A plus folded energy on the block labels with inputs `G ∘ crt⁻¹` is the energy of the
crt-pulled folded laws with the folded inputs `G ∘ φ₊`. -/
theorem foldedPlus_eq_crt {L : ℕ} (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (c : ReflectionCut Slot) {I : BlockAtom Bk J L → Type} [∀ b, Fintype (I b)]
    (Lp : ∀ b, I b → TheoremCBlock.AtomMeasure m₀ blk p L b)
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) (φ : ∀ b, I b) :
    foldedPlus c Lp (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ =
      multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b => Lp b (φ b)))
        (fun v => G (c.foldPlus v)) := by
  unfold foldedPlus
  rw [multilinearIntegral_crt blk h0 L]
  congr 1
  funext v y
  simp only [Function.comp, Equiv.symm_apply_apply]

omit [DecidableEq P] in
/-- The same for a minus folded energy. -/
theorem foldedMinus_eq_crt {L : ℕ} (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (c : ReflectionCut Slot) {I : BlockAtom Bk J L → Type} [∀ b, Fintype (I b)]
    (Lm : ∀ b, I b → TheoremCBlock.AtomMeasure m₀ blk p L b)
    (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ) (φ : ∀ b, I b) :
    foldedMinus c Lm (fun v x => G v ((crtLabelEquiv blk h0 L).symm x)) φ =
      multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b => Lm b (φ b)))
        (fun v => G (c.foldMinus v)) := by
  unfold foldedMinus
  rw [multilinearIntegral_crt blk h0 L]
  congr 1
  funext v y
  simp only [Function.comp, Equiv.symm_apply_apply]

end Transport

omit [DecidableEq P] in
/-- **The revealed-input chain on the block atoms for arbitrary slot data**
(`prop:record:density-structured` with structured slot data, `lem:record:density-dc`): B9's
`data_block_energy_le_structured` with any slot data `dat : Slot → SlotDatum` in place of the
pair data `slotDatum u qdat`, e.g. the pair data composed with a fold. The proof is B9's, through
`abs_tensor_energy_le_structured`. -/
theorem block_energy_le_structured_data (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk J L)) (hE : ∀ b ∉ Es, Λ b = D.R.law p L b)
    {qE cE : ℕ} (hDE : ∏ b ∈ Es, crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Q : ℝ) (dat : Slot → SlotDatum)
    (hD0 : ∀ v, 1 ≤ (dat v).1)
    (hD0M : ∀ v, (dat v).1 ∣ M0)
    (hcop0 : ∀ v k, ((dat v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ v, (dat v).2.2.1 = blockScale * L ∨
      (dat v).2.2.1 = L)
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬((dat v).1 *
      ∏ j ∈ Es, crtModuli m₀ blk p L j = 1 ∧
      (dat v).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) Es A (fun v => (dat v).1)
        (fun v => (dat v).2.2.1)
        (fun v => (dat v).2.2.2)
        (fun v => (dat v).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) Es
        (dat v).1 (dat v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) Es (Q' v) B (blockScale * stepEll (crtModuli m₀ blk p L)
            Es (dat v).1
            (dat v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) Es (dat v).1
          (dat v).2.2.1) B)
    (hdc : |structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (paperInputs (crtModuli m₀ blk p L) Es Q A
            (fun v => (dat v).1)
            (fun v => (dat v).2.2.1)
            (fun _ v => (dat v).2.2.2)
            (fun _ v => (dat v).2.1)) -
        structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (fun _ => revealedModel (crtModuli m₀ blk p L) Es A
            (fun v => (dat v).1)
            (fun v => (dat v).2.2.1)
            (fun v => (dat v).2.2.2)
            (fun v => (dat v).2.1) Q')| ≤
      Cdc * totalVariation (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ)) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ Es, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (fun v => paperForm (crtModuli m₀ blk p L) Q A (dat v))| ≤
      (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk p L) Es
              (fun v => (dat v).1)
              (fun v => (dat v).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (dat v).1)
              (fun v => (dat v).2.2.1)
              (fun _ v => (dat v).2.2.2)
              (fun _ v => (dat v).2.1))
            changed a' θ (density (blockScale * L) A) * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have h0 := prefix_pairwise hpair
  have hR3 := crtRef_squareAffineInvariant blk p h0 D.R.μ₀ D.R.μp L D.R.inv₀ D.R.invp
  have hEc : ∀ b ∉ Es, crtLaws blk h0 L Λ b =
      signedIntegral (crtRef blk p h0 D.R.μ₀ D.R.μp L b).weight := by
    intro b hb
    rw [← crtLaws_blockRefLaws blk p h0 D.R.μ₀ D.R.μp L b]
    unfold crtLaws
    rw [hE b hb]
  have hμ := crtRef_slotReflectionPositive blk p h0 D.R.μ₀ D.R.μp L
    (fun β => (D.R.rp₀ β).slot) (fun j => (D.R.rpp (p L j) (D.S.p_prime L j)).slot)
  have hres := abs_tensor_energy_le_structured (crtModuli m₀ blk p L)
    (crtModuli_pairwise blk hpair) hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    (crtRef blk p h0 D.R.μ₀ D.R.μp L) hμ hR3 (crtLaws blk h0 L Λ) Es hEc hDE hqE hcE hcE0 hcQ
    hcopE hqN _ hD0 hD0M hcop0 _ hM _ _ changed hchg Q Q' hun hrest hdc
    (fun b hb => mixedLpBound_variationLaw_pull (crtAtomEquiv blk h0 L b.1) (Λ b.1)
      (hatom b.1 b.2) hb)
  have hprod : (∏ b : {b // b ∈ Es}, ∑ y : Slot → ZMod (crtModuli m₀ blk p L b.1),
      |lawDensity (crtLaws blk h0 L Λ b.1) y|) =
      ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x| :=
    prod_congr rfl fun b _ => sum_abs_lawDensity_pullLaw _ _
  rw [hprod] at hres
  exact hres

section Chain

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **A folded `envC` energy is bounded by the revealed-input chain**: for any fold map `fo`, the
energy of a block-atom law (equal to `μ` off `Es`) with the folded pair inputs of `envC` at a
depth vector revealing the intervals is at most the chain's bound at the slot data
`envSlots ∘ fo` (`prop:record:density-structured` applied to a folded energy). -/
theorem env_fold_le_chain (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk J L)) (hE : ∀ b ∉ Es, Λ b = D.R.law p L b)
    {qE cE : ℕ} (hDE : ∏ b ∈ Es, crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (hJ : ∀ e, (Jq e none : ℕ) ≠ 0) (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j)
    (u : E → reservedCut.Half) (fo : Slot → Slot)
    (hD0 : ∀ v, 1 ≤ (envSlots hcop u L Jq ω (fo v)).1)
    (hD0M : ∀ v, (envSlots hcop u L Jq ω (fo v)).1 ∣ M0)
    (hcop0 : ∀ v k, ((envSlots hcop u L Jq ω (fo v)).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ v, (envSlots hcop u L Jq ω (fo v)).2.2.1 = blockScale * L ∨
      (envSlots hcop u L Jq ω (fo v)).2.2.1 = L)
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬((envSlots hcop u L Jq ω (fo v)).1 *
      ∏ j ∈ Es, crtModuli m₀ blk p L j = 1 ∧
      (envSlots hcop u L Jq ω (fo v)).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) Es A (fun v => (envSlots hcop u L Jq ω (fo v)).1)
        (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
        (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
        (fun v => (envSlots hcop u L Jq ω (fo v)).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) Es
        (envSlots hcop u L Jq ω (fo v)).1 (envSlots hcop u L Jq ω (fo v)).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) Es (Q' v) B (blockScale * stepEll (crtModuli m₀ blk p L)
            Es (envSlots hcop u L Jq ω (fo v)).1
            (envSlots hcop u L Jq ω (fo v)).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) Es (envSlots hcop u L Jq ω (fo v)).1
          (envSlots hcop u L Jq ω (fo v)).2.2.1) B)
    (hdc : |structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (paperInputs (crtModuli m₀ blk p L) Es (paperCutoff (blockScale * L)) A
            (fun v => (envSlots hcop u L Jq ω (fo v)).1)
            (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
            (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
            (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.1)) -
        structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (fun _ => revealedModel (crtModuli m₀ blk p L) Es A
            (fun v => (envSlots hcop u L Jq ω (fo v)).1)
            (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
            (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
            (fun v => (envSlots hcop u L Jq ω (fo v)).2.1) Q')| ≤
      Cdc * totalVariation (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ)) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ Es, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (fun v => pairInputs u u (revealedInputCRT blk hcop D L A Jq)
          (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω (fo v))| ≤
      (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk p L) Es
              (fun v => (envSlots hcop u L Jq ω (fo v)).1)
              (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (envSlots hcop u L Jq ω (fo v)).1)
              (fun v => (envSlots hcop u L Jq ω (fo v)).2.2.1)
              (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.2.2)
              (fun _ v => (envSlots hcop u L Jq ω (fo v)).2.1))
            changed a' θ (density (blockScale * L) A) * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hG : pairInputs u u (revealedInputCRT blk hcop D L A Jq) (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω =
      fun v => paperForm (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A
        (envSlots hcop u L Jq ω v) :=
    pairInputs_eq_slotDatum (crtModuli m₀ blk p L) u (revealedInputCRT blk hcop D L A Jq)
      (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω
      (paperCutoff (blockScale * L)) A (fun e => envDatum hcop L Jq e (ω e)) (wholeDatum L)
      (fun e => revealedInputCRT_eq_paperForm hcop D L A Jq e (ω e) (hJ e))
      (unchangedInput_eq_paperForm _ _ _ _)
  rw [hG]
  exact block_energy_le_structured_data D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Λ Es hE hDE hqE
    hcE hcE0 hcQ hcopE hqN (paperCutoff (blockScale * L)) (fun v => envSlots hcop u L Jq ω (fo v))
    hD0 hD0M hcop0 hM changed hchg Q' hun hrest hdc hatom

/-- **A folded `fixC` energy is bounded by the revealed-input chain** (fixed intervals on `𝒮`,
interval `t`, slot data `fixSlots ∘ fo`). -/
theorem fix_fold_le_chain (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {Yf : ℕ → Finset ℤ → ℝ} {a' θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a' θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1)
    (ha : 0 ≤ a') (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Es : Finset (BlockAtom Bk J L)) (hE : ∀ b ∉ Es, Λ b = D.R.law p L b)
    {qE cE : ℕ} (hDE : ∏ b ∈ Es, crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) (u : E → reservedCut.Half)
    (fo : Slot → Slot)
    (hD0 : ∀ v, 1 ≤ (fixSlots hcop u L S t Jq ω (fo v)).1)
    (hD0M : ∀ v, (fixSlots hcop u L S t Jq ω (fo v)).1 ∣ M0)
    (hcop0 : ∀ v k, ((fixSlots hcop u L S t Jq ω (fo v)).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ v, (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 = blockScale * L ∨
      (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 = L)
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬((fixSlots hcop u L S t Jq ω (fo v)).1 *
      ∏ j ∈ Es, crtModuli m₀ blk p L j = 1 ∧
      (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) Es A (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
        (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
        (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
        (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) Es
        (fixSlots hcop u L S t Jq ω (fo v)).1 (fixSlots hcop u L S t Jq ω (fo v)).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) Es (Q' v) B (blockScale * stepEll (crtModuli m₀ blk p L)
            Es (fixSlots hcop u L S t Jq ω (fo v)).1
            (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) Es (fixSlots hcop u L S t Jq ω (fo v)).1
          (fixSlots hcop u L S t Jq ω (fo v)).2.2.1) B)
    (hdc : |structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (paperInputs (crtModuli m₀ blk p L) Es (paperCutoff (blockScale * L)) A
            (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
            (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
            (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
            (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.1)) -
        structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (fun _ => revealedModel (crtModuli m₀ blk p L) Es A
            (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
            (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
            (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
            (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.1) Q')| ≤
      Cdc * totalVariation (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ)) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ Es, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (fun v => pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω (fo v))| ≤
      (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk p L) Es
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).1)
              (fun v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.1)
              (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.2.2)
              (fun _ v => (fixSlots hcop u L S t Jq ω (fo v)).2.1))
            changed a' θ (density (blockScale * L) A) * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hG : pairInputs u u (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω =
      fun v => paperForm (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A
        (fixSlots hcop u L S t Jq ω v) :=
    pairInputs_eq_slotDatum (crtModuli m₀ blk p L) u
      (revealedSlot Jq (wrapInputCRT blk hcop L A S t))
      (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω
      (paperCutoff (blockScale * L)) A (fun e => fixDatum hcop L S t Jq e (ω e)) (wholeDatum L)
      (fun e => revealedSlot_wrapInputCRT_eq_paperForm hcop L A S t Jq e (ω e))
      (unchangedInput_eq_paperForm _ _ _ _)
  rw [hG]
  exact block_energy_le_structured_data D hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 Λ Es hE hDE hqE
    hcE hcE0 hcQ hcopE hqN (paperCutoff (blockScale * L))
    (fun v => fixSlots hcop u L S t Jq ω (fo v))
    hD0 hD0M hcop0 hM changed hchg Q' hun hrest hdc hatom

end Chain

/-! ## The main prices of the two folded energies (`lem:record:folded-energy`(e)) -/

section Prices

/-- **Copying for the main prices** (`lem:record:folded-energy`(e)): the main prices of the slot
data copied by the two folds multiply to the square of the main price of the original data,
`Π(𝔈₊) Π(𝔈₋) = Π²`. Here all slots are changed, as for the folded energies of a term with
`D_E ≠ 1`. -/
theorem mainPrice_fold_mul (c : ReflectionCut Slot) (ξ αbar : Slot → ℝ) (a θ α : ℝ) :
    mainPrice (fun v => ξ (c.foldPlus v)) (fun v => αbar (c.foldPlus v)) (fun _ => True) a θ α *
      mainPrice (fun v => ξ (c.foldMinus v)) (fun v => αbar (c.foldMinus v)) (fun _ => True)
        a θ α =
      mainPrice ξ αbar (fun _ => True) a θ α ^ 2 := by
  unfold mainPrice
  simp only [Finset.filter_true]
  have h1 := ReflectionCut.prod_folds c (fun v => ξ v ^ (a / 72))
  have h2 := ReflectionCut.prod_folds c (fun v => (αbar v / α) ^ (θ / 72))
  calc ((∏ v, ξ (c.foldPlus v) ^ (a / 72)) * ∏ v, (αbar (c.foldPlus v) / α) ^ (θ / 72)) *
        ((∏ v, ξ (c.foldMinus v) ^ (a / 72)) * ∏ v, (αbar (c.foldMinus v) / α) ^ (θ / 72))
      = ((∏ v, ξ (c.foldPlus v) ^ (a / 72)) * ∏ v, ξ (c.foldMinus v) ^ (a / 72)) *
        ((∏ v, (αbar (c.foldPlus v) / α) ^ (θ / 72)) *
          ∏ v, (αbar (c.foldMinus v) / α) ^ (θ / 72)) := by ring
    _ = _ := by rw [h1, h2]; ring

/-- **The AM–GM condition of `hfold` with the geometric-mean price**: if `M₊ M₋ = M²` with
`M₊, M₋ > 0` and `M ≥ 0`, then `t = √(M₋/M₊)` gives `t M₊ + M₋/t = 2M`. -/
theorem fold_ratio_eq {Mp Mm M : ℝ} (hp : 0 < Mp) (hm : 0 < Mm) (hM : 0 ≤ M)
    (hprod : Mp * Mm = M ^ 2) :
    0 < Real.sqrt (Mm / Mp) ∧ Real.sqrt (Mm / Mp) * Mp + Mm / Real.sqrt (Mm / Mp) = 2 * M := by
  have hq : 0 < Mm / Mp := div_pos hm hp
  have ht := Real.sqrt_pos.mpr hq
  refine ⟨ht, ?_⟩
  have hsq := Real.sq_sqrt hq.le
  have hMval : M = Real.sqrt (Mm / Mp) * Mp := by
    have h1 : (Real.sqrt (Mm / Mp) * Mp) ^ 2 = M ^ 2 := by
      rw [mul_pow, hsq, ← hprod]
      field_simp
    have h2 : 0 ≤ Real.sqrt (Mm / Mp) * Mp := mul_nonneg ht.le hp.le
    nlinarith [sq_nonneg (Real.sqrt (Mm / Mp) * Mp - M), sq_nonneg (Real.sqrt (Mm / Mp) * Mp + M)]
  have h3 : Mm / Real.sqrt (Mm / Mp) = Real.sqrt (Mm / Mp) * Mp := by
    field_simp
    rw [hsq]
    field_simp
  rw [h3, ← hMval]
  ring

end Prices

end Sarkozy.DensityFibre
