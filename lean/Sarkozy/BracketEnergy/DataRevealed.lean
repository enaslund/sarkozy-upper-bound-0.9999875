module

public import Sarkozy.BracketEnergy.PairSlots
public import Sarkozy.EnvelopeEnergiesPaper.DataChain

@[expose] public section

/-!
# The first bound of `lem:bracket-energy` for the energies of `envC`, `fixC`

* `data_block_energy_le_structured`: the revealed-input chain (`abs_pair_energy_le_structured`)
  on the block atoms of comparison data `D`, by B5's CRT transport, with (R2), (R3) from the
  data's reference (the structured-slot form of B5's `data_block_energy_le_unchanged`).
* `envDatum`, `revealedInputCRT_eq_paperForm`: the revealed input of `envC` at a depth vector that
  reveals the interval is `g^{I_b, D_𝒥, s mod D_𝒥}`;
* **`env_first_le_chain`**: the energy of `hfirstL` (`EnvelopeBracketInputs`, source side) at a
  depth vector that reveals every interval, a term `(f, g)` and an index `ω`, is bounded by the
  chain, given the chain's per-term inputs (modulus conditions on `D_{f ∪ g}`, `hrest`, `hdc`,
  the moments `hatom` of the selected envelope increments `Q_𝔟` and reserved records
  `Ñ_{0,𝔟} − μ_𝔟`);
* `fixDatum`, `revealedSlot_wrapInputCRT_eq_paperForm`, **`fix_first_le_chain`**: the same for
  `hfirstL` of `FixedBracketInputs`, at every depth vector.

The interval coordinate of the index of `envC` is revealed with probability one (its tail is
`Tails.bernoulli 1`), so depth vectors that do not reveal it carry weight `0` in the remainder
summation `hrem`, and their first bound is free (signed remainders).
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

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

omit [DecidableEq P] in
/-- **The revealed-input chain on the block atoms of comparison data**
(`prop:record:density-structured` with structured slot data at `ϑ`, `lem:record:density-dc`;
the structured-slot form of `data_block_energy_le_unchanged`): for a block-atom law `⊗_𝔟 Λ_𝔟`
equal to `μ_𝔟` off `Es` and pair inputs whose query inputs are `g^{I_e, D_e, s_e}`, the energy on
the cyclic coordinates is at most `∏_{Es} ‖Λ_𝔟‖ [(1 + u_L) Π_main Y + C_dc L^{-σ} α]`. -/
theorem data_block_energy_le_structured (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
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
    {Ωi : Type} (u : E → reservedCut.Half)
    (φ : E → Ωi → ResidueSpace (crtModuli m₀ blk p L) → ℝ) (ω : E → Ωi) (Q : ℝ)
    (qdat : E → SlotDatum)
    (hφ : ∀ e, φ e (ω e) = paperForm (crtModuli m₀ blk p L) Q A (qdat e))
    (hD0 : ∀ v, 1 ≤ (slotDatum u qdat (wholeDatum L) v).1)
    (hD0M : ∀ v, (slotDatum u qdat (wholeDatum L) v).1 ∣ M0)
    (hcop0 : ∀ v k, ((slotDatum u qdat (wholeDatum L) v).1).Coprime (crtModuli m₀ blk p L k))
    (hM : ∀ v, (slotDatum u qdat (wholeDatum L) v).2.2.1 = blockScale * L ∨
      (slotDatum u qdat (wholeDatum L) v).2.2.1 = L)
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬((slotDatum u qdat (wholeDatum L) v).1 *
      ∏ j ∈ Es, crtModuli m₀ blk p L j = 1 ∧
      (slotDatum u qdat (wholeDatum L) v).2.2.1 = blockScale * L))
    (Q' : Slot → ℝ)
    (hun : ∀ v, ¬changed v → ∀ x, referenceEnergy
      (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
      (revealedModel (crtModuli m₀ blk p L) Es A (fun v => (slotDatum u qdat (wholeDatum L) v).1)
        (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
        (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
        (fun v => (slotDatum u qdat (wholeDatum L) v).2.1) Q' v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) Es
        (slotDatum u qdat (wholeDatum L) v).1 (slotDatum u qdat (wholeDatum L) v).2.2.1 : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (child (crtModuli m₀ blk p L) Es (Q' v) B (blockScale * stepEll (crtModuli m₀ blk p L)
            Es (slotDatum u qdat (wholeDatum L) v).1
            (slotDatum u qdat (wholeDatum L) v).2.2.1)) ≤
        Yf (stepEll (crtModuli m₀ blk p L) Es (slotDatum u qdat (wholeDatum L) v).1
          (slotDatum u qdat (wholeDatum L) v).2.2.1) B)
    (hdc : |structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (paperInputs (crtModuli m₀ blk p L) Es Q A
            (fun v => (slotDatum u qdat (wholeDatum L) v).1)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
            (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
            (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.1)) -
        structuredEnergy
          (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) D.R.μ₀ D.R.μp L))
          (FiniteLaw.uniform Unit)
          (liftWeight Es (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) Es))
          (fun _ => revealedModel (crtModuli m₀ blk p L) Es A
            (fun v => (slotDatum u qdat (wholeDatum L) v).1)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
            (fun v => (slotDatum u qdat (wholeDatum L) v).2.1) Q')| ≤
      Cdc * totalVariation (selectedWeight Es (crtLaws blk (prefix_pairwise hpair) L Λ)) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ Es, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (pairInputs u u φ φ (unchangedInput (crtModuli m₀ blk p L) Q A L) ω ω)| ≤
      (∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (crtModuli m₀ blk p L) Es
              (fun v => (slotDatum u qdat (wholeDatum L) v).1)
              (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A
              (fun v => (slotDatum u qdat (wholeDatum L) v).1)
              (fun v => (slotDatum u qdat (wholeDatum L) v).2.2.1)
              (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.2.2)
              (fun _ v => (slotDatum u qdat (wholeDatum L) v).2.1))
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
  have hres := abs_pair_energy_le_structured (crtModuli m₀ blk p L)
    (crtModuli_pairwise blk hpair) hcex hθ hθ2 ha hC0 hL hY0 hsc hM0
    (crtRef blk p h0 D.R.μ₀ D.R.μp L) hμ hR3 (crtLaws blk h0 L Λ) Es hEc hDE hqE hcE hcE0 hcQ
    hcopE hqN u φ ω Q qdat hφ hD0 hD0M hcop0 hM changed hchg Q' hun hrest hdc
    (fun b hb => mixedLpBound_variationLaw_pull (crtAtomEquiv blk h0 L b.1) (Λ b.1)
      (hatom b.1 b.2) hb)
  have hprod : (∏ b : {b // b ∈ Es}, ∑ y : Slot → ZMod (crtModuli m₀ blk p L b.1),
      |lawDensity (crtLaws blk h0 L Λ b.1) y|) =
      ∏ b : {b // b ∈ Es}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x| :=
    prod_congr rfl fun b _ => sum_abs_lawDensity_pullLaw _ _
  rw [hprod] at hres
  exact hres

end Sarkozy.BracketEnergy
