module

public import Sarkozy.EnvelopeEnergiesPaper.BlockReference
public import Sarkozy.EnvelopeInputs.FoldedEnvelope

@[expose] public section






open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.PaperFrame Sarkozy.BlockFrame
  Sarkozy.Structured

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The density-structured chain at `θ = ϑ` on the paper's block atoms** (G1's gap 2;
`prop:record:density-structured` for an energy that is `μ` off a selected set `E`, with
`lem:record:density-dc`; I1's `abs_tensor_energy_le_unchanged_atoms` transported by the CRT).
For every block-atom law `⊗_b Λ_b` with `Λ_b = μ_b` off `E` (joint block laws allowed),
`|Y_{⊗_b Λ_b}(F_A)| ≤ ∏_{b ∈ E} ‖Λ_b‖ [(1 + u_L) R_E^a Y + C_dc L^{-σ} α]`, where
`R_E = sq(∏_{b ∈ E} crtModuli_b)`, from (R2), (R3) of the block laws, the moment inputs of the
selected block laws on their own alphabets, and the per-term inputs `hrest`, `hdc` in cyclic
coordinates. -/
theorem abs_block_energy_le_unchanged {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ}
    {A : Finset ℤ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (rp₀ : ∀ β, SlotReflectionPositive (signedIntegral (μ₀ β).weight))
    (rpp : ∀ j, SlotReflectionPositive (signedIntegral (μp (p L j)).weight))
    (inv₀ : ∀ β (a : ∀ i, (ZMod (blockModuli m₀ blk β i))ˣ) (b : BlockRes m₀ blk β),
      (∀ i, IsSquare ((a i : ZMod (blockModuli m₀ blk β i)))) →
        ∀ F : (Slot → BlockRes m₀ blk β) → ℝ,
          (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli m₀ blk β) a b (z v))) =
            (μ₀ β).expect F)
    (invp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
      ∀ F : (Slot → ZMod q) → ℝ,
        (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (E : Finset (BlockAtom Bk J L)) (hE : ∀ b ∉ E, Λ b = blockRefLaws m₀ blk p μ₀ μp L b)
    {qE cE : ℕ} (hDE : ∏ b ∈ E, crtModuli m₀ blk p L b = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (hne : ∏ b ∈ E, crtModuli m₀ blk p L b ≠ 1)
    {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (Q' : Slot → ℝ) {Cdc σ : ℝ}
    (hrest : ∀ (v : Slot) (B : Finset ℤ),
      B ⊆ Icc 1 ((blockScale * stepEll (crtModuli m₀ blk p L) E 1 (blockScale * L) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) μ₀ μp L))
          (child (crtModuli m₀ blk p L) E (Q' v) B
            (blockScale * stepEll (crtModuli m₀ blk p L) E 1 (blockScale * L))) ≤
        Yf (stepEll (crtModuli m₀ blk p L) E 1 (blockScale * L)) B)
    (hdc : |structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) μ₀ μp L)) P
          (liftWeight E (selectedWeight E (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) E))
          (paperInputs (crtModuli m₀ blk p L) E (paperCutoff (blockScale * L)) A (fun _ => 1)
            (fun _ => blockScale * L) (fun _ _ => 0) (fun _ _ => 0)) -
        structuredEnergy (FiniteLaw.tensor (crtRef blk p (prefix_pairwise hpair) μ₀ μp L)) P
          (liftWeight E (selectedWeight E (crtLaws blk (prefix_pairwise hpair) L Λ))
            (uniformRest (Xa := fun b => ZMod (crtModuli m₀ blk p L b)) E))
          (unchangedModel (crtModuli m₀ blk p L) E A L Q')| ≤
      Cdc * totalVariation (selectedWeight E (crtLaws blk (prefix_pairwise hpair) L Λ)) *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    (hatom : ∀ b ∈ E, ∀ hb : 0 < totalVariation (lawDensity (Λ b)),
      MixedLpBound (variationLaw _ hb) (72 / θ) 1) :
    |diagonalIntegral (tensorLaw Λ) (blockLift m₀ blk p L A)| ≤
      (∏ b : {b // b ∈ E}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x|) *
        ((1 + scaleU blockScale M0 Qcl stageTau L) *
            ((stepR (crtModuli m₀ blk p L) E 1 : ℕ) : ℝ) ^ a * Yf L A +
          Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have h0 := prefix_pairwise hpair
  rw [diagonalIntegral_blockLift_eq_crt blk L hpair A Λ]
  have hR3 := crtRef_squareAffineInvariant blk p h0 μ₀ μp L inv₀ invp
  have hEc : ∀ b ∉ E, crtLaws blk h0 L Λ b = signedIntegral (crtRef blk p h0 μ₀ μp L b).weight := by
    intro b hb
    rw [← crtLaws_blockRefLaws blk p h0 μ₀ μp L b]
    unfold crtLaws
    rw [hE b hb]
  have h := EnvelopeInputs.abs_tensor_energy_le_unchanged_atoms (crtModuli m₀ blk p L)
    (crtModuli_pairwise blk hpair) hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 (crtRef blk p h0 μ₀ μp L)
    (crtRef_slotReflectionPositive blk p h0 μ₀ μp L rp₀ rpp) (crtLaws blk h0 L Λ) E hEc
    hDE hqE hcE hcE0 hcQ hcopE hqN hne P (paperCutoff (blockScale * L)) Q' hrest
    (fun j F => tensor_expect_stepMapOff (crtModuli m₀ blk p L) _ hR3 E (isSquare_leastSquare _)
      (leastSquare_step_conditions (crtModuli m₀ blk p L) (E := E) (le_refl 1)
        (fun k => Nat.coprime_one_left _) (crtModuli_pairwise blk hpair)).2.2.2 0 j F)
    hdc
    (fun b hb => mixedLpBound_variationLaw_pull (crtAtomEquiv blk h0 L b.1) (Λ b.1)
      (hatom b.1 b.2) hb)
  have hprod : (∏ b : {b // b ∈ E}, ∑ y : Slot → ZMod (crtModuli m₀ blk p L b.1),
      |lawDensity (crtLaws blk h0 L Λ b.1) y|) =
      ∏ b : {b // b ∈ E}, ∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (Λ b.1) x| :=
    prod_congr rfl fun b _ => sum_abs_lawDensity_pullLaw _ _
  rw [hprod] at h
  exact h

end Sarkozy.EnvelopeEnergiesPaper
