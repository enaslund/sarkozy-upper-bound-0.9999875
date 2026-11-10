module

public import Sarkozy.EnvelopeInputs.MixedChainDC



@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing
  Sarkozy.DensityDC Sarkozy.PaperFrame

/-- An expectation over a subsingleton type is the value at its point. -/
theorem expect_of_subsingleton {Ω : Type*} [Fintype Ω] [Subsingleton Ω] (P : FiniteLaw Ω)
    (ω : Ω) (f : Ω → ℝ) : P.expect f = f ω := by
  unfold FiniteLaw.expect
  have h : ∀ ω', P.weight ω' * f ω' = P.weight ω' * f ω := fun ω' => by
    rw [Subsingleton.elim ω' ω]
  rw [Finset.sum_congr rfl fun ω' _ => h ω', ← Finset.sum_mul, P.total, one_mul]

/-- **The per-index means for a trivial index**: `MeanBound` holds when the index type is a
subsingleton. -/
theorem meanBound_of_subsingleton {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ)
    [∀ j, NeZero (m j)] {Ω : Type*} [Fintype Ω] [Subsingleton Ω] (E : Finset J) (A : Finset ℤ)
    (P : FiniteLaw Ω) (D0 M : Slot → ℕ) (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
    (changed : Slot → Prop) : MeanBound m E A P D0 M c s changed := by
  intro ω v _
  rw [uniform_fibreDensity]
  unfold paperMeanDensity
  rw [expect_of_subsingleton P ω]

/-- **`prop:record:density-structured` at `ϑ` for unchanged inputs, from the density moment**
(`lem:bracket-energy`, (E1) first bound, for the subset terms and the folded energies): for a
selected set `E` with `D_E ≠ 1` and small `q_E`, a weight `ρ` with uniform selected marginals
whose variation law has unit mixed `L^{72/θ}` (Part V), and the unchanged inputs `F_A`
(`D₀ = 1`, `M = N`, `c = 0`, trivial index), every slot is changed and
`|𝔈| ≤ ‖ρ‖ ((1 + u_L) Π_main Y + C L^{-σ} α)`. No two-occurrence or independence hypothesis. -/
theorem density_structured_unchanged_mixed (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
      (P4 : ℕ)
      (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
      (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
      {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ},
      ∀ (_hpair : Pairwise fun i j =>
          (joinModuli m₀ (tailModuli (tailPrimes P4) L) i).Coprime
            (joinModuli m₀ (tailModuli (tailPrimes P4) L) j))
      (_hcex : IsLeastCounterexample (paperY m₀ (tailPrimes P4) μ0 μp) a θ C0 L A) (_hθ : 0 < θ)
      (_hθ2 : 2 * (θ / 72) ≤ 1) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L)
      (_hY0 : paperY m₀ (tailPrimes P4) μ0 μp L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (_hp0 : ∀ i, SlotReflectionPositive (signedIntegral (μ0 i).weight))
      (_hpp : ∀ (q : ℕ) [NeZero q], q.Prime →
        SlotReflectionPositive (signedIntegral (μp q).weight))
      (_hR30 : ∀ i (r t : ZMod (m₀ i)), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod (m₀ i)) → ℝ,
          (μ0 i).expect (fun w => F (fun v => r * w v + t)) = (μ0 i).expect F)
      (_hR3p : ∀ (q : ℕ) [NeZero q] (r t : ZMod q), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod q) → ℝ,
          (μp q).expect (fun w => F (fun v => r * w v + t)) = (μp q).expect F)
      {γ : ℝ} (_hγ : 0 ≤ γ)
      (_hmixp : ∀ (j : ↥(tailPrimes P4 L)) (v : Slot), IsGammaMixing (j : ℕ) γ (μp (j : ℕ)) {v})
      (E : Finset (J₀ ⊕ ↥(tailPrimes P4 L))) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j = qE * cE)
      (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (_hne : ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j ≠ 1)
      (ρ : (Slot → ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L))) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ)
      (_hdmom : ∀ hρ : 0 < totalVariation ρ, MixedLpBound (variationLaw ρ hρ) (72 / θ) 1),
      |structuredEnergy (FiniteLaw.tensor (atomLaws m₀ (tailPrimes P4) μ0 μp L))
          (FiniteLaw.uniform Unit) ρ
          (paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
            (paperCutoff (blockScale * L)) A (fun _ => 1) (fun _ => blockScale * L)
            (fun _ _ => 0) (fun _ _ => 0))| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (fun _ => 1)
              (fun _ => blockScale * L) L)
            (paperMeanDensity (FiniteLaw.uniform Unit) A (fun _ => 1) (fun _ => blockScale * L)
              (fun _ _ => 0) (fun _ _ => 0)) (fun _ => True) a θ (density (blockScale * L) A) *
            paperY m₀ (tailPrimes P4) μ0 μp L A +
          (72 * ((∏ i, m₀ i : ℕ) : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_dc_tailPrimes_mixed ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ P4 μ0 μp a θ C0 L A hpair hcex hθ hθ2 ha hC0 hL hY0 M0 Qcl Qpre N0 N0' hsc hM0
    hp0 hpp hR30 hR3p γ hγ hmixp E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN hne ρ hunif σ hσ hS1 hdmom
  exact h m₀ P4 μ0 μp hpair hcex hθ hθ2 ha hC0 hL hY0 hsc hM0 hp0 hpp hR30 hR3p hγ hmixp E hDE hqE
    hcE hcE0 hcQ hcopE hqN (FiniteLaw.uniform Unit) ρ hunif (fun _ => 1) (fun _ => le_rfl)
    (fun _ => one_dvd _) (fun _ _ => Nat.coprime_one_left _) (fun _ => blockScale * L)
    (fun _ => Or.inl rfl) (fun _ _ => 0) (fun _ _ => 0) (fun _ => True)
    (fun _ _ hv => hne ((one_mul _).symm.trans hv.1)) (fun _ hv => absurd trivial hv) hσ hS1 hdmom
    (meanBound_of_subsingleton _ _ _ _ _ _ _ _ _)

end Sarkozy.EnvelopeInputs
