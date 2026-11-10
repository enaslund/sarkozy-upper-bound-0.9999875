module

public import Sarkozy.DensityDC.Paper

/-!
# `prop:record:density-structured` with `lem:record:density-dc` proved

`density_structured_dc` is `Sarkozy.Structured.density_structured_reference` (the paper's
first inequality of `prop:record:density-structured` for `μ_N = ⊗_b μ_b`) with its
hypothesis `hdc` derived from `lem:record:density-dc`
(`Sarkozy.DensityDC.density_dc_paper` and `dc_constant_le`). The additive error is
`C_dc ‖ρ‖ L^{-σ} α` with `C_dc = 72 C'^γ c₂^{1/2} c₁^{71/142}` and `H = N^{1/40}`.

In place of `hdc` the hypotheses are:
* (R4) for the tail coordinates `T` (`hmix`), which stays a hypothesis;
* the prefix conductor `C' = Q_pre` (`hdiv`);
* `H ≤ Q'_v` and `H D_E ≤ Q` (`lem:scale-conditions`, consequences, with `Q = N^β`,
  `Q'_v = n_v^β`);
* `g̃ = g` at the unchanged slots (`hgu`);
* the averaged moments `B₂ ≤ c₂ N^ε α` and `B ≤ c₁ N^ε α` (`lem:record:lift-moments`(c),
  `lem:record:fibre-scale`(e)), which are hypotheses;
* (S1) in the form `ε - γ/40 ≤ -σ`.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- **`prop:record:density-structured` with `lem:record:density-dc` proved** (first
inequality, `μ_N = ⊗_b μ_b`, coordinates as atoms). -/
theorem density_structured_dc (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (hR3 : SquareAffineInvariant m μb)
    (T : Finset J) (hprime : ∀ j ∈ T, (m j).Prime) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmix : ∀ j ∈ T, ∀ v, IsGammaMixing (m j) γ (μb j) {v}) {C' : ℕ} (hC' : 0 < C')
    (hdiv : ∀ a : ResidueSpace m, (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
    (E : Finset J) {qE cE : ℕ}
    (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0)
    (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ) (hunif : selectedMarginalsUniform ρ)
    (D0 : Slot → ℕ) (hD0 : ∀ v, 1 ≤ D0 v) (hD0M : ∀ v, D0 v ∣ M0)
    (hcop0 : ∀ v k, (D0 v).Coprime (m k))
    (M : Slot → ℕ) (hM : ∀ v, M v = blockScale * L ∨ M v = L)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, m j = 1 ∧ M v = blockScale * L))
    (Q : ℝ) (Q' : Slot → ℝ) (gt : Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ)
    (hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel m E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR m E (D0 v)) (blockScale * stepEll m E (D0 v) (M v)) (Q' v) y).re)
    (hgu : ∀ v, ¬changed v → ∀ ω x, gt ω v x = paperInputs m E Q A D0 M c s ω v x)
    (hun : ∀ v, ¬changed v → ∀ ω x, referenceEnergy (FiniteLaw.tensor μb) (gt ω v x) ≤ Yf L A)
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hHQ' : ∀ v, changed v → ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) ≤ Q' v)
    (hHQ : ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) * (∏ j ∈ E, m j : ℕ) ≤ Q)
    {B2 B c2 c1 ε σ : ℝ} (hc2 : 0 ≤ c2) (hc1 : 0 ≤ c1) (hσ : 0 ≤ σ)
    (hS1 : ε - γ / 40 ≤ -σ)
    (hm2 : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment 2
          (fun y => paperInputs m E Q A D0 M c s p.1 v (p.2 v) y - gt p.1 v (p.2 v) y)) ≤ B2)
    (hmg : ∀ hρ : 0 < totalVariation ρ, ∀ w,
      (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment 142
          (paperInputs m E Q A D0 M c s p.1 w (p.2 w))) ≤ B)
    (hmgt : ∀ hρ : 0 < totalVariation ρ, ∀ w,
      (P.product (variationLaw ρ hρ)).expect (fun p =>
        (FiniteLaw.uniform (ResidueSpace m)).moment 142 (gt p.1 w (p.2 w))) ≤ B)
    (hB2 : 0 ≤ B2) (hB : 0 ≤ B)
    (hB2le : B2 ≤ c2 * ((blockScale * L : ℕ) : ℝ) ^ ε * density (blockScale * L) A)
    (hBle : B ≤ c1 * ((blockScale * L : ℕ) : ℝ) ^ ε * density (blockScale * L) A) :
    |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        (72 * (C' : ℝ) ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) *
          density (blockScale * L) A) := by
  set N : ℝ := ((blockScale * L : ℕ) : ℝ) with hNdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hLN : (L : ℝ) ≤ N := by
    rw [hNdef]
    exact_mod_cast Nat.le_mul_of_pos_left L (by norm_num [blockScale])
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one (hL1.trans hLN)
  have hH : 0 < N ^ ((1 : ℝ) / 40) := Real.rpow_pos_of_pos hN0 _
  have hα : 0 ≤ density (blockScale * L) A := density_nonneg _ _
  -- `lem:record:density-dc`, Steps 1 and 2
  have hdc0 := density_dc_paper m hpair μb hR3 T hprime hγ hmix hC' hdiv E P ρ D0 hD0 hcop0 M
    (fun v => by
      rcases hM v with h | h
      · rw [h]; exact Nat.mul_pos (by norm_num [blockScale]) (by omega)
      · rw [h]; omega)
    c s changed Q Q' gt hgt hgu hH hHQ' hHQ hB2 hB hm2 hmg hmgt
  -- at most 72 changed slots
  have hcard : (((univ.filter changed).card : ℕ) : ℝ) ≤ 72 := by
    have : (univ.filter changed).card ≤ 72 := by
      have h := card_filter_le (univ : Finset Slot) changed
      rwa [card_univ, card_slot] at h
    exact_mod_cast this
  have hterm : 0 ≤ ((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ *
      (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)) := by
    have h1 : 0 ≤ ((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ :=
      Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hH.le) _
    have h2 : 0 ≤ B2 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hB2 _
    have h3 : 0 ≤ B ^ ((71 : ℝ) / 142) := Real.rpow_nonneg hB _
    positivity
  have hconst := dc_constant_le (C' := (C' : ℝ)) (Nat.cast_nonneg _) hc2 hc1 hB2 hB hα hL1 hLN
    hσ hS1 hB2le hBle
  have hdc : |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s) -
      structuredEnergy (FiniteLaw.tensor μb) P ρ gt| ≤
      (72 * (C' : ℝ) ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142)) * totalVariation ρ *
        (L : ℝ) ^ (-σ) * density (blockScale * L) A := by
    refine hdc0.trans ?_
    calc totalVariation ρ * (((univ.filter changed).card : ℝ) *
          (((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ * (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142))))
        ≤ totalVariation ρ * (72 * (((C' : ℝ) / N ^ ((1 : ℝ) / 40)) ^ γ *
            (B2 ^ ((1 : ℝ) / 2) * B ^ ((71 : ℝ) / 142)))) := by
          apply mul_le_mul_of_nonneg_left _ (totalVariation_nonneg ρ)
          exact mul_le_mul_of_nonneg_right hcard hterm
      _ ≤ totalVariation ρ * (72 * (C' : ℝ) ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142) *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
          mul_le_mul_of_nonneg_left hconst (totalVariation_nonneg ρ)
      _ = (72 * (C' : ℝ) ^ γ * c2 ^ ((1 : ℝ) / 2) * c1 ^ ((71 : ℝ) / 142)) * totalVariation ρ *
            (L : ℝ) ^ (-σ) * density (blockScale * L) A := by ring
  exact density_structured_reference m hpair hcex hθ hθ1 ha hC0 hL hY0 hsc hM0 μb hμb hR3 E hDE
    hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed hchg Q Q' gt hgt hun
    hrest hdc

end Sarkozy.DensityDC
