module

public import Sarkozy.Structured.ThetaProduction
public import Sarkozy.Structured.AffineInvariance

/-!
# The ϑ chain: `prop:record:density-structured` layers without `θ ≤ 1`

The layers `density_structured_paper`, `density_structured_scale` and
`density_structured_reference` (`PaperEnergy`, `ScaleInputs`, `AffineInvariance`) pass
`θ ≤ 1` down to `density_structured`, where it is used once (the final Jensen step). This
file re-runs them on `density_structured_theta_counterexample`
(`Sarkozy/Structured/ThetaProduction.lean`). The proofs are otherwise unchanged. In each
`_theta` layer:
* `θ ≤ 1` is replaced by `2θ/72 ≤ 1`, which holds at `ϑ = densityExponent`
  (`two_mul_densityExponent_div_le`);
* the two-occurrence structure of `prop:density:production`
  (`paper/sections/31_density_induction_upgrade.tex:498`) is a named hypothesis:
  `slotOf : I × Bool ≃ {v // changed v}` (each query index occurs in exactly two changed
  slots) and `hindep : PairIndependent …` (distinct indices are independent for the paper's
  fibre densities). Deriving these from the index law of the production arguments is not
  done here.

The progression averaging (`changed_slot_bound_paper`) needs only `θ ≤ 72`, which follows
from `2θ/72 ≤ 1`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- **The two-occurrence independence of `prop:density:production`** for the paper's fibre
densities: under the sample law `P ⊗ |ρ|/‖ρ‖`, the pair terms
`α_{f,v}^{θ/72} α_{f,v'}^{θ/72}` of the two changed slots `v = slotOf (e, true)`,
`v' = slotOf (e, false)` of the distinct query indices `e` are independent. -/
def PairIndependent (E : Finset J) (A : Finset ℤ) (P : FiniteLaw Ω)
    (ρ : (Slot → ResidueSpace m) → ℝ) (D0 M : Slot → ℕ) (c : Ω → Slot → ℤ)
    (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v)) (changed : Slot → Prop) [DecidablePred changed]
    (θ : ℝ) {I : Type} [Fintype I] (slotOf : I × Bool ≃ {v // changed v}) : Prop :=
  ∀ hρ : 0 < totalVariation ρ,
    (P.product (variationLaw ρ hρ)).expect (fun p => ∏ e,
      (fibreDensity m E (p.2 (slotOf (e, true))) (s p.1 (slotOf (e, true))) A
          (c p.1 (slotOf (e, true))) (M (slotOf (e, true))) ^ (θ / 72) *
        fibreDensity m E (p.2 (slotOf (e, false))) (s p.1 (slotOf (e, false))) A
          (c p.1 (slotOf (e, false))) (M (slotOf (e, false))) ^ (θ / 72))) =
    ∏ e, (P.product (variationLaw ρ hρ)).expect (fun p =>
      fibreDensity m E (p.2 (slotOf (e, true))) (s p.1 (slotOf (e, true))) A
          (c p.1 (slotOf (e, true))) (M (slotOf (e, true))) ^ (θ / 72) *
        fibreDensity m E (p.2 (slotOf (e, false))) (s p.1 (slotOf (e, false))) A
          (c p.1 (slotOf (e, false))) (M (slotOf (e, false))) ^ (θ / 72))

/-- `density_structured_paper` without `θ ≤ 1` (see the module docstring). -/
theorem density_structured_paper_theta (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    (μS : FiniteLaw (Slot → ResidueSpace m))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (E : Finset J)
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ) (hunif : selectedMarginalsUniform ρ)
    (D0 : Slot → ℕ) (hD0 : ∀ v, 1 ≤ D0 v) (hcop0 : ∀ v k, (D0 v).Coprime (m k))
    (M : Slot → ℕ) (hM : ∀ v, M v = blockScale * L ∨ M v = L)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, m j = 1 ∧ M v = blockScale * L))
    (Q : ℝ) (Q' : Slot → ℝ) (gt : Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ)
    (hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel m E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR m E (D0 v)) (blockScale * stepEll m E (D0 v) (M v)) (Q' v) y).re)
    (hun : ∀ v, ¬changed v → ∀ ω x, referenceEnergy μS (gt ω v x) ≤ Yf L A)
    {u Cdc σ : ℝ} (hu : 0 ≤ u)
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy μS (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hinvT : ∀ v, changed v → ∀ ω (j : ℤ) (F : (Slot → ResidueSpace m) → ℝ),
      μS.expect (fun w => F (fun v' => stepMapOff m E (stepR m E (D0 v)) (c ω v) j (w v'))) =
        μS.expect F)
    (hlamu : ∀ v, changed v →
      (((stepR m E (D0 v) : ℕ) : ℝ) * ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℝ) /
        M v) ^ 72 ≤ 1 + u)
    (hdc : |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    {I : Type} [Fintype I] [DecidableEq I] (slotOf : I × Bool ≃ {v // changed v})
    (hindep : PairIndependent m E A P ρ D0 M c s changed θ slotOf) :
    |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + u) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hM1 : ∀ v, 1 ≤ M v := by
    intro v
    rcases hM v with h | h
    · rw [h]; exact Nat.mul_pos (by norm_num [blockScale]) (by omega)
    · rw [h]; omega
  have hA := hcex.admissible
  have hξ : ∀ v, 1 ≤ paperPrice m E D0 M L v := by
    intro v
    unfold paperPrice
    have hR1 : 1 ≤ stepR m E (D0 v) := leastSquare_pos _
    have hR1' : (1 : ℝ) ≤ ((stepR m E (D0 v) : ℕ) : ℝ) := by exact_mod_cast hR1
    have hNM : (1 : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) / M v := by
      have hMpos : (0 : ℝ) < M v := by exact_mod_cast hM1 v
      rw [le_div_iff₀ hMpos, one_mul]
      rcases hM v with h | h
      · rw [h]
      · rw [h]
        exact_mod_cast Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    nlinarith
  have hαbar : ∀ v, 0 ≤ paperMeanDensity P A D0 M c s v := by
    intro v
    unfold paperMeanDensity
    apply P.expect_nonneg
    intro ω
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hαf : ∀ ω v x, 0 ≤ fibreDensity m E x (s ω v) A (c ω v) (M v) := by
    intro ω v x
    unfold fibreDensity
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hch : ∀ v, changed v → ∀ ω x, referenceEnergy μS (gt ω v x) ≤
      (1 + u) * C0 * (L : ℝ) ^ (-a) * paperPrice m E D0 M L v ^ a *
        fibreDensity m E x (s ω v) A (c ω v) (M v) ^ θ := by
    intro v hv ω x
    rw [hgt ω v x hv]
    have h := changed_slot_bound_paper m μS hμS E x (hD0 v) (s ω v) (hcop0 v) hpair A hA.2
      (c ω v) (hM1 v) hL (hM v) (hchg v hv) (Q' v) ha hθ.le (by linarith) hC0
      (fun ℓ hℓ hℓL => hcex.2.2 ℓ hℓ hℓL) (hrest v hv) (fun j => hinvT v hv ω j) (hlamu v hv)
    unfold paperPrice
    exact h
  have hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect
        (fun p => fibreDensity m E (p.2 v) (s p.1 v) A (c p.1 v) (M v)) =
      paperMeanDensity P A D0 M c s v := by
    intro hρ v _
    rw [FiniteLaw.expect_product]
    unfold paperMeanDensity
    apply P.expect_congr
    intro ω
    rw [expect_variationLaw_slot ρ hρ hunif v
      (fun x => fibreDensity m E x (s ω v) A (c ω v) (M v)), uniform_fibreDensity]
  exact density_structured_theta_counterexample hcex hθ hθ2 ha hC0 (by omega) hY0 μS hμS P ρ
    (paperInputs m E Q A D0 M c s) gt changed hu (paperPrice m E D0 M L)
    (paperMeanDensity P A D0 M c s) hξ hαbar hun
    (fun ω v x => fibreDensity m E x (s ω v) A (c ω v) (M v)) hαf hch hmean slotOf hindep hdc

/-- `density_structured_scale` without `θ ≤ 1`. -/
theorem density_structured_scale_theta (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μS : FiniteLaw (Slot → ResidueSpace m))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (E : Finset J) {qE cE : ℕ}
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
    (hun : ∀ v, ¬changed v → ∀ ω x, referenceEnergy μS (gt ω v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy μS (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hinvT : ∀ v, changed v → ∀ ω (j : ℤ) (F : (Slot → ResidueSpace m) → ℝ),
      μS.expect (fun w => F (fun v' => stepMapOff m E (stepR m E (D0 v)) (c ω v) j (w v'))) =
        μS.expect F)
    (hdc : |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    {I : Type} [Fintype I] [DecidableEq I] (slotOf : I × Bool ≃ {v // changed v})
    (hindep : PairIndependent m E A P ρ D0 M c s changed θ slotOf) :
    |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  density_structured_paper_theta (slotOf := slotOf) (hindep := hindep) m hpair hcex hθ hθ2 ha hC0
      hL hY0 μS hμS E P ρ hunif D0 hD0 hcop0 M
    hM c s changed hchg Q Q' gt hgt hun (scaleU_nonneg _ _ _ _ _) hrest hinvT
    (fun v _ => lambda_pow_le_scaleU m E hsc (by omega) hM0 hDE hqE hcE hcE0 hcQ hcopE hqN
      (hD0M v) (hcop0 v) (hM v)) hdc

/-- `density_structured_reference` without `θ ≤ 1`. -/
theorem density_structured_reference_theta (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μb : ∀ b, FiniteLaw (Slot → ZMod (m b)))
    (hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
    (hR3 : SquareAffineInvariant m μb) (E : Finset J) {qE cE : ℕ}
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
    (hun : ∀ v, ¬changed v → ∀ ω x, referenceEnergy (FiniteLaw.tensor μb) (gt ω v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor μb)
          (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hdc : |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy (FiniteLaw.tensor μb) P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A)
    {I : Type} [Fintype I] [DecidableEq I] (slotOf : I × Bool ≃ {v // changed v})
    (hindep : PairIndependent m E A P ρ D0 M c s changed θ slotOf) :
    |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  density_structured_scale_theta (slotOf := slotOf) (hindep := hindep) m hpair hcex hθ hθ2 ha hC0
      hL hY0 hsc hM0 (FiniteLaw.tensor μb)
    (tensor_slot_reflection_positive μb hμb) E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0
    hD0M hcop0 M hM c s changed hchg Q Q' gt hgt hun hrest
    (fun v _ ω j F => tensor_expect_stepMapOff m μb hR3 E (isSquare_leastSquare _)
      (leastSquare_step_conditions m (E := E) (hD0 v) (hcop0 v) hpair).2.2.2 (c ω v) j F)
    hdc

end Sarkozy.Structured
