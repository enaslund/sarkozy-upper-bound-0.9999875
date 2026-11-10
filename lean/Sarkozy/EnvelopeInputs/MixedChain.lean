module

public import Sarkozy.Structured.ThetaChain
public import Sarkozy.EnvelopeInputs.LabelBound

/-!
# The ϑ chain with the density moment of the selected law (base and `Structured` layers)

WP-R's `Structured/ThetaChain.lean` re-runs `density_structured_paper`, `…_scale` and
`…_reference` on `density_structured_theta_counterexample`, with the two-occurrence structure of
`prop:density:production` (`slotOf`, `hindep : PairIndependent …`) as named hypotheses. For the
energies with a nonempty selected set every slot is changed, and that structure is absent (see
`LabelBound`). This file re-runs the same layers, **with WP-R's proofs unchanged except for the
last step**, on `density_structured_mixed_counterexample`: the counterexample form of
`EnvelopeInputs.density_structured_theta_of_mixed`. The two-occurrence hypotheses are replaced by
* `hmix`: the variation law `|ρ|/‖ρ‖` of the selected labels has unit mixed `L^{72/θ}` (density
  endpoint `θ`; Part V data);
* `hmeanω` (`MeanBound`): for every index `ω` the uniform mean of the paper's fibre density is
  at most its mean `paperMeanDensity` over the index (equality for inputs that do not depend on
  the index, `meanBound_of_const`, and for a trivial index, `meanBound_of_subsingleton`).

WP-R's uniform-marginal hypothesis `hunif` (condition (b) for `ρ`) is dropped from these layers:
it was used only for the sample-law mean of the last step. `2θ/72 ≤ 1` is no longer needed by the
last step; it is kept where WP-R's progression averaging uses `θ ≤ 72`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- **The per-index fibre means** are at most the index-averaged mean `paperMeanDensity`. -/
def MeanBound (E : Finset J) (A : Finset ℤ) (P : FiniteLaw Ω) (D0 M : Slot → ℕ)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v)) (changed : Slot → Prop) : Prop :=
  ∀ ω v, changed v →
    (FiniteLaw.uniform (ResidueSpace m)).expect
        (fun x => fibreDensity m E x (s ω v) A (c ω v) (M v)) ≤
      paperMeanDensity P A D0 M c s v

omit [DecidableEq J] in
/-- `density_structured_theta_of_mixed` at a least normalized counterexample. -/
theorem density_structured_mixed_counterexample {X XE : Type*} [Fintype X] [Fintype XE]
    [Nonempty XE] {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ}
    {A : Finset ℤ} (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ)
    (ha : 0 ≤ a) (hC0 : 0 ≤ C0) (hL : 1 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    (μS : FiniteLaw (Slot → X)) (hμS : SlotReflectionPositive (signedIntegral μS.weight))
    (P : FiniteLaw Ω) (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed] {u Cdc σ : ℝ} (hu : 0 ≤ u)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Yf L A)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤
      (1 + u) * C0 * (L : ℝ) ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmix : ∀ hρ : 0 < totalVariation ρ, MixedLpBound (variationLaw ρ hρ) (72 / θ) 1)
    (hmean : ∀ ω v, changed v → (FiniteLaw.uniform XE).expect (αf ω v) ≤ αbar v)
    (hdc : |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :
    |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * ((1 + u) *
        mainPrice ξ αbar changed a θ (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  have hα := hcex.density_pos hθ.ne' hY0
  have hlow := hcex.lower
  have hYpos : 0 ≤ Yf L A := le_trans (by
    exact mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (density_nonneg _ _) _)) hlow.le
  exact density_structured_theta_of_mixed μS hμS P ρ g gt changed hC0 ha hθ
    (by exact_mod_cast hL) hα hu hYpos hlow ξ αbar hξ hαbar hun αf hαf hch hmix hmean hdc

/-- `density_structured_paper` with the density moment in place of the two-occurrence
structure. -/
theorem density_structured_paper_mixed (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ2 : 2 * (θ / 72) ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    (μS : FiniteLaw (Slot → ResidueSpace m))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (E : Finset J)
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ)
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
    (hmix : ∀ hρ : 0 < totalVariation ρ, MixedLpBound (variationLaw ρ hρ) (72 / θ) 1)
    (hmeanω : MeanBound m E A P D0 M c s changed) :
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
  exact density_structured_mixed_counterexample hcex hθ ha hC0 (by omega) hY0 μS hμS P ρ
    (paperInputs m E Q A D0 M c s) gt changed hu (paperPrice m E D0 M L)
    (paperMeanDensity P A D0 M c s) hξ hαbar hun
    (fun ω v x => fibreDensity m E x (s ω v) A (c ω v) (M v)) hαf hch hmix hmeanω hdc

/-- `density_structured_scale` with the density moment in place of the two-occurrence
structure. -/
theorem density_structured_scale_mixed (hpair : Pairwise fun i j => (m i).Coprime (m j))
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
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ)
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
    (hmix : ∀ hρ : 0 < totalVariation ρ, MixedLpBound (variationLaw ρ hρ) (72 / θ) 1)
    (hmeanω : MeanBound m E A P D0 M c s changed) :
    |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  density_structured_paper_mixed (hmix := hmix) (hmeanω := hmeanω) m hpair hcex hθ hθ2 ha hC0
      hL hY0 μS hμS E P ρ D0 hD0 hcop0 M
    hM c s changed hchg Q Q' gt hgt hun (scaleU_nonneg _ _ _ _ _) hrest hinvT
    (fun v _ => lambda_pow_le_scaleU m E hsc (by omega) hM0 hDE hqE hcE hcE0 hcQ hcopE hqN
      (hD0M v) (hcop0 v) (hM v)) hdc

/-- `density_structured_reference` with the density moment in place of the two-occurrence
structure. -/
theorem density_structured_reference_mixed (hpair : Pairwise fun i j => (m i).Coprime (m j))
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
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ)
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
    (hmix : ∀ hρ : 0 < totalVariation ρ, MixedLpBound (variationLaw ρ hρ) (72 / θ) 1)
    (hmeanω : MeanBound m E A P D0 M c s changed) :
    |structuredEnergy (FiniteLaw.tensor μb) P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  density_structured_scale_mixed (hmix := hmix) (hmeanω := hmeanω) m hpair hcex hθ hθ2 ha hC0
      hL hY0 hsc hM0 (FiniteLaw.tensor μb)
    (tensor_slot_reflection_positive μb hμb) E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ D0 hD0
    hD0M hcop0 M hM c s changed hchg Q Q' gt hgt hun hrest
    (fun v _ ω j F => tensor_expect_stepMapOff m μb hR3 E (isSquare_leastSquare _)
      (leastSquare_step_conditions m (E := E) (hD0 v) (hcop0 v) hpair).2.2.2 (c ω v) j F)
    hdc

end Sarkozy.EnvelopeInputs
