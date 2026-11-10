module

public import Sarkozy.Structured.ScaleInputs

/-!
# The coarse price and the second form of `prop:record:density-structured`

`def:record:structured-energy` defines the coarse price
`Π = ∏_v ξ_v^{a/72} ∏_{v changed} κ_v^{θ/72}`, for numbers `κ_v ≥ 1` with
`ᾱ_v ≤ κ_v α` at every changed slot, and notes `Π ≥ max(1, Π_main)`.

* `coarsePrice`, `mainPrice_le_coarsePrice`, `one_le_coarsePrice`: the definition and
  the two inequalities (the second with `ξ_v ≥ 1`).
* `density_structured_scale_coarse`: the second inequality of
  `prop:record:density-structured` for the paper's inputs:
  `|𝔈| ≤ ‖ρ‖ (1 + u_L + (C_dc/C₀) L^{a-σ} α^{1-θ}) Π Y`, with the hypotheses of
  `density_structured_scale` and `C₀ > 0`, `C_dc ≥ 0`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

/-- The coarse price `Π = ∏_v ξ_v^{a/72} ∏_{v changed} κ_v^{θ/72}`
(`def:record:structured-energy`). -/
noncomputable def coarsePrice (ξ κ : Slot → ℝ) (changed : Slot → Prop) [DecidablePred changed]
    (a θ : ℝ) : ℝ :=
  (∏ v, ξ v ^ (a / 72)) * ∏ v ∈ univ.filter changed, κ v ^ (θ / 72)

/-- `Π_main ≤ Π` when `ᾱ_v ≤ κ_v α` at every changed slot. -/
theorem mainPrice_le_coarsePrice (ξ αbar κ : Slot → ℝ) (changed : Slot → Prop)
    [DecidablePred changed] {a θ α : ℝ} (hξ : ∀ v, 0 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hα : 0 < α) (hθ : 0 ≤ θ) (hκ : ∀ v, changed v → αbar v ≤ κ v * α) :
    mainPrice ξ αbar changed a θ α ≤ coarsePrice ξ κ changed a θ := by
  unfold mainPrice coarsePrice
  apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun v _ => Real.rpow_nonneg (hξ v) _)
  apply prod_le_prod₀
  · intro v _
    exact Real.rpow_nonneg (div_nonneg (hαbar v) hα.le) _
  · intro v hv
    have hv' := (mem_filter.mp hv).2
    apply Real.rpow_le_rpow (div_nonneg (hαbar v) hα.le) _ (by positivity)
    rw [div_le_iff₀ hα]
    exact hκ v hv'

/-- `Π ≥ 1` when `ξ_v ≥ 1` and `κ_v ≥ 1`. -/
theorem one_le_coarsePrice (ξ κ : Slot → ℝ) (changed : Slot → Prop) [DecidablePred changed]
    {a θ : ℝ} (hξ : ∀ v, 1 ≤ ξ v) (ha : 0 ≤ a) (hθ : 0 ≤ θ)
    (hκ : ∀ v, changed v → 1 ≤ κ v) : 1 ≤ coarsePrice ξ κ changed a θ := by
  unfold coarsePrice
  have h1 : 1 ≤ ∏ v, ξ v ^ (a / 72) :=
    one_le_prod₀ fun v _ => Real.one_le_rpow (hξ v) (by positivity)
  have h2 : 1 ≤ ∏ v ∈ univ.filter changed, κ v ^ (θ / 72) :=
    one_le_prod₀ fun v hv => Real.one_le_rpow (hκ v (mem_filter.mp hv).2) (by positivity)
  nlinarith

section Coarse

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- **`prop:record:density-structured`, second inequality, for the paper's inputs**:
`|𝔈| ≤ ‖ρ‖ (1 + u_L + (C_dc/C₀) L^{a-σ} α^{1-θ}) Π Y` with the coarse price `Π` of
numbers `κ_v ≥ 1` with `ᾱ_v ≤ κ_v α` at the changed slots. -/
theorem density_structured_scale_coarse (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 < C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
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
    {Cdc σ : ℝ} (hCdc : 0 ≤ Cdc)
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
    (κ : Slot → ℝ) (hκ1 : ∀ v, changed v → 1 ≤ κ v)
    (hκ : ∀ v, changed v →
      paperMeanDensity P A D0 M c s v ≤ κ v * density (blockScale * L) A) :
    |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * (1 + scaleU blockScale M0 Qcl stageTau L +
        Cdc / C0 * (L : ℝ) ^ (a - σ) * density (blockScale * L) A ^ (1 - θ)) *
        coarsePrice (paperPrice m E D0 M L) κ changed a θ * Yf L A := by
  have hmain := density_structured_scale m hpair hcex hθ hθ1 ha hC0.le hL hY0 hsc hM0 μS hμS E
    hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed hchg Q Q' gt
    hgt hun hrest hinvT hdc
  have hα := hcex.density_pos hθ.ne' hY0
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlow := hcex.lower
  have hY : 0 ≤ Yf L A := by
    have : 0 ≤ C0 * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ θ := by
      have h1 : 0 ≤ (L : ℝ) ^ (-a) := Real.rpow_nonneg hLpos.le _
      have h2 : 0 ≤ density (blockScale * L) A ^ θ := Real.rpow_nonneg hα.le _
      positivity
    linarith
  -- the prices
  have hM1 : ∀ v, 1 ≤ M v := by
    intro v
    rcases hM v with h | h
    · rw [h]; exact Nat.mul_pos (by norm_num [blockScale]) (by omega)
    · rw [h]; omega
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
  have hPm := mainPrice_le_coarsePrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s)
    κ changed (a := a) (fun v => zero_le_one.trans (hξ v)) hαbar hα hθ.le hκ
  have hP1 := one_le_coarsePrice (paperPrice m E D0 M L) κ changed hξ ha hθ.le hκ1
  have h := density_structured_coarse hmain (totalVariation_nonneg ρ) hC0 hLpos hα
    (scaleU_nonneg _ _ _ _ _) hY hCdc hlow hPm hP1
  exact h

end Coarse

end Sarkozy.Structured
