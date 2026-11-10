module

public import Sarkozy.Moments.Holder
public import Sarkozy.Reflection.Seminorm
public import Sarkozy.Energy
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Jensen

/-!
# Structured energies and the Hölder step of their estimate

`def:record:structured-energy` of the paper (`paper/sections/08_scale_comparison.tex`)
in the form used by the estimate `prop:record:density-structured`. The selected
atoms `E` carry a finite signed measure `ρ` on `X_E^V`, here a weight function on
`Slot → XE`; the remaining atoms `𝒮` carry the reference law `μ_𝒮`, here a
`FiniteLaw` on `Slot → X`; the index vectors `ω` have a law `P`, a `FiniteLaw` on a
finite type `Ω`; and the specialized inputs are `g ω v (z v) : X → ℝ`, the paper's
`g_v^ω(z_v, ·)`. Then

  `𝔈 = E_{ω∼P} ∫ Λ_{μ_𝒮}((g_v^ω(z_v, ·))_v) dρ(z)`     (`structuredEnergy`).

* `variationLaw ρ`: the law `|ρ|/‖ρ‖`; `selectedMarginalsUniform ρ` is the
  condition (b) of the definition, that every one-slot marginal of `|ρ|` is
  `‖ρ‖ Unif(X_E)`.
* `abs_structuredEnergy_le`: **the Hölder step** of the proof of
  `prop:record:density-structured`. For a law reflection positive at the sorting
  cuts, pointwise in `(ω, z)` the signed Hölder inequality (`lem:record:holder`(a),
  `Sarkozy.slot_signedHolder`) bounds the multilinear average by
  `∏_v Z_𝒮(g_v^ω(z_v,·))^{1/72}`; Hölder's inequality with 72 equal exponents on the
  probability space of `(ω, z)` with law `P ⊗ |ρ|/‖ρ‖`
  (`Sarkozy.FiniteLaw.abs_expect_prod_le_lpNorm`) then gives
  `|𝔈| ≤ ‖ρ‖ ∏_v (E Z_𝒮(g_v^ω(z_v,·)))^{1/72}`.
* `abs_structuredEnergy_le_of_slot_bounds`: the same with per-slot bounds
  `E Z_𝒮(g_v) ≤ b_v`.
* `expect_rpow_le_rpow_expect`: Jensen's inequality `E x^θ ≤ (E x)^θ`,
  `0 ≤ θ ≤ 1`, for the final averaging step.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

variable {X XE Ω : Type*} [Fintype X] [Fintype XE] [Fintype Ω]

/-- The total variation `‖ρ‖ = |ρ|(X_E^V)`. -/
noncomputable def totalVariation (ρ : (Slot → XE) → ℝ) : ℝ := ∑ z, |ρ z|

theorem totalVariation_nonneg (ρ : (Slot → XE) → ℝ) : 0 ≤ totalVariation ρ :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- Condition (b) of `def:record:structured-energy`: every one-slot marginal of the
variation `|ρ|` is `‖ρ‖ Unif(X_E)`. -/
def selectedMarginalsUniform [DecidableEq XE] (ρ : (Slot → XE) → ℝ) : Prop :=
  ∀ v (x : XE), ∑ z ∈ univ.filter (fun z : Slot → XE => z v = x), |ρ z| =
    totalVariation ρ / (Fintype.card XE : ℝ)

/-- **The structured energy** `𝔈 = E_{ω∼P} ∫ Λ_{μ_𝒮}((g_v^ω(z_v, ·))_v) dρ(z)`. -/
noncomputable def structuredEnergy (μS : FiniteLaw (Slot → X)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g : Ω → Slot → XE → X → ℝ) : ℝ :=
  P.expect fun ω => ∑ z, ρ z * multilinearIntegral (signedIntegral μS.weight)
    (fun v => g ω v (z v))

/-- The law `|ρ|/‖ρ‖` of the selected labels. -/
noncomputable def variationLaw (ρ : (Slot → XE) → ℝ) (h : 0 < totalVariation ρ) :
    FiniteLaw (Slot → XE) where
  weight z := |ρ z| / totalVariation ρ
  nonneg z := div_nonneg (abs_nonneg _) h.le
  total := by
    rw [← sum_div]
    exact div_self h.ne'

theorem expect_variationLaw (ρ : (Slot → XE) → ℝ) (h : 0 < totalVariation ρ)
    (f : (Slot → XE) → ℝ) :
    (variationLaw ρ h).expect f = (∑ z, |ρ z| * f z) / totalVariation ρ := by
  unfold FiniteLaw.expect variationLaw
  simp only
  rw [sum_div]
  apply sum_congr rfl
  intro z _
  ring

/-- `Z(g)^{1/72}` raised back to the power 72 is `Z(g)`. -/
theorem rootEnergy_rpow_72 {μS : FiniteLaw (Slot → X)}
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (g : X → ℝ) :
    |rootEnergy (signedIntegral μS.weight) g| ^ (72 : ℝ) = referenceEnergy μS g := by
  have hh := slot_signedHolder hμS
  rw [abs_of_nonneg (hh.rootEnergy_nonneg g)]
  rw [show (72 : ℝ) = ((72 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hp := hh.rootEnergy_pow g
  rw [card_slot] at hp
  rw [hp]
  rfl

/-- **The Hölder step of `prop:record:density-structured`**:
`|𝔈| ≤ ‖ρ‖ ∏_v (E_{P ⊗ |ρ|/‖ρ‖} Z_𝒮(g_v^ω(z_v, ·)))^{1/72}`. -/
theorem abs_structuredEnergy_le (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (hρ : 0 < totalVariation ρ) (g : Ω → Slot → XE → X → ℝ) :
    |structuredEnergy μS P ρ g| ≤ totalVariation ρ *
      ∏ v, ((P.product (variationLaw ρ hρ)).expect
        (fun p => referenceEnergy μS (g p.1 v (p.2 v)))) ^ ((1 : ℝ) / 72) := by
  set L := signedIntegral μS.weight
  set Jt := P.product (variationLaw ρ hρ)
  have hh := slot_signedHolder hμS
  set W : Slot → Ω × (Slot → XE) → ℝ := fun v p => rootEnergy L (g p.1 v (p.2 v))
  -- pointwise signed Hölder
  have hpoint : ∀ ω z, |multilinearIntegral L (fun v => g ω v (z v))| ≤ ∏ v, W v (ω, z) :=
    fun ω z => hh.2 _
  -- the energy is bounded by the expectation of the product of root energies
  have h1 : |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * Jt.expect (fun p => ∏ v, W v p) := by
    unfold structuredEnergy
    refine (P.abs_expect_le _).trans ?_
    rw [FiniteLaw.expect_product]
    have hω : ∀ ω, |∑ z, ρ z * multilinearIntegral L (fun v => g ω v (z v))| ≤
        totalVariation ρ * (variationLaw ρ hρ).expect (fun z => ∏ v, W v (ω, z)) := by
      intro ω
      rw [expect_variationLaw, mul_div_cancel₀ _ hρ.ne']
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply sum_le_sum
      intro z _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hpoint ω z) (abs_nonneg _)
    refine (P.expect_mono hω).trans_eq ?_
    exact P.expect_const_mul _ _
  -- Hölder with 72 equal exponents
  have h2 : Jt.expect (fun p => ∏ v, W v p) ≤ ∏ v, Jt.lpNorm 72 (W v) := by
    have hs : ∑ _v : Slot, (1 : ℝ) / 72 = 1 := by
      rw [sum_const, card_univ, card_slot, nsmul_eq_mul]
      norm_num
    exact (le_abs_self _).trans
      (Jt.abs_expect_prod_le_lpNorm (fun _ => (72 : ℝ)) (fun _ => by norm_num) hs W)
  have h3 : ∀ v, Jt.lpNorm 72 (W v) =
      (Jt.expect (fun p => referenceEnergy μS (g p.1 v (p.2 v)))) ^ ((1 : ℝ) / 72) := by
    intro v
    unfold FiniteLaw.lpNorm FiniteLaw.moment
    congr 1
    apply Jt.expect_congr
    intro p
    exact rootEnergy_rpow_72 hμS _
  calc |structuredEnergy μS P ρ g| ≤ totalVariation ρ * Jt.expect (fun p => ∏ v, W v p) := h1
    _ ≤ totalVariation ρ * ∏ v, Jt.lpNorm 72 (W v) :=
        mul_le_mul_of_nonneg_left h2 (totalVariation_nonneg ρ)
    _ = _ := by simp only [h3]

/-- The Hölder step with per-slot bounds `E Z_𝒮(g_v) ≤ b_v`. -/
theorem abs_structuredEnergy_le_of_slot_bounds (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (hρ : 0 < totalVariation ρ) (g : Ω → Slot → XE → X → ℝ)
    (b : Slot → ℝ)
    (hb : ∀ v, (P.product (variationLaw ρ hρ)).expect
      (fun p => referenceEnergy μS (g p.1 v (p.2 v))) ≤ b v) :
    |structuredEnergy μS P ρ g| ≤ totalVariation ρ * ∏ v, b v ^ ((1 : ℝ) / 72) := by
  refine (abs_structuredEnergy_le μS hμS P ρ hρ g).trans ?_
  apply mul_le_mul_of_nonneg_left _ (totalVariation_nonneg ρ)
  apply prod_le_prod₀
  · intro v _
    exact Real.rpow_nonneg ((P.product (variationLaw ρ hρ)).expect_nonneg
      fun p => referenceEnergy_nonneg μS hμS _) _
  · intro v _
    exact Real.rpow_le_rpow ((P.product (variationLaw ρ hρ)).expect_nonneg
      fun p => referenceEnergy_nonneg μS hμS _) (hb v) (by norm_num)

/-- If `ρ = 0` the structured energy vanishes. -/
theorem structuredEnergy_eq_zero_of_totalVariation (μS : FiniteLaw (Slot → X))
    (P : FiniteLaw Ω) (ρ : (Slot → XE) → ℝ) (hρ : totalVariation ρ = 0)
    (g : Ω → Slot → XE → X → ℝ) : structuredEnergy μS P ρ g = 0 := by
  have hz : ∀ z, ρ z = 0 := fun z =>
    abs_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun z _ => abs_nonneg (ρ z)).mp hρ z (mem_univ z))
  unfold structuredEnergy
  simp [hz, FiniteLaw.expect]

/-- **Jensen's inequality** for `x ↦ x^θ`, `0 ≤ θ ≤ 1`, under a finite law. -/
theorem expect_rpow_le_rpow_expect {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω')
    {x : Ω' → ℝ} (hx : ∀ ω, 0 ≤ x ω) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    μ.expect (fun ω => x ω ^ θ) ≤ μ.expect x ^ θ := by
  have hc := (Real.concaveOn_rpow hθ0 hθ1).le_map_sum (t := univ) (w := μ.weight) (p := x)
    (fun ω _ => μ.nonneg ω) μ.total (fun ω _ => Set.mem_Ici.mpr (hx ω))
  simpa only [smul_eq_mul, FiniteLaw.expect] using hc

end Sarkozy.Structured
