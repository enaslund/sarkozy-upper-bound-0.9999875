module

public import Sarkozy.TraceMixing.ProductionFromIndex
public import Sarkozy.Moments.Energy

/-!
# The label bound of the ϑ chain from the density moment of the selected law

`paper/sections/31_density_induction_upgrade.tex`, `prop:density:production` and
`lem:density:coupled`. At `θ = ϑ > 1` the final Jensen step of `prop:record:density-structured`
fails, and WP-R's `_theta` layers replace it by a product bound over the changed slots. WP-S
isolated it as the hypothesis `hpairs` of `TraceMixing.density_structured_theta_of_pairs`:

  `E_{P ⊗ |ρ|/‖ρ‖} ∏_{v changed} α_f(ω, v, z_v)^{θ/72} ≤ ∏_{v changed} ᾱ_v^{θ/72}`.

For the energies with a nonempty selected set (the subset terms and the folded energies of the
reduced hypotheses), **every** slot is changed in WP-R's formalization (`_hunch` of the
density-dc theorems: an unchanged slot needs `E = ∅`). So WP-S's `density_structured_theta_few`
(at most `70` changed slots) does not apply there, and the two-occurrence structure is absent.
The product bound is then the unit mixed `L^{72/θ}` moment of the selected law: the density
endpoint `θ` of the selected law, which is Part V data (`lem:density:coupled`, the density
moments of Part V).

* `lpNorm_rpow_div` and `lpNorm_one'`: the norms of `α^{θ/72}` and of `1`;
* `hpairs_of_mixedLpBound`: **`hpairs` from `MixedLpBound (|ρ|/‖ρ‖) (72/θ) 1`** and the fibre
  means `E_unif α_f(ω, v, ·) ≤ ᾱ_v`;
* `density_structured_theta_of_mixed`: WP-S's `density_structured_theta_of_pairs` with `hpairs`
  so discharged: `prop:record:density-structured` at `θ > 1`, at the base layer, from the density
  moment of the selected law.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured

variable {X XE Ω : Type*} [Fintype X] [Fintype XE] [Fintype Ω]

omit [Fintype X] [Fintype Ω] in
/-- The uniform `L^{72/θ}` norm of `α^{θ/72}` is `(E α)^{θ/72}` for `α ≥ 0`. -/
theorem lpNorm_rpow_div [Nonempty XE] {θ : ℝ} (hθ : 0 < θ) (α : XE → ℝ) (hα : ∀ x, 0 ≤ α x) :
    (FiniteLaw.uniform XE).lpNorm (72 / θ) (fun x => α x ^ (θ / 72)) =
      (FiniteLaw.uniform XE).expect α ^ (θ / 72) := by
  unfold FiniteLaw.lpNorm FiniteLaw.moment
  have hpt : ∀ x, |α x ^ (θ / 72)| ^ (72 / θ) = α x := by
    intro x
    rw [abs_of_nonneg (Real.rpow_nonneg (hα x) _), ← Real.rpow_mul (hα x)]
    have : θ / 72 * (72 / θ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  simp only [hpt]
  congr 1
  field_simp

omit [Fintype X] [Fintype Ω] in
/-- The uniform `L^p` norm of the constant `1` is one. -/
theorem lpNorm_one' [Nonempty XE] (q : ℝ) :
    (FiniteLaw.uniform XE).lpNorm q (fun _ => (1 : ℝ)) = 1 := by
  unfold FiniteLaw.lpNorm FiniteLaw.moment
  simp

omit [Fintype X] in
/-- **The label bound `hpairs` from the density moment of the selected law**: if the variation
law `|ρ|/‖ρ‖` of the selected labels has unit mixed `L^{72/θ}` (density endpoint `θ`) and the
fibre densities have uniform means at most `ᾱ_v`, then
`E_{P ⊗ |ρ|/‖ρ‖} ∏_{v changed} α_f^{θ/72} ≤ ∏_{v changed} ᾱ_v^{θ/72}`, for any index law `P`. -/
theorem hpairs_of_mixedLpBound [Nonempty XE] (P : FiniteLaw Ω) (ρ : (Slot → XE) → ℝ)
    (hρ : 0 < totalVariation ρ) (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (changed : Slot → Prop) [DecidablePred changed] {θ : ℝ} (hθ : 0 < θ) (αbar : Slot → ℝ)
    (hmix : MixedLpBound (variationLaw ρ hρ) (72 / θ) 1)
    (hmean : ∀ ω v, changed v → (FiniteLaw.uniform XE).expect (αf ω v) ≤ αbar v) :
    (P.product (variationLaw ρ hρ)).expect
        (fun p => ∏ v ∈ univ.filter changed, αf p.1 v (p.2 v) ^ (θ / 72)) ≤
      ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) := by
  rw [FiniteLaw.expect_product]
  have hω : ∀ ω, (variationLaw ρ hρ).expect
      (fun z => ∏ v ∈ univ.filter changed, αf ω v (z v) ^ (θ / 72)) ≤
        ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) := by
    intro ω
    set g : Slot → XE → ℝ := fun v x => if changed v then αf ω v x ^ (θ / 72) else 1 with hg
    have hprod : ∀ z : Slot → XE, ∏ v ∈ univ.filter changed, αf ω v (z v) ^ (θ / 72) =
        ∏ v, g v (z v) := by
      intro z
      rw [Finset.prod_filter]
    have hm := hmix g
    simp only [one_mul] at hm
    have hnorm : ∀ v, (FiniteLaw.uniform XE).lpNorm (72 / θ) (g v) =
        if changed v then (FiniteLaw.uniform XE).expect (αf ω v) ^ (θ / 72) else 1 := by
      intro v
      by_cases hv : changed v
      · simp only [hg, hv, ↓reduceIte]
        exact lpNorm_rpow_div hθ (αf ω v) (hαf ω v)
      · simp only [hg, hv, ↓reduceIte]
        exact lpNorm_one' _
    calc (variationLaw ρ hρ).expect
          (fun z => ∏ v ∈ univ.filter changed, αf ω v (z v) ^ (θ / 72))
        = (variationLaw ρ hρ).expect (fun z => ∏ v, g v (z v)) :=
          FiniteLaw.expect_congr _ hprod
      _ ≤ ∏ v, (FiniteLaw.uniform XE).lpNorm (72 / θ) (g v) := (le_abs_self _).trans hm
      _ = ∏ v ∈ univ.filter changed, (FiniteLaw.uniform XE).expect (αf ω v) ^ (θ / 72) := by
          rw [Finset.prod_filter]
          exact Finset.prod_congr rfl fun v _ => hnorm v
      _ ≤ ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) := by
          refine Finset.prod_le_prod₀ (fun v _ => Real.rpow_nonneg
            (FiniteLaw.expect_nonneg _ fun x => hαf ω v x) _) (fun v hv => ?_)
          rw [Finset.mem_filter] at hv
          exact Real.rpow_le_rpow (FiniteLaw.expect_nonneg _ fun x => hαf ω v x)
            (hmean ω v hv.2) (by positivity)
  calc P.expect (fun ω => (variationLaw ρ hρ).expect
        (fun z => ∏ v ∈ univ.filter changed, αf (ω, z).1 v ((ω, z).2 v) ^ (θ / 72)))
      ≤ P.expect (fun _ => ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72)) :=
        P.expect_mono fun ω => hω ω
    _ = ∏ v ∈ univ.filter changed, αbar v ^ (θ / 72) := FiniteLaw.expect_const _ _

/-- **`prop:record:density-structured` at `θ > 1` from the density moment of the selected law**:
WP-S's `density_structured_theta_of_pairs` with `hpairs` discharged by `hpairs_of_mixedLpBound`.
Its remaining inputs are WP-R's (the fibre bounds `hch`, `hun` and the density-dc comparison
`hdc`) and the Part V input `hmix` (unit mixed `L^{72/θ}` of `|ρ|/‖ρ‖`), with the fibre means
`hmean`. -/
theorem density_structured_theta_of_mixed [Nonempty XE] (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ : 0 < θ)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Y)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z,
      referenceEnergy μS (gt ω v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmix : ∀ hρ : 0 < totalVariation ρ, MixedLpBound (variationLaw ρ hρ) (72 / θ) 1)
    (hmean : ∀ ω v, changed v → (FiniteLaw.uniform XE).expect (αf ω v) ≤ αbar v)
    (hdc : |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * L ^ (-σ) * α) :
    |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y +
        Cdc * L ^ (-σ) * α) :=
  Sarkozy.TraceMixing.density_structured_theta_of_pairs μS hμS P ρ g gt changed hC0 ha hL hα hu
    hY hlow ξ αbar hξ hαbar hun αf hαf hch
    (fun hρ => hpairs_of_mixedLpBound P ρ hρ αf hαf changed hθ αbar (hmix hρ) hmean) hdc

end Sarkozy.EnvelopeInputs
