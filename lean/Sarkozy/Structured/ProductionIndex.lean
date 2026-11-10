module

public import Sarkozy.Structured.ThetaProduction

/-!
# The two-occurrence structure of the production arguments (`prop:density:production`)

`density_structured_theta` (`Sarkozy/Structured/ThetaProduction.lean`) takes two named
hypotheses, `slotOf` and `hindep`. This file derives both from one named property,
`ProductionTwoOccurrence`, which states exactly what the paper uses
(`paper/sections/31_density_induction_upgrade.tex:540–548`, proof of
`prop:density:production`): "After the complementary geometric means, a production query index
occurs in exactly two original slots. If their fibre-density means are `A, B` … Distinct query
indices are independent."

For queries `e : E` with source slots `src e` and target slots `tgt e` (in WP-FI's model,
`Queries.source` and `Queries.target`), the property has two parts:
* **(a) two occurrences.** The changed slots are exactly the `2|E|` sources and targets, and
  these slots are distinct.
* **(b) independence.** Under the sample law `P ⊗ |ρ|/‖ρ‖`, the pairs of fibre densities
  `(α_{f,src e}, α_{f,tgt e})` of distinct queries are independent: the expectation of
  `∏_e F_e(α_{f,src e}, α_{f,tgt e})` is the product of the expectations.

**What the index law gives and what is missing.** The coupled index law
(`def:hyb:coupled`; WP-FI's `IndexLaw`, `paperCoupledIndex`) is a product over the queries.
So the index part `ω` of the sample is independent across queries, and part (a) holds by the
injectivity and disjointness of the sources and targets (`Queries.hu`, `Queries.hw`, sources
in `V₊`, targets in `V₋`). Part (b) also needs the selected labels `z_{src e}, z_{tgt e}` of
distinct queries to be independent under `|ρ|/‖ρ‖`. The fibre density at a slot depends on
its label `z_v` through the fibre class. This holds if `|ρ|` is a product over the query
pairs. It does not follow from `def:hyb:coupled`; the paper obtains it from the step "after
the complementary geometric means", which is not formalized.

* `ProductionTwoOccurrence.slotOf`: the indexing `E × Bool ≃ {v // changed v}` from (a).
* `ProductionTwoOccurrence.hindep`: the hypothesis `hindep` of `density_structured_theta` from
  (b).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

variable {X XE Ω : Type*} [Fintype X] [Fintype XE] [Fintype Ω]

/-- **The two-occurrence structure of `prop:density:production`**
(`31_density_induction_upgrade.tex:540–548`). Part (a): the changed slots are exactly the
distinct sources `src e` and targets `tgt e` of the queries. Part (b): under the sample law
`P ⊗ |ρ|/‖ρ‖`, the pairs of fibre densities of distinct queries are independent. -/
structure ProductionTwoOccurrence (P : FiniteLaw Ω) (ρ : (Slot → XE) → ℝ)
    (αf : Ω → Slot → XE → ℝ) (changed : Slot → Prop) {E : Type*} [Fintype E]
    (src tgt : E → Slot) : Prop where
  src_inj : Function.Injective src
  tgt_inj : Function.Injective tgt
  src_ne_tgt : ∀ e e', src e ≠ tgt e'
  changed_iff : ∀ v, changed v ↔ (∃ e, src e = v) ∨ (∃ e, tgt e = v)
  indep : ∀ hρ : 0 < totalVariation ρ, ∀ F : E → ℝ → ℝ → ℝ,
    (P.product (variationLaw ρ hρ)).expect (fun p => ∏ e,
      F e (αf p.1 (src e) (p.2 (src e))) (αf p.1 (tgt e) (p.2 (tgt e)))) =
    ∏ e, (P.product (variationLaw ρ hρ)).expect (fun p =>
      F e (αf p.1 (src e) (p.2 (src e))) (αf p.1 (tgt e) (p.2 (tgt e))))

namespace ProductionTwoOccurrence

variable {P : FiniteLaw Ω} {ρ : (Slot → XE) → ℝ} {αf : Ω → Slot → XE → ℝ}
  {changed : Slot → Prop} {E : Type*} [Fintype E] {src tgt : E → Slot}

/-- The occurrence map `(e, true) ↦ src e`, `(e, false) ↦ tgt e`. -/
def occ (h : ProductionTwoOccurrence P ρ αf changed src tgt) (x : E × Bool) :
    {v // changed v} :=
  match x with
  | (e, true) => ⟨src e, (h.changed_iff _).mpr (Or.inl ⟨e, rfl⟩)⟩
  | (e, false) => ⟨tgt e, (h.changed_iff _).mpr (Or.inr ⟨e, rfl⟩)⟩

theorem occ_bijective (h : ProductionTwoOccurrence P ρ αf changed src tgt) :
    Function.Bijective h.occ := by
  constructor
  · rintro ⟨e, s⟩ ⟨e', s'⟩ hee
    cases s <;> cases s' <;> simp only [occ, Subtype.mk.injEq] at hee
    · rw [h.tgt_inj hee]
    · exact absurd hee.symm (h.src_ne_tgt e' e)
    · exact absurd hee (h.src_ne_tgt e e')
    · rw [h.src_inj hee]
  · rintro ⟨v, hv⟩
    rcases (h.changed_iff v).mp hv with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact ⟨(e, true), rfl⟩
    · exact ⟨(e, false), rfl⟩

/-- **`slotOf` from the two occurrences** (part (a)). -/
noncomputable def slotOf (h : ProductionTwoOccurrence P ρ αf changed src tgt) :
    E × Bool ≃ {v // changed v} :=
  Equiv.ofBijective h.occ h.occ_bijective

theorem slotOf_true (h : ProductionTwoOccurrence P ρ αf changed src tgt) (e : E) :
    (h.slotOf (e, true) : Slot) = src e := rfl

theorem slotOf_false (h : ProductionTwoOccurrence P ρ αf changed src tgt) (e : E) :
    (h.slotOf (e, false) : Slot) = tgt e := rfl

/-- **`hindep` from the independence** (part (b)): the hypothesis `hindep` of
`density_structured_theta` for the indexing `slotOf`. -/
theorem hindep (h : ProductionTwoOccurrence P ρ αf changed src tgt) (θ : ℝ) :
    ∀ hρ : 0 < totalVariation ρ,
      (P.product (variationLaw ρ hρ)).expect (fun p => ∏ e,
        (αf p.1 (h.slotOf (e, true)) (p.2 (h.slotOf (e, true))) ^ (θ / 72) *
          αf p.1 (h.slotOf (e, false)) (p.2 (h.slotOf (e, false))) ^ (θ / 72))) =
      ∏ e, (P.product (variationLaw ρ hρ)).expect (fun p =>
        αf p.1 (h.slotOf (e, true)) (p.2 (h.slotOf (e, true))) ^ (θ / 72) *
          αf p.1 (h.slotOf (e, false)) (p.2 (h.slotOf (e, false))) ^ (θ / 72)) :=
  fun hρ => h.indep hρ (fun _ x y => x ^ (θ / 72) * y ^ (θ / 72))

end ProductionTwoOccurrence

/-- **`density_structured_theta` from the two-occurrence structure**: the hypotheses `slotOf`
and `hindep` are replaced by `ProductionTwoOccurrence` (`prop:density:production`) for the
queries' sources and targets. -/
theorem density_structured_theta_production (μS : FiniteLaw (Slot → X))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (P : FiniteLaw Ω)
    (ρ : (Slot → XE) → ℝ) (g gt : Ω → Slot → XE → X → ℝ)
    (changed : Slot → Prop) [DecidablePred changed]
    {Y C0 a θ L α u Cdc σ : ℝ} (hC0 : 0 ≤ C0) (ha : 0 ≤ a) (hθ0 : 0 ≤ θ)
    (hθ2 : 2 * (θ / 72) ≤ 1)
    (hL : 0 < L) (hα : 0 < α) (hu : 0 ≤ u) (hY : 0 ≤ Y)
    (hlow : C0 * L ^ (-a) * α ^ θ < Y)
    (ξ αbar : Slot → ℝ) (hξ : ∀ v, 1 ≤ ξ v) (hαbar : ∀ v, 0 ≤ αbar v)
    (hun : ∀ v, ¬changed v → ∀ ω z, referenceEnergy μS (gt ω v z) ≤ Y)
    (αf : Ω → Slot → XE → ℝ) (hαf : ∀ ω v z, 0 ≤ αf ω v z)
    (hch : ∀ v, changed v → ∀ ω z,
      referenceEnergy μS (gt ω v z) ≤ (1 + u) * C0 * L ^ (-a) * ξ v ^ a * αf ω v z ^ θ)
    (hmean : ∀ hρ : 0 < totalVariation ρ, ∀ v, changed v →
      (P.product (variationLaw ρ hρ)).expect (fun p => αf p.1 v (p.2 v)) = αbar v)
    {E : Type*} [Fintype E] [DecidableEq E] (src tgt : E → Slot)
    (hprod : ProductionTwoOccurrence P ρ αf changed src tgt)
    (hdc : |structuredEnergy μS P ρ g - structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * L ^ (-σ) * α) :
    |structuredEnergy μS P ρ g| ≤
      totalVariation ρ * ((1 + u) * mainPrice ξ αbar changed a θ α * Y +
        Cdc * L ^ (-σ) * α) := by
  exact density_structured_theta μS hμS P ρ g gt changed hC0 ha hθ0 hθ2 hL hα hu hY hlow ξ αbar
    hξ hαbar hun αf hαf hch hmean hprod.slotOf (hprod.hindep θ) hdc

end Sarkozy.Structured
