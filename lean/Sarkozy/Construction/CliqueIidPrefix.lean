module

public import Sarkozy.Construction.CliqueLaw
public import Sarkozy.Construction.CliqueInvariance
public import Sarkozy.Construction.CliqueArithmetic

/-!
# The replacement prefix: independent clique draws at every slot

`thm:density:iid-prefix`(a), reflection positivity and marginals;
`paper/sections/30_density_moment_upgrade.tex`.

At a large prefix prime, the replacement prefix keeps the clique data, the random square clique
and the common square-affine map of `def:clique-law`. It draws the 72 labels conditionally
independently and uniformly from the clique, one per slot. The old prefix drew six chamber
labels and copied each to its slots.

* `slotIidLaw w ν` has shared data `ω ∼ w` and one label per slot, drawn independently from
  `ν ω`.
  - Its signed integral is the mixture `∑_ω w_ω · iidLaw (ν ω)` (`signedIntegral_slotIidLaw`).
  - So it is reflection positive at every cut of the slot array (`slotIidLaw_positive`), not
    only at the seven sorting cuts.
  - Its one-slot marginal is the mixture `∑_ω w_ω ν_ω` (`slotIidLaw_marginal`), the same as
    for the chamber pullback.
* `affineSlotLaw` and `cliqueIidLaw p ℓ` are the affine-randomized and square-clique instances.
  They are reflection positive at every cut and have uniform one-slot marginals
  (`cliqueIidLaw_positive`, `cliqueIidLaw_uniformMarginals`). The marginal proof reuses the
  chamber law's: both marginals are the same mixture.

These are the reflection-positivity, invariance and marginal assertions of
`thm:density:iid-prefix`(a). The invariance under `z ↦ (σ z_v + τ)_v`, for unit squares `σ`, is
`cliqueIidLaw_invariant`. The square property, that two distinct labels in the support differ
by `p^{2j}` times a unit square, is `cliqueIidLaw_support_sub`. Parts (b)–(d) are not formalized
here.
For draws from one digit pair, the moment statement (b) is `lem:density:clique-copies`
(`Moments/CliqueCopies.lean`), proved from `lem:density:clique36`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy

open ReflectionCut

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]

/-- Shared data and one label per slot: the base law on `Ω × (Slot → X)`. -/
noncomputable def slotBase (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) :
    FiniteLaw (Ω × (Slot → X)) where
  weight q := w.weight q.1 * ∏ v, (ν q.1).weight (q.2 v)
  nonneg q := mul_nonneg (w.nonneg _) (prod_nonneg fun _ _ => (ν q.1).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    have h1 : ∀ ω, ∑ y : Slot → X, ∏ v, (ν ω).weight (y v) = 1 := by
      intro ω
      have h := Fintype.prod_sum (fun (_ : Slot) (x : X) => (ν ω).weight x)
      simp only [(ν ω).total, prod_const_one] at h
      exact h.symm
    simp_rw [← mul_sum, h1, mul_one]
    exact w.total

/-- **Independent labels at every slot**, given shared data. -/
noncomputable def slotIidLaw (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) : FiniteLaw (Slot → X) :=
  (slotBase w ν).map Prod.snd

theorem expect_slotIidLaw (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (f : (Slot → X) → ℝ) :
    (slotIidLaw w ν).expect f =
      ∑ ω, w.weight ω * ∑ y : Slot → X, (∏ v, (ν ω).weight (y v)) * f y := by
  unfold slotIidLaw
  rw [FiniteLaw.expect_map]
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [slotBase, Function.comp_apply]
  ring

theorem signedIntegral_slotIidLaw (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) :
    signedIntegral (slotIidLaw w ν).weight = ∑ ω, w.weight ω • iidLaw (I := Slot) (ν ω) := by
  apply LinearMap.ext
  intro f
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_slotIidLaw, LinearMap.sum_apply]
  refine sum_congr rfl fun ω _ => ?_
  rfl

/-- **Reflection positivity at every cut of the slot array.** -/
theorem slotIidLaw_positive (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (c : ReflectionCut Slot) :
    c.Positive (signedIntegral (slotIidLaw w ν).weight) := by
  rw [signedIntegral_slotIidLaw]
  exact Positive.sum univ fun ω _ => (iidLaw_positive c (ν ω)).smul (w.nonneg ω)

theorem slotIidLaw_slotReflectionPositive (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) :
    SlotReflectionPositive (signedIntegral (slotIidLaw w ν).weight) :=
  fun c _ => slotIidLaw_positive w ν c

/-- The one-slot marginal of independent slot labels is the mixture of the label laws. -/
theorem slotIidLaw_marginal (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (v : Slot) (f : X → ℝ) :
    (slotIidLaw w ν).expect (fun z => f (z v)) = ∑ ω, w.weight ω * (ν ω).expect f := by
  rw [expect_slotIidLaw]
  refine sum_congr rfl fun ω _ => ?_
  congr 1
  have hprod : ∀ y : Slot → X, (∏ u, (ν ω).weight (y u)) * f (y v) =
      ∏ u, ((ν ω).weight (y u) * (if u = v then f (y u) else 1)) := by
    intro y
    rw [prod_mul_distrib, prod_ite_eq' univ v (fun u => f (y u))]
    simp only [mem_univ, ↓reduceIte]
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (u : Slot) (x : X) => (ν ω).weight x * (if u = v then f x else 1))]
  rw [prod_eq_single v]
  · unfold FiniteLaw.expect
    simp only [↓reduceIte]
  · intro u _ huv
    simp only [huv, ↓reduceIte, mul_one]
    exact (ν ω).total
  · intro h; exact absurd (mem_univ v) h

/-- A labelling of positive weight under independent slot labels has every label in the support
of one common label law. -/
theorem slotIidLaw_weight_ne_zero {w : FiniteLaw Ω} {ν : Ω → FiniteLaw X} {z : Slot → X}
    (hz : (slotIidLaw w ν).weight z ≠ 0) : ∃ ω, ∀ v, (ν ω).weight (z v) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hz
  show (∑ q, if q.2 = z then (slotBase w ν).weight q else 0) = 0
  apply Finset.sum_eq_zero
  intro q _
  split_ifs with hq
  · obtain ⟨v, hv⟩ := hcon q.1
    show w.weight q.1 * ∏ u, (ν q.1).weight (q.2 u) = 0
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hq]; exact hv), mul_zero]
  · rfl

/-- Independent slot labels and the chamber pullback have the same one-slot marginals. -/
theorem slotIidLaw_marginal_eq_chamber (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (v : Slot)
    (f : X → ℝ) :
    (slotIidLaw w ν).expect (fun z => f (z v)) = (chamberIidLaw w ν).expect (fun z => f (z v)) := by
  rw [slotIidLaw_marginal, chamberIidLaw_marginal]

variable {R D : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Fintype D]

/-- **The affine-randomized slot law**: data, multiplier and shift uniform; given them, one label
per slot, independently uniform on `s · C(d) + c`. -/
noncomputable def affineSlotLaw [Nonempty D] (S : Finset R) (hS : S.Nonempty)
    (C : D → Finset R) (hC : ∀ d, (C d).Nonempty) : FiniteLaw (Slot → R) :=
  have : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  slotIidLaw (FiniteLaw.uniform (AffineData (R := R) D S)) (affineLabelLaw S C hC)

theorem affineSlotLaw_positive [Nonempty D] (S : Finset R) (hS : S.Nonempty)
    (C : D → Finset R) (hC : ∀ d, (C d).Nonempty) (c : ReflectionCut Slot) :
    c.Positive (signedIntegral (affineSlotLaw S hS C hC).weight) :=
  slotIidLaw_positive _ _ c

/-- **Uniform marginals of the affine-randomized slot law**, for any sets `C(d)` and any set of
unit multipliers. -/
theorem affineSlotLaw_uniformMarginals [Nonempty D] (S : Finset R) (hS : S.Nonempty)
    (hSu : ∀ s ∈ S, IsUnit s) (C : D → Finset R) (hC : ∀ d, (C d).Nonempty) :
    HasUniformMarginals (affineSlotLaw S hS C hC) := by
  intro v f
  have h := affineChamberLaw_uniformMarginals S hS hSu C hC v f
  unfold affineChamberLaw at h
  unfold affineSlotLaw
  rw [slotIidLaw_marginal_eq_chamber]
  exact h

section Clique

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ)

/-- **The replacement prefix law** of `thm:density:iid-prefix`: the data, clique and common
square-affine map of `def:clique-law`, with one independent uniform clique label per slot. -/
noncomputable def cliqueIidLaw : FiniteLaw (Slot → ZMod (p ^ (2 * ℓ))) :=
  affineSlotLaw (unitSquares p ℓ) (unitSquares_nonempty p ℓ) (clique p ℓ) (clique_nonempty p ℓ)

/-- **`thm:density:iid-prefix`(a), reflection positivity**: at every cut of the slot array. -/
theorem cliqueIidLaw_positive (c : ReflectionCut Slot) :
    c.Positive (signedIntegral (cliqueIidLaw p ℓ).weight) :=
  affineSlotLaw_positive _ _ _ _ c

theorem cliqueIidLaw_slotReflectionPositive :
    SlotReflectionPositive (signedIntegral (cliqueIidLaw p ℓ).weight) :=
  fun c _ => cliqueIidLaw_positive p ℓ c

/-- **`thm:density:iid-prefix`(a), marginals**: the one-slot marginals are uniform. -/
theorem cliqueIidLaw_uniformMarginals : HasUniformMarginals (cliqueIidLaw p ℓ) :=
  affineSlotLaw_uniformMarginals _ _ (unitSquares_isUnit p ℓ) _ _

/-- **`thm:density:iid-prefix`(a), invariance**: the replacement prefix law is invariant under
`z ↦ (σ z_v + τ)_v` for every unit square `σ` and every `τ`. The proof is that of
`cliqueLaw_invariant`, with one label per slot. -/
theorem cliqueIidLaw_invariant {σ : ZMod (p ^ (2 * ℓ))} (hσ : σ ∈ unitSquares p ℓ)
    (τ : ZMod (p ^ (2 * ℓ))) (f : (Slot → ZMod (p ^ (2 * ℓ))) → ℝ) :
    (cliqueIidLaw p ℓ).expect (fun z => f (fun v => σ * z v + τ)) =
      (cliqueIidLaw p ℓ).expect f := by
  obtain ⟨σ', hσ'S, hσ'⟩ := unitSquares_inv ℓ hσ
  have hσσ' : σ * σ' = 1 := (mul_comm _ _).trans hσ'
  let h : ZMod (p ^ (2 * ℓ)) ≃ ZMod (p ^ (2 * ℓ)) :=
    { toFun := fun x => σ * x + τ
      invFun := fun x => σ' * (x - τ)
      left_inv := fun x => by
        change σ' * (σ * x + τ - τ) = x
        rw [add_sub_cancel_right, ← mul_assoc, hσ', one_mul]
      right_inv := fun x => by
        change σ * (σ' * (x - τ)) + τ = x
        rw [← mul_assoc, hσσ', one_mul, sub_add_cancel] }
  have hS : Nonempty (unitSquares p ℓ) :=
    ⟨⟨(unitSquares_nonempty p ℓ).choose, (unitSquares_nonempty p ℓ).choose_spec⟩⟩
  unfold cliqueIidLaw affineSlotLaw
  rw [expect_slotIidLaw, expect_slotIidLaw]
  have hinj : ∀ (s : ZMod (p ^ (2 * ℓ))), s ∈ unitSquares p ℓ → ∀ c : ZMod (p ^ (2 * ℓ)),
      Function.Injective fun x : ZMod (p ^ (2 * ℓ)) => s * x + c := by
    intro s hs c x x' hxx
    have hu := unitSquares_isUnit p ℓ s hs
    have : s * x = s * x' := by simpa using hxx
    exact hu.mul_left_cancel this
  have hfactor : ∀ q (x : ZMod (p ^ (2 * ℓ))),
      (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q).weight x =
      (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ)
        (affineShift ℓ hσ τ q)).weight (h x) := by
    intro q x
    set q' := affineShift ℓ hσ τ q
    have hq1 : q'.1 = q.1 := rfl
    have hq2 : (q'.2.1 : ZMod (p ^ (2 * ℓ))) = σ * q.2.1 := rfl
    have hq3 : q'.2.2 = σ * q.2.2 + τ := rfl
    have hmem : (x ∈ (clique p ℓ q.1).image fun y => (q.2.1 : ZMod (p ^ (2 * ℓ))) * y + q.2.2) ↔
        (h x ∈ (clique p ℓ q'.1).image fun y => (q'.2.1 : ZMod (p ^ (2 * ℓ))) * y + q'.2.2) := by
      rw [hq1, hq2, hq3]
      simp only [mem_image]
      constructor
      · rintro ⟨y, hy, hxe⟩
        exact ⟨y, hy, by rw [← hxe]; simp only [h, Equiv.coe_fn_mk]; ring⟩
      · rintro ⟨y, hy, hxe⟩
        refine ⟨y, hy, ?_⟩
        have : h ((q.2.1 : ZMod (p ^ (2 * ℓ))) * y + q.2.2) = h x := by
          simp only [h, Equiv.coe_fn_mk] at hxe ⊢; rw [← hxe]; ring
        exact h.injective this
    have hcard : ((clique p ℓ q.1).image fun y => (q.2.1 : ZMod (p ^ (2 * ℓ))) * y + q.2.2).card =
        ((clique p ℓ q'.1).image fun y => (q'.2.1 : ZMod (p ^ (2 * ℓ))) * y + q'.2.2).card := by
      rw [card_image_of_injective _ (hinj _ q.2.1.2 _),
        card_image_of_injective _ (hinj _ q'.2.1.2 _), hq1]
    unfold affineLabelLaw uniformOn
    by_cases hx : x ∈ (clique p ℓ q.1).image fun y => (q.2.1 : ZMod (p ^ (2 * ℓ))) * y + q.2.2
    · have hx' := hmem.mp hx
      simp only [hx, hx', ↓reduceIte, hcard]
    · have hx' : h x ∉ (clique p ℓ q'.1).image
          fun y => (q'.2.1 : ZMod (p ^ (2 * ℓ))) * y + q'.2.2 :=
        fun h' => hx (hmem.mpr h')
      simp only [hx, hx', ↓reduceIte]
  have hsub : ∀ q, ∑ y : Slot → ZMod (p ^ (2 * ℓ)),
      (∏ v, (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q).weight
        (y v)) * f (fun v => σ * y v + τ) =
      ∑ y : Slot → ZMod (p ^ (2 * ℓ)),
      (∏ v, (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ)
        (affineShift ℓ hσ τ q)).weight (y v)) * f y := by
    intro q
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl Slot) h) _ _ (fun y => ?_)
    simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.coe_refl, Function.comp_apply,
      CompTriple.comp_eq]
    congr 1
    exact prod_congr rfl fun v _ => hfactor q (y v)
  simp_rw [hsub]
  exact Fintype.sum_equiv (affineShift ℓ hσ τ) _ _ (fun _ => rfl)

/-- **`thm:density:iid-prefix`(a), square property**: two distinct labels in the support of the
replacement prefix law differ by `p^{2j} w` with `j < ℓ` and `w` a unit square of `ℤ/p^{2ℓ}ℤ`,
as in `lem:frontier:iidlocal`(iii). -/
theorem cliqueIidLaw_support_sub (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3)
    {z : Slot → ZMod (p ^ (2 * ℓ))} (hz : (cliqueIidLaw p ℓ).weight z ≠ 0) {u v : Slot}
    (huv : z u ≠ z v) :
    ∃ j : ℕ, j < ℓ ∧ ∃ w : ZMod (p ^ (2 * ℓ)),
      z u - z v = (p : ZMod (p ^ (2 * ℓ))) ^ (2 * j) * w ∧ IsUnit w ∧ IsSquare w := by
  unfold cliqueIidLaw affineSlotLaw at hz
  obtain ⟨q, hq⟩ := slotIidLaw_weight_ne_zero hz
  have hmem : ∀ t, ∃ x : Fin ℓ → Bool,
      z t = (q.2.1 : ZMod (p ^ (2 * ℓ))) * cliqueElt ℓ q.1 x + q.2.2 := by
    intro t
    have h := hq t
    unfold affineLabelLaw uniformOn at h
    simp only at h
    split_ifs at h with hm
    · obtain ⟨y, hy, hyz⟩ := mem_image.mp hm
      obtain ⟨x, _, rfl⟩ := mem_image.mp hy
      exact ⟨x, hyz.symm⟩
    · exact absurd rfl h
  obtain ⟨x, hx⟩ := hmem u
  obtain ⟨x', hx'⟩ := hmem v
  have hxx : x ≠ x' := by
    rintro rfl
    exact huv (hx.trans hx'.symm)
  rw [hx, hx']
  exact affine_cliqueElt_sub ℓ hp2 hp4 q.1 q.2.1.2 q.2.2 hxx

end Clique

end Sarkozy
