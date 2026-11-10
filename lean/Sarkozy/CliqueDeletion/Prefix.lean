module

public import Sarkozy.CliqueDeletion.Event
public import Sarkozy.PartVLaws.InvariantBackground
public import Sarkozy.PartVLaws.FiberAssembly
public import Sarkozy.DensityMoments.PrefixEqualityEvents
public import Sarkozy.Construction.CliqueException
public import Sarkozy.MainAnchor.PaperQueries

@[expose] public section

/-!
# The four properties of the prefix law used by the deletion

`paper/sections/19_prefix.tex`, `lem:frontier:iidlocal`(ii)–(v);
`paper/sections/30_density_moment_upgrade.tex`, `thm:density:iid-prefix`(a),(c).

V1's prefix law `PartV.prefixLaw p` (`thm:density:iid-prefix`: the independent-draw clique law
`cliqueIidLaw` for `p ≥ 2¹⁶`, the square-clique law `cliqueLaw` of `def:clique-law` below), on
`ℤ/p^{2𝔪}`, `𝔪 = 8192`, for a prime `p ≡ 1 (4)`:

* `prefixLaw_flip`: **invariance under the reserved reflection `ι`** (`z ↦ z ∘ ι`). For the
  independent-draw law this is the slot exchangeability (`cliqueIidLaw_perm_inv`); for the
  six-label law every labelling of the support is fixed by `ι`, since `ι` keeps the first
  chamber coordinate (`chamberIidLaw_flip`; `lem:frontier:iidlocal`(iv), "fixed samplewise by
  `ι`").
* `prefixLaw_add`: invariance under the common translations (`lem:frontier:iidlocal`(ii), from
  `prefixLaw_invariant`).
* `prefixLaw_support_sub`: **two distinct labels of a labelling in the support differ by
  `p^{2j} w`, `j < 𝔪`, `w` a unit square** (`lem:frontier:iidlocal`(iii),
  `thm:density:iid-prefix`(a)); for the six-label law this is new here
  (`cliqueLaw_support_sub`, through `chamberIidLaw_weight_ne_zero`).
* `prefixLaw_queryEq_le`: **the exception of the six queries `𝓔₆` has mass at most `6 · 2^{-𝔪}`**
  (`lem:frontier:iidlocal`(iv),(v); `thm:density:iid-prefix`(c): `η = 1 - (1 - 2^{-𝔪})⁶`).
* `prefixLaw_symQueryEq_le`: its `ι`-closure has mass at most `12 · 2^{-𝔪}`, and
  `prefixLaw_symQueryEq_lt_one`: less than one.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.CliqueDeletion

open Sarkozy.PartV Sarkozy.PartVLaws Sarkozy.DensityMoments Sarkozy.TheoremC

/-! ## Chamber pullbacks under `ι` -/

/-- The reserved reflection keeps the first chamber coordinate. -/
theorem firstChamber_flip : ∀ v : Slot, firstChamber (reservedCut.flip v) = firstChamber v := by
  decide

/-- **A chamber pullback is invariant under `ι`**: its labellings are fixed by `ι`. -/
theorem chamberIidLaw_flip {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (H : (Slot → X) → ℝ) :
    (chamberIidLaw w ν).expect (fun z => H (z ∘ reservedCut.flip)) =
      (chamberIidLaw w ν).expect H := by
  rw [expect_chamberIidLaw, expect_chamberIidLaw]
  have hy : ∀ y : Chamber → X, (y ∘ firstChamber) ∘ reservedCut.flip = y ∘ firstChamber := by
    intro y
    funext v
    simp only [Function.comp_apply, firstChamber_flip]
  simp only [hy]

/-- A labelling of positive weight under a chamber pullback has every label in the support of one
common label law. -/
theorem chamberIidLaw_weight_ne_zero {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    {w : FiniteLaw Ω} {ν : Ω → FiniteLaw X} {z : Slot → X}
    (hz : (chamberIidLaw w ν).weight z ≠ 0) : ∃ ω, ∀ v, (ν ω).weight (z v) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hz
  show (∑ q, if q.2 ∘ firstChamber = z then (chamberBase w ν).weight q else 0) = 0
  apply Finset.sum_eq_zero
  intro q _
  split_ifs with hq
  · obtain ⟨v, hv⟩ := hcon q.1
    have hv' : (ν q.1).weight (q.2 (firstChamber v)) = 0 := by
      rw [show q.2 (firstChamber v) = z v from congrFun hq v]
      exact hv
    show w.weight q.1 * ∏ i, (ν q.1).weight (q.2 i) = 0
    rw [Finset.prod_eq_zero (Finset.mem_univ (firstChamber v)) hv', mul_zero]
  · rfl

section Clique

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ)

/-- **`lem:frontier:iidlocal`(iii) on the support of the six-label law**: two distinct labels
differ by `p^{2j} w` with `j < ℓ` and `w` a unit square of `ℤ/p^{2ℓ}ℤ`. -/
theorem cliqueLaw_support_sub (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3)
    {z : Slot → ZMod (p ^ (2 * ℓ))} (hz : (cliqueLaw p ℓ).weight z ≠ 0) {u v : Slot}
    (huv : z u ≠ z v) :
    ∃ j : ℕ, j < ℓ ∧ ∃ w : ZMod (p ^ (2 * ℓ)),
      z u - z v = (p : ZMod (p ^ (2 * ℓ))) ^ (2 * j) * w ∧ IsUnit w ∧ IsSquare w := by
  unfold cliqueLaw affineChamberLaw at hz
  obtain ⟨q, hq⟩ := chamberIidLaw_weight_ne_zero hz
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

/-! ## The prefix law -/

section Prefix

variable (p : ℕ) [Fact p.Prime]

/-- **The prefix law is invariant under `ι`** (`thm:density:iid-prefix`(a); for `p < 2¹⁶`,
`lem:frontier:iidlocal`(iv): the labellings are fixed by `ι`). -/
theorem prefixLaw_flip (H : (Slot → ZMod (p ^ (2 * digitPairs))) → ℝ) :
    (prefixLaw p).expect (fun z => H (z ∘ reservedCut.flip)) = (prefixLaw p).expect H := by
  unfold prefixLaw
  split_ifs
  · exact cliqueIidLaw_perm_inv p digitPairs reservedCut.flip H
  · unfold cliqueLaw affineChamberLaw
    exact chamberIidLaw_flip _ _ H

/-- **The prefix law is invariant under the common translations** (`lem:frontier:iidlocal`(ii)). -/
theorem prefixLaw_add (c : ZMod (p ^ (2 * digitPairs)))
    (H : (Slot → ZMod (p ^ (2 * digitPairs))) → ℝ) :
    (prefixLaw p).expect (fun z => H (fun v => z v + c)) = (prefixLaw p).expect H := by
  have h := prefixLaw_invariant p 1 c ⟨1, by simp⟩ H
  simpa only [Units.val_one, one_mul] using h

/-- **The square property on the support of the prefix law** (`lem:frontier:iidlocal`(iii),
`thm:density:iid-prefix`(a)). -/
theorem prefixLaw_support_sub (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3)
    {z : Slot → ZMod (p ^ (2 * digitPairs))} (hz : (prefixLaw p).weight z ≠ 0) {u v : Slot}
    (huv : z u ≠ z v) :
    ∃ j : ℕ, j < digitPairs ∧ ∃ w : ZMod (p ^ (2 * digitPairs)),
      z u - z v = (p : ZMod (p ^ (2 * digitPairs))) ^ (2 * j) * w ∧ IsUnit w ∧ IsSquare w := by
  unfold prefixLaw at hz
  split_ifs at hz
  · exact cliqueIidLaw_support_sub p digitPairs hp2 hp4 hz huv
  · exact cliqueLaw_support_sub p digitPairs hp2 hp4 hz huv

theorem paperQueries_source_eq (j : Chamber) : MainAnchor.paperQueries.source j = querySource j :=
  rfl

theorem paperQueries_target_eq (j : Chamber) : MainAnchor.paperQueries.target j = queryTarget j :=
  reservedCut.flip_flip _

/-- **The exception of `𝓔₆` has mass at most `6 · 2^{-𝔪}`** (`lem:frontier:iidlocal`(iv),(v):
exactly `2^{-𝔪}` for the six-label law, by the union bound here; `thm:density:iid-prefix`(c):
`η = 1 - (1 - 2^{-𝔪})⁶ ≤ 6 · 2^{-𝔪}` for the independent-draw law). -/
theorem prefixLaw_queryEq_le (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) :
    eventMass (prefixLaw p) (queryEq MainAnchor.paperQueries) ≤ 6 / 2 ^ digitPairs := by
  unfold prefixLaw
  split_ifs
  · -- the independent-draw law: M1's `deleted_mass`
    have hd := deleted_mass p digitPairs
    rw [sum_sub_distrib, (cliqueIidLaw p digitPairs).total] at hd
    have hE : eventMass (cliqueIidLaw p digitPairs) (queryEq MainAnchor.paperQueries) =
        ∑ z, deletedWeight p digitPairs z := by
      unfold eventMass restrictW deletedWeight
      refine sum_congr rfl fun z _ => ?_
      have hq : queryEq MainAnchor.paperQueries z ↔ QueryEq z := by
        unfold queryEq QueryEq
        simp only [paperQueries_source_eq, paperQueries_target_eq]
      simp only [hq]
    rw [hE]
    have h6 := prefixEta_le digitPairs
    have : ∑ z, deletedWeight p digitPairs z = prefixEta digitPairs := by linarith
    rw [this]
    calc prefixEta digitPairs ≤ 6 * (1 / (2 : ℝ) ^ digitPairs) := h6
      _ = 6 / 2 ^ digitPairs := by ring
  · -- the six-label law: the union bound `cliqueLaw_exception_le`
    rw [eventMass_eq]
    have h := cliqueLaw_exception_le (p := p) digitPairs hp2 hp4 (n := 6)
      (fun k => MainAnchor.paperQueries.source k) (fun k => MainAnchor.paperQueries.target k)
      (by decide)
    have h6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
    rw [h6] at h
    refine le_trans (le_of_eq (FiniteLaw.expect_congr _ fun z => ?_)) h
    by_cases hz : queryEq MainAnchor.paperQueries z
    · have hz' : ∃ k : Fin 6, z (MainAnchor.paperQueries.source k) =
          z (MainAnchor.paperQueries.target k) := hz
      simp only [hz, hz', ↓reduceIte]
    · have hz' : ¬ ∃ k : Fin 6, z (MainAnchor.paperQueries.source k) =
          z (MainAnchor.paperQueries.target k) := hz
      simp only [hz, hz', ↓reduceIte]

/-- `12 · 2^{-𝔪} < 1`. -/
theorem twelve_div_lt_one : (12 : ℝ) / 2 ^ digitPairs < 1 := by
  have h16 : (16 : ℝ) ≤ 2 ^ digitPairs := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ digitPairs := pow_le_pow_right₀ (by norm_num) (by unfold digitPairs; norm_num)
  rw [div_lt_one (by positivity)]
  linarith

/-- **The `ι`-closed exception of `𝓔₆` has mass at most `12 · 2^{-𝔪}`.** -/
theorem prefixLaw_symQueryEq_le (hp2 : p ≠ 2) (hp4 : p % 4 ≠ 3) :
    eventMass (prefixLaw p) (symQueryEq MainAnchor.paperQueries) ≤ 12 / 2 ^ digitPairs := by
  have h := eventMass_symQueryEq_le MainAnchor.paperQueries (prefixLaw p) (prefixLaw_flip p)
  have h6 := prefixLaw_queryEq_le p hp2 hp4
  calc eventMass (prefixLaw p) (symQueryEq MainAnchor.paperQueries)
      ≤ 2 * eventMass (prefixLaw p) (queryEq MainAnchor.paperQueries) := h
    _ ≤ 2 * (6 / 2 ^ digitPairs) := by linarith
    _ = 12 / 2 ^ digitPairs := by ring

end Prefix

end Sarkozy.CliqueDeletion
