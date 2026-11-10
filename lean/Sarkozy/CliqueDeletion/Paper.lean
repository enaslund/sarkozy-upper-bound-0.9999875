module

public import Sarkozy.CliqueDeletion.Prefix
public import Sarkozy.ComparisonLawPaper.Paper

@[expose] public section

/-!
# The square-clique atoms of the paper: `DeletionInputs` proved (`lem:frontier:iidenergy`(ii))

`paper/sections/19_prefix.tex`, `lem:frontier:iidlocal`(ii)–(v) and `lem:frontier:iidenergy`(ii);
`paper/sections/30_density_moment_upgrade.tex`, `thm:density:iid-prefix`(a),(c).

At the square-clique atom `{p}` (`p ∈ 𝒫₁`, `p ≡ 1 (4)`, `p < P₄`) of the paper's construction the
reference law `μ_p` is V1's prefix law carried to the coordinate's modulus (`prefixAtomLaw`). This
file **proves** B2's `DeletionInputs μ_p acc_p 𝓔₆` (all 9 fields, no hypothesis) by deleting the
`ι`-closed query-coincidence event `symQueryEq 𝓔₆` (`Event.lean`):

* `prefixAtomLaw_flip`, `prefixAtomLaw_add`: invariance of `μ_p` under `ι` and the translations;
* `prefixAtomLaw_accept`: off the event, on the support, every query of `𝓔₆` is accepted at the
  prefix atom (`prefixAccepted`: `y - x ≠ 0`, of valuation `2j < e_p` with a square unit part);
* `prefixAtomLaw_mass`: the deleted mass equals that on `ℤ/p^{2𝔪}`, hence is at most
  `12 · 2^{-𝔪}` (`cliqueDeletion_ω_le`);
* **`cliqueDeletion blockOf q`**: the `DeletionInputs`;
* **`paperCliqueDeletion blockOf hW spec hC`**: the same, at the type of B2's field
  `ComparisonInputs.clique` and of K1's `MainFinal.ComparisonParts.clique` (for every block
  assignment, block specification and tail input: the prefix law does not depend on them).

**Relation to the paper.** `lem:frontier:iidenergy`(ii) deletes the exception `λ^ex_p` of `𝓔₆`
(the restriction to `queryEq`). For `p < 2¹⁶` (six-label law, `def:clique-law`) the support is
fixed by `ι`, so `symQueryEq = queryEq` almost surely and the deletion is the paper's. For
`p ≥ 2¹⁶` (independent draws, `thm:density:iid-prefix`) the paper's `E_p` is not symmetric at `ι`
("no symmetry of `E_p` is assumed"), but `DeletionInputs` requires the symmetry of `κ̄`
(`rem:cp:charging`(i)); the deletion here removes the `ι`-closure instead, of mass at most
`2η ≤ 12 · 2^{-𝔪}`, still accepted. The price bound is `ω ≤ 12 · 2^{-𝔪}` in place of the paper's
`η_𝔪 = 2^{1-𝔪} - 2^{-2𝔪}`; the paper's (d) of `thm:density:iid-prefix` budgets the same factor
`12 · 2^{-𝔪}` (sym. and skew parts of `E_p` separately).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.CliqueDeletion

open Sarkozy.PartV Sarkozy.PartVLaws Sarkozy.TheoremC Sarkozy.ComparisonLawPaper
  Sarkozy.CancellationSteps

/-- The support of an image law lies in the image of the support. -/
theorem exists_of_map_weight_ne_zero {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (φ : Ω → Ξ) {ξ : Ξ} (h : (μ.map φ).weight ξ ≠ 0) :
    ∃ ω, μ.weight ω ≠ 0 ∧ φ ω = ξ := by
  by_contra hcon
  push Not at hcon
  apply h
  show (∑ ω, if φ ω = ξ then μ.weight ω else 0) = 0
  refine sum_eq_zero fun ω _ => ?_
  split_ifs with hω
  · by_contra hne
    exact hcon ω hne hω
  · rfl

variable {B : Type} [DecidableEq B] (blockOf : PaperJ0 → B) (q : PrefixCoord)

/-- The atom label map `z ↦ (v ↦ (e_j(z_v))_j)` of the prefix atom. -/
noncomputable abbrev labelMap (z : Slot → ZMod (q.1.1 ^ (2 * digitPairs))) :
    Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inl q) :=
  fun v j => prefixRingEquiv blockOf q j (z v)

omit [DecidableEq B] in
theorem labelMap_eq_iff (a b : ZMod (q.1.1 ^ (2 * digitPairs))) :
    ((fun j => prefixRingEquiv blockOf q j a) :
        AtomLabel paperM0 (paperAtomMap blockOf) (.inl q)) =
      (fun j => prefixRingEquiv blockOf q j b) ↔ a = b := by
  constructor
  · intro h
    exact (prefixRingEquiv blockOf q (prefixPoint blockOf q)).injective
      (congrFun h (prefixPoint blockOf q))
  · rintro rfl
    rfl

omit [DecidableEq B] in
theorem symQueryEq_labelMap (z : Slot → ZMod (q.1.1 ^ (2 * digitPairs))) :
    symQueryEq MainAnchor.paperQueries (labelMap blockOf q z) ↔
      symQueryEq MainAnchor.paperQueries z := by
  unfold symQueryEq labelMap
  simp only [labelMap_eq_iff]

/-- **`μ_p` is invariant under `ι`.** -/
theorem prefixAtomLaw_flip
    (H : (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inl q)) → ℝ) :
    (prefixAtomLaw blockOf q).expect (fun z => H (z ∘ reservedCut.flip)) =
      (prefixAtomLaw blockOf q).expect H := by
  unfold prefixAtomLaw
  rw [singletonAtomLaw_expect, singletonAtomLaw_expect]
  exact prefixLaw_flip q.1.1 (fun z => H (fun v j => prefixRingEquiv blockOf q j (z v)))

/-- **`μ_p` is invariant under the common translations.** -/
theorem prefixAtomLaw_add (c : AtomLabel paperM0 (paperAtomMap blockOf) (.inl q))
    (H : (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inl q)) → ℝ) :
    (prefixAtomLaw blockOf q).expect (fun z => H (fun v => z v + c)) =
      (prefixAtomLaw blockOf q).expect H := by
  have h := prefixAtom_inv blockOf q (fun _ => 1) c (fun _ => ⟨1, by simp⟩) H
  have hfa : ∀ z : Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inl q),
      fiberAffine paperM0 (paperAtomMap blockOf) (fun _ => 1) c z = fun v => z v + c := by
    intro z
    funext v j
    show ((1 : (ZMod (paperM0 j.1))ˣ) : ZMod (paperM0 j.1)) * z v j + c j = z v j + c j
    simp
  simp only [hfa] at h
  exact h

/-- **The deleted mass at the atom equals that on `ℤ/p^{2𝔪}`.** -/
theorem prefixAtomLaw_mass :
    eventMass (prefixAtomLaw blockOf q) (symQueryEq MainAnchor.paperQueries) =
      eventMass (prefixLaw q.1.1) (symQueryEq MainAnchor.paperQueries) := by
  rw [eventMass_eq, eventMass_eq]
  unfold prefixAtomLaw
  rw [singletonAtomLaw_expect]
  refine FiniteLaw.expect_congr _ fun z => ?_
  have h := symQueryEq_labelMap blockOf q z
  by_cases hz : symQueryEq MainAnchor.paperQueries z
  · have hz' : symQueryEq MainAnchor.paperQueries (labelMap blockOf q z) := h.mpr hz
    simp only [hz, hz', ↓reduceIte]
  · have hz' : ¬ symQueryEq MainAnchor.paperQueries (labelMap blockOf q z) := fun h' => hz (h.mp h')
    simp only [hz, hz', ↓reduceIte]

theorem prefixCoord_ne_two : q.1.1 ≠ 2 := by
  intro h
  have := q.2
  rw [h] at this
  norm_num at this

theorem prefixCoord_mod_ne_three : q.1.1 % 4 ≠ 3 := by
  rw [q.2]
  norm_num

/-- **The deleted mass is at most `12 · 2^{-𝔪}`** (`lem:frontier:iidlocal`(iv),(v),
`thm:density:iid-prefix`(c)). -/
theorem prefixAtomLaw_mass_le :
    eventMass (prefixAtomLaw blockOf q) (symQueryEq MainAnchor.paperQueries) ≤
      12 / 2 ^ digitPairs := by
  rw [prefixAtomLaw_mass]
  exact prefixLaw_symQueryEq_le q.1.1 (prefixCoord_ne_two q) (prefixCoord_mod_ne_three q)

/-- **Acceptance off the deleted event** (`lem:frontier:iidlocal`(iv), `def:cp4`(a), (R5)): on the
support of `μ_p`, if no query of `𝓔₆` (nor its mirror image) has equal end labels, every query is
accepted at the prefix atom: `y - x ≠ 0`, `y - x = p^{2j} r` with `2j < e_p`, `r` a unit square. -/
theorem prefixAtomLaw_accept (z : Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inl q))
    (hz : (prefixAtomLaw blockOf q).weight z ≠ 0)
    (hG : ¬ symQueryEq MainAnchor.paperQueries z) (e : Chamber) :
    paperPrefixAccepted blockOf (.inl q) (z (MainAnchor.paperQueries.source e))
      (z (MainAnchor.paperQueries.target e)) := by
  unfold prefixAtomLaw singletonAtomLaw at hz
  obtain ⟨z', hz', rfl⟩ := exists_of_map_weight_ne_zero _ _ hz
  have hne : z' (MainAnchor.paperQueries.target e) ≠ z' (MainAnchor.paperQueries.source e) := by
    intro h
    apply not_queryEq_of_not_symQueryEq MainAnchor.paperQueries hG e
    show (fun j => prefixRingEquiv blockOf q j (z' (MainAnchor.paperQueries.source e))) =
      (fun j => prefixRingEquiv blockOf q j (z' (MainAnchor.paperQueries.target e)))
    rw [h]
  obtain ⟨jj, hjj, w, hw, hwu, hws⟩ :=
    prefixLaw_support_sub q.1.1 (prefixCoord_ne_two q) (prefixCoord_mod_ne_three q) hz' hne
  intro i
  have hi : i.1 = q.1 := paperAtomMap_inl blockOf i.2
  have hpp : paperPP i.1 = q.1.1 := by
    unfold paperPP
    rw [hi]
  have hep : paperEP i.1 = 2 * digitPairs := by
    unfold paperEP
    rw [hi]
    simp only [q.2, ↓reduceIte, prefixExponent]
  have hdiff : prefixRingEquiv blockOf q i (z' (MainAnchor.paperQueries.target e)) -
      prefixRingEquiv blockOf q i (z' (MainAnchor.paperQueries.source e)) =
      ((paperPP i.1 : ℕ) : ZMod (paperM0 i.1)) ^ (2 * jj) * prefixRingEquiv blockOf q i w := by
    rw [← map_sub, hw, map_mul, map_pow, map_natCast, hpp]
  refine ⟨?_, jj, by rw [hep]; omega, prefixRingEquiv blockOf q i w, hwu.map _, hws.map _, hdiff⟩
  rw [← map_sub]
  exact fun h => hne (sub_eq_zero.mp ((prefixRingEquiv blockOf q i).map_eq_zero_iff.mp h))

/-- **The square-clique atom's `DeletionInputs`** (`lem:frontier:iidenergy`(ii),
`lem:frontier:iidlocal`(iv),(v); for `p ≥ 2¹⁶` `thm:density:iid-prefix`(a),(c)), proved: the
deletion of the `ι`-closed coincidence event of `𝓔₆` from `μ_p`. -/
noncomputable def cliqueDeletion :
    DeletionInputs (prefixAtomLaw blockOf q) (paperPrefixAccepted blockOf (.inl q))
      MainAnchor.paperQueries :=
  ofEvent (prefixAtomLaw blockOf q) (symQueryEq MainAnchor.paperQueries)
    (lt_of_le_of_lt (prefixAtomLaw_mass_le blockOf q) twelve_div_lt_one)
    (prefixAtomLaw_flip blockOf q) (symQueryEq_flip MainAnchor.paperQueries)
    (prefixAtom_unif blockOf q) (prefixAtomLaw_add blockOf q)
    (symQueryEq_add MainAnchor.paperQueries) (prefixAtomLaw_accept blockOf q)

/-- The deleted mass `ω` of `cliqueDeletion`. -/
theorem cliqueDeletion_ω :
    (cliqueDeletion blockOf q).ω =
      eventMass (prefixAtomLaw blockOf q) (symQueryEq MainAnchor.paperQueries) := by
  unfold cliqueDeletion
  exact ofEvent_ω _ _ _ _ _ _ _ _ _

/-- **`ω ≤ 12 · 2^{-𝔪}`.** -/
theorem cliqueDeletion_ω_le : (cliqueDeletion blockOf q).ω ≤ 12 / 2 ^ digitPairs := by
  rw [cliqueDeletion_ω]
  exact prefixAtomLaw_mass_le blockOf q

variable [Fintype B]

/-- **B2's and K1's square-clique field, proved** (`lem:frontier:iidenergy`(ii),
`lem:frontier:iidlocal`(iv),(v)): at every square-clique atom of the paper's reference, for every
block assignment, block specification and tail input. -/
noncomputable def paperCliqueDeletion (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (q : PrefixCoord) :
    DeletionInputs ((v2Reference blockOf hW spec hC).μ₀ (.inl q))
      (paperPrefixAccepted blockOf (.inl q)) MainAnchor.paperQueries :=
  cliqueDeletion blockOf q

omit [Fintype B] in
theorem paperCliqueDeletion_ω_le (hW : Target.Weil) (spec : ∀ b, PaperBlockSpec blockOf b)
    (hC : TailInputsCorr PartV.P4) (q : PrefixCoord) :
    (paperCliqueDeletion blockOf hW spec hC q).ω ≤ 12 / 2 ^ digitPairs :=
  cliqueDeletion_ω_le blockOf q

end Sarkozy.CliqueDeletion
