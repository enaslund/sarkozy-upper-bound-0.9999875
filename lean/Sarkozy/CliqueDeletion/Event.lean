module

public import Sarkozy.ComparisonLawPaper.Deletion

@[expose] public section

/-!
# The deletion of an event, as `DeletionInputs` (`lem:frontier:iidenergy`(ii))

`paper/sections/19_prefix.tex`, `lem:frontier:iidlocal`(iv) and `lem:frontier:iidenergy`(ii): at a
square-clique atom the comparison law is `ν_p = λ_p - λ^ex_p`, where the exception `λ^ex_p` is the
restriction of `λ_p` to an event `𝖤` on which some query has equal labels.

This file builds B2's `DeletionInputs μ acc Q` from **any** event `G` of a reference law `μ`:

* `restrictW μ G` (the restriction `1_G μ`), `eventMass μ G` (its mass `ω = μ(G)`);
* `kappa μ G` (the normalized restriction `κ̄ = 1_G μ / ω`, or `μ` itself if `ω = 0`);
* `nu μ G hω` (the normalized retained law `ν̄ = 1_{Gᶜ} μ / (1 - ω)`);
* **`ofEvent`**: `DeletionInputs μ acc Q` with `ω = μ(G)`, from
  - `ω < 1`;
  - invariance of `μ` under the reflection `ι` (`z ↦ z ∘ ι`) and of `G` under `ι`
    (this gives the symmetry of `κ̄` at `ι`);
  - invariance of `μ` and `G` under the common translations `z ↦ z + c`, and uniform marginals
    of `μ` (this gives the uniform one-slot marginals of `κ̄`);
  - acceptance of every query off `G` on the support of `μ`.
* The event of the square-clique atoms: `queryEq Q` (some query has equal end labels) and its
  `ι`-closure **`symQueryEq Q`** (some query or its mirror image has equal end labels), which is
  invariant under `ι` and under translations (`symQueryEq_flip`, `symQueryEq_add`), with
  `μ(symQueryEq Q) ≤ 2 μ(queryEq Q)` for an `ι`-invariant `μ` (`eventMass_symQueryEq_le`).

Why the `ι`-closure: for the six-label square-clique law of `def:clique-law` every labelling of
the support is fixed by `ι`, so `symQueryEq` and `queryEq` agree almost surely. For the
independent-draw prefix of `thm:density:iid-prefix` (`p ≥ 2¹⁶`) the paper's exception `E_p`
(restriction to `queryEq`) is not symmetric at `ι` ("no symmetry of `E_p` is assumed"), while
`DeletionInputs` asks `κ̄` to be symmetric; the restriction to `symQueryEq` is symmetric and
removes at most twice the mass.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.CliqueDeletion

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.ComparisonLawPaper

variable {X : Type} [Fintype X]

/-! ## The restriction to an event -/

section Event

variable (μ : FiniteLaw (Slot → X)) (G : (Slot → X) → Prop) [DecidablePred G]

/-- The restriction `1_G μ` of `μ` to the event `G` (`lem:frontier:iidlocal`(iv)). -/
noncomputable def restrictW (z : Slot → X) : ℝ := if G z then μ.weight z else 0

/-- The mass `ω = μ(G)` of the restriction. -/
noncomputable def eventMass : ℝ := ∑ z, restrictW μ G z

theorem restrictW_nonneg (z : Slot → X) : 0 ≤ restrictW μ G z := by
  unfold restrictW
  split_ifs
  · exact μ.nonneg z
  · exact le_rfl

theorem eventMass_nonneg : 0 ≤ eventMass μ G := sum_nonneg fun z _ => restrictW_nonneg μ G z

theorem sum_restrictW_mul (f : (Slot → X) → ℝ) :
    ∑ z, restrictW μ G z * f z = μ.expect (fun z => if G z then f z else 0) := by
  unfold FiniteLaw.expect restrictW
  refine sum_congr rfl fun z _ => ?_
  by_cases h : G z <;> simp [h]

/-- `μ(G)` as an expectation. -/
theorem eventMass_eq : eventMass μ G = μ.expect (fun z => if G z then 1 else 0) := by
  rw [← sum_restrictW_mul]
  unfold eventMass
  simp

theorem weight_eq_zero_of_eventMass {z : Slot → X} (h : eventMass μ G = 0) (hz : G z) :
    μ.weight z = 0 := by
  have h0 := (sum_eq_zero_iff_of_nonneg fun z _ => restrictW_nonneg μ G z).mp h z (mem_univ z)
  unfold restrictW at h0
  simpa only [hz, ↓reduceIte] using h0

/-- **The normalized restriction** `κ̄ = 1_G μ / μ(G)`; `μ` itself if `μ(G) = 0` (then it is not
used: the deleted mass is zero). -/
noncomputable def kappa : FiniteLaw (Slot → X) :=
  if h : eventMass μ G = 0 then μ else
    { weight := fun z => restrictW μ G z / eventMass μ G
      nonneg := fun z => div_nonneg (restrictW_nonneg μ G z) (eventMass_nonneg μ G)
      total := by
        rw [← sum_div]
        exact div_self h }

theorem kappa_of_eq_zero (h : eventMass μ G = 0) : kappa μ G = μ := by
  unfold kappa
  simp only [h, ↓reduceDIte]

theorem kappa_weight (h : eventMass μ G ≠ 0) (z : Slot → X) :
    (kappa μ G).weight z = restrictW μ G z / eventMass μ G := by
  unfold kappa
  simp only [h, ↓reduceDIte]

theorem kappa_expect (h : eventMass μ G ≠ 0) (f : (Slot → X) → ℝ) :
    (kappa μ G).expect f = μ.expect (fun z => if G z then f z else 0) / eventMass μ G := by
  rw [← sum_restrictW_mul, sum_div]
  unfold FiniteLaw.expect
  refine sum_congr rfl fun z _ => ?_
  rw [kappa_weight μ G h]
  ring

/-- **The normalized retained law** `ν̄ = 1_{Gᶜ} μ / (1 - μ(G))`. -/
noncomputable def nu (hω : eventMass μ G < 1) : FiniteLaw (Slot → X) where
  weight z := (if G z then 0 else μ.weight z) / (1 - eventMass μ G)
  nonneg z := div_nonneg (by split_ifs; exacts [le_rfl, μ.nonneg z]) (by linarith)
  total := by
    rw [← sum_div]
    have hs : ∑ z, (if G z then 0 else μ.weight z) = 1 - eventMass μ G := by
      rw [← μ.total]
      unfold eventMass restrictW
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun z _ => ?_
      split_ifs <;> ring
    rw [hs]
    exact div_self (by linarith)

theorem nu_weight (hω : eventMass μ G < 1) (z : Slot → X) :
    (nu μ G hω).weight z = (if G z then 0 else μ.weight z) / (1 - eventMass μ G) := rfl

/-- `(1 - ω) ν̄ = μ - ω κ̄`. -/
theorem nu_decomp (hω : eventMass μ G < 1) (z : Slot → X) :
    (1 - eventMass μ G) * (nu μ G hω).weight z =
      μ.weight z - eventMass μ G * (kappa μ G).weight z := by
  have h1 : (1 - eventMass μ G) ≠ 0 := by linarith
  rw [nu_weight, mul_div_cancel₀ _ h1]
  by_cases h : eventMass μ G = 0
  · rw [h, zero_mul, sub_zero]
    split_ifs with hz
    · exact (weight_eq_zero_of_eventMass μ G h hz).symm
    · rfl
  · rw [kappa_weight μ G h, mul_div_cancel₀ _ h]
    unfold restrictW
    split_ifs <;> ring

/-- **The normalized restriction is symmetric at `ι`** if `μ` and `G` are invariant under `ι`. -/
theorem kappa_symmetric
    (hflip : ∀ H : (Slot → X) → ℝ, μ.expect (fun z => H (z ∘ reservedCut.flip)) = μ.expect H)
    (hG : ∀ z, G (z ∘ reservedCut.flip) ↔ G z) :
    IsSymmetricAt reservedCut (signedIntegral (kappa μ G).weight) := by
  unfold IsSymmetricAt
  apply LinearMap.ext
  intro f
  rw [reflect_apply, ← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral]
  by_cases h : eventMass μ G = 0
  · rw [kappa_of_eq_zero μ G h]
    exact hflip f
  · rw [kappa_expect μ G h, kappa_expect μ G h]
    congr 1
    have := hflip (fun z => if G z then f z else 0)
    refine Eq.trans ?_ this
    refine FiniteLaw.expect_congr _ fun z => ?_
    simp only [hG z]

/-- **The normalized restriction has uniform one-slot marginals** if `μ` has, and `μ` and `G` are
invariant under the common translations. -/
theorem kappa_unif [Nonempty X] [AddCommGroup X] (hunif : HasUniformMarginals μ)
    (htrans : ∀ (c : X) (H : (Slot → X) → ℝ), μ.expect (fun z => H (fun v => z v + c)) = μ.expect H)
    (hG : ∀ (c : X) z, G (fun v => z v + c) ↔ G z) :
    HasUniformMarginals (kappa μ G) := by
  intro v f
  by_cases h : eventMass μ G = 0
  · rw [kappa_of_eq_zero μ G h]
    exact hunif v f
  · rw [kappa_expect μ G h]
    -- translate by every `c` and average
    have hc : ∀ c : X, μ.expect (fun z => if G z then f (z v) else 0) =
        μ.expect (fun z => if G z then f (z v + c) else 0) := by
      intro c
      have := htrans c (fun z => if G z then f (z v) else 0)
      simp only [hG c] at this
      exact this.symm
    have hsum : (Fintype.card X : ℝ) * μ.expect (fun z => if G z then f (z v) else 0) =
        (∑ x, f x) * eventMass μ G := by
      rw [← nsmul_eq_mul, ← card_univ, ← sum_const, sum_congr rfl fun c _ => hc c, eventMass_eq]
      unfold FiniteLaw.expect
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun z _ => ?_
      by_cases hz : G z
      · simp only [hz, ↓reduceIte, mul_one]
        have hs := Equiv.sum_comp (Equiv.addLeft (z v)) f
        simp only [Equiv.coe_addLeft] at hs
        rw [← mul_sum, hs]
        ring
      · simp [hz]
    have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [FiniteLaw.expect_uniform, div_eq_iff h]
    field_simp
    linarith

/-- **The deletion of the event `G`** (`lem:frontier:iidenergy`(ii), `lem:frontier:iidlocal`(iv)):
`κ̄ = 1_G μ / μ(G)`, `ω = μ(G)`, `ν̄ = 1_{Gᶜ} μ / (1 - ω)`. -/
noncomputable def ofEvent [DecidableEq X] [Nonempty X] {acc : X → X → Prop} {E : Type}
    {Q : Queries E} [AddCommGroup X]
    (hω : eventMass μ G < 1)
    (hflip : ∀ H : (Slot → X) → ℝ, μ.expect (fun z => H (z ∘ reservedCut.flip)) = μ.expect H)
    (hGflip : ∀ z, G (z ∘ reservedCut.flip) ↔ G z)
    (hunif : HasUniformMarginals μ)
    (htrans : ∀ (c : X) (H : (Slot → X) → ℝ), μ.expect (fun z => H (fun v => z v + c)) = μ.expect H)
    (hGtrans : ∀ (c : X) z, G (fun v => z v + c) ↔ G z)
    (hacc : ∀ z, μ.weight z ≠ 0 → ¬ G z → ∀ e, acc (z (Q.source e)) (z (Q.target e))) :
    DeletionInputs μ acc Q where
  κ := kappa μ G
  ω := eventMass μ G
  ω_nonneg := eventMass_nonneg μ G
  ω_lt_one := hω
  ν := nu μ G hω
  decomp := nu_decomp μ G hω
  κ_sym := kappa_symmetric μ G hflip hGflip
  κ_unif := kappa_unif μ G hunif htrans hGtrans
  accept z hz := by
    rw [nu_weight] at hz
    have hG : ¬ G z := fun h => hz (by simp [h])
    have hμ : μ.weight z ≠ 0 := fun h => hz (by simp [hG, h])
    exact hacc z hμ hG

/-- The deleted mass of `ofEvent` is `μ(G)`. -/
theorem ofEvent_ω [DecidableEq X] [Nonempty X] {acc : X → X → Prop} {E : Type}
    {Q : Queries E} [AddCommGroup X] (hω : eventMass μ G < 1)
    (hflip : ∀ H : (Slot → X) → ℝ, μ.expect (fun z => H (z ∘ reservedCut.flip)) = μ.expect H)
    (hGflip : ∀ z, G (z ∘ reservedCut.flip) ↔ G z)
    (hunif : HasUniformMarginals μ)
    (htrans : ∀ (c : X) (H : (Slot → X) → ℝ), μ.expect (fun z => H (fun v => z v + c)) = μ.expect H)
    (hGtrans : ∀ (c : X) z, G (fun v => z v + c) ↔ G z)
    (hacc : ∀ z, μ.weight z ≠ 0 → ¬ G z → ∀ e, acc (z (Q.source e)) (z (Q.target e))) :
    (ofEvent μ G hω hflip hGflip hunif htrans hGtrans hacc).ω = eventMass μ G := rfl

end Event

/-! ## The query events -/

section Queries

variable [DecidableEq X] {E : Type} [Fintype E] (Q : Queries E)

/-- Some query has equal end labels: the event `𝖤` of `lem:frontier:iidlocal`(iv) for `𝓔₆`. -/
def queryEq (z : Slot → X) : Prop := ∃ e, z (Q.source e) = z (Q.target e)

/-- **The `ι`-closure of the query event**: some query, or its mirror image under `ι`, has equal
end labels. -/
def symQueryEq (z : Slot → X) : Prop :=
  ∃ e, z (Q.source e) = z (Q.target e) ∨
    z (reservedCut.flip (Q.source e)) = z (reservedCut.flip (Q.target e))

instance : DecidablePred (queryEq (X := X) Q) := fun _ => by
  unfold queryEq
  infer_instance

instance : DecidablePred (symQueryEq (X := X) Q) := fun _ => by
  unfold symQueryEq
  infer_instance

omit [Fintype X] [DecidableEq X] [Fintype E] in
theorem symQueryEq_flip (z : Slot → X) :
    symQueryEq Q (z ∘ reservedCut.flip) ↔ symQueryEq Q z := by
  unfold symQueryEq
  simp only [Function.comp_apply, reservedCut.flip_flip]
  exact exists_congr fun _ => or_comm

omit [Fintype X] [DecidableEq X] [Fintype E] in
theorem symQueryEq_add [AddCommGroup X] (c : X) (z : Slot → X) :
    symQueryEq Q (fun v => z v + c) ↔ symQueryEq Q z := by
  unfold symQueryEq
  simp only [add_left_inj]

omit [Fintype X] [DecidableEq X] [Fintype E] in
theorem not_queryEq_of_not_symQueryEq {z : Slot → X} (h : ¬ symQueryEq Q z) (e : E) :
    z (Q.source e) ≠ z (Q.target e) := fun h' => h ⟨e, Or.inl h'⟩

/-- **`μ(symQueryEq) ≤ 2 μ(queryEq)`** for an `ι`-invariant law. -/
theorem eventMass_symQueryEq_le (μ : FiniteLaw (Slot → X))
    (hflip : ∀ H : (Slot → X) → ℝ, μ.expect (fun z => H (z ∘ reservedCut.flip)) = μ.expect H) :
    eventMass μ (symQueryEq Q) ≤ 2 * eventMass μ (queryEq Q) := by
  rw [eventMass_eq, eventMass_eq]
  have hle : ∀ z : Slot → X, (if symQueryEq Q z then (1 : ℝ) else 0) ≤
      (if queryEq Q z then 1 else 0) + (if queryEq Q (z ∘ reservedCut.flip) then 1 else 0) := by
    intro z
    by_cases h : symQueryEq Q z
    · obtain ⟨e, he | he⟩ := h
      · have : queryEq Q z := ⟨e, he⟩
        simp only [this, ↓reduceIte]
        split_ifs <;> norm_num
      · have : queryEq Q (z ∘ reservedCut.flip) := ⟨e, he⟩
        simp only [this, ↓reduceIte]
        split_ifs <;> norm_num
    · simp only [h, ↓reduceIte]
      split_ifs <;> norm_num
  calc μ.expect (fun z => if symQueryEq Q z then (1 : ℝ) else 0)
      ≤ μ.expect (fun z => (if queryEq Q z then (1 : ℝ) else 0) +
          (if queryEq Q (z ∘ reservedCut.flip) then 1 else 0)) := μ.expect_mono hle
    _ = 2 * μ.expect (fun z => if queryEq Q z then (1 : ℝ) else 0) := by
        rw [FiniteLaw.expect_add, hflip (fun z => if queryEq Q z then (1 : ℝ) else 0)]
        ring

end Queries

end Sarkozy.CliqueDeletion
