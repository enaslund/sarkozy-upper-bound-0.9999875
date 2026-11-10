module

public import Sarkozy.MiddleComparison.Merges

@[expose] public section

/-!
# The matching replacements of a middle block (`lem:record:e-law`(a), `lem:record:exact-marginal-e`)

`paper/sections/21_middle_records.tex`, `lem:record:exact-marginal-e`: "each two-layer matching
record `E₀, E₁` of a middle block is replaced, at every prime, by the law `K₁` of
`lem:record:e-law`, and the block record is the tensor product over the primes";
`lem:record:e-law`(a): `K₁` "is `4/z₁` times the indicator of the strict edges `x₁ → y₀` and
`x₀ → y₁` and imposes no other relation between the halves", relative to `ν_E ⊗ ν_E` (`ν_E`
uniform on the injective triples).

So `K₁` is the uniform law on the two-layer labellings `y : Fin 3 × Fin 2 → 𝔽_p` that are injective
within each layer and have the strict edges `x₁ → y₀`, `x₀ → y₁` (`EGood`, `eSet`, `eLaw`).

* `eSet_nonempty`: `eSet` is nonempty when `|𝔽_p| ≥ 3` and the mirror graph has labellings (extend
  a mirror labelling by a third label in each layer);
* `eLaw_translate`: `K₁` is translation invariant, so the placed block law has uniform one-slot
  marginals (`matchRec_uniform`);
* **`matchRec s`**: the block law `⊗_p K₁` placed by the matching `E_s` on the two layers;
  `matchRec_accepts`: every query reads `x₀ → y₁` (`cert:record:middle-geometry`), a strict edge
  of `K₁`, so it is accepted.

The norms of `matchRec s - Π_{E_s}` (`lem:record:exact-marginal-e`(i),(ii)) are not proved here.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.Labellings

section OnePrime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The support of `K₁`: injective within each layer, with the strict edges `x₁ → y₀` and
`x₀ → y₁`. -/
def EGood (y : Fin 3 × Fin 2 → F) : Prop :=
  (∀ ℓ : Fin 2, Function.Injective fun o : Fin 3 => y (o, ℓ)) ∧
    quadraticChar F (y (0, 1) - y (1, 0)) = 1 ∧ quadraticChar F (y (1, 1) - y (0, 0)) = 1

instance (y : Fin 3 × Fin 2 → F) : Decidable (EGood y) := by unfold EGood; infer_instance

/-- The support of `K₁`, as a finite set. -/
noncomputable def eSet : Finset (Fin 3 × Fin 2 → F) := univ.filter EGood

omit [Field F] in
theorem exists_ne_ne (h3 : 3 ≤ Fintype.card F) (a b : F) : ∃ c : F, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  have key : ∀ c : F, c ∈ ({a, b} : Finset F) := fun c => by
    by_contra h'
    simp only [mem_insert, mem_singleton, not_or] at h'
    exact hcon ⟨c, h'.1, h'.2⟩
  have hsub : (univ : Finset F) ⊆ {a, b} := fun c _ => key c
  have h1 := card_le_card hsub
  have h2 := card_insert_le a ({b} : Finset F)
  rw [card_univ, card_singleton] at *
  omega

/-- **`K₁` exists** (`lem:record:e-law`(a)): extend a labelling of the mirror graph (the two strict
edges on the objects `0, 1`) by a third label in each layer. -/
theorem eSet_nonempty (h3 : 3 ≤ Fintype.card F) (hm : (injLabellings F mirrorGraph).Nonempty) :
    (eSet (F := F)).Nonempty := by
  obtain ⟨m, hm⟩ := hm
  rw [mem_injLabellings_iff_feasible] at hm
  obtain ⟨hinj, hedge⟩ := hm
  obtain ⟨c₀, hc₀a, hc₀b⟩ := exists_ne_ne h3 (m (0, 0)) (m (1, 0))
  obtain ⟨c₁, hc₁a, hc₁b⟩ := exists_ne_ne h3 (m (0, 1)) (m (1, 1))
  have h01 : ∀ ℓ : Fin 2, m (0, ℓ) ≠ m (1, ℓ) := fun ℓ e => by
    have := hinj _ (mem_univ _) _ (mem_univ _) e
    simp at this
  let c : Fin 2 → F := ![c₀, c₁]
  have hc : ∀ ℓ, c ℓ ≠ m (0, ℓ) ∧ c ℓ ≠ m (1, ℓ) := by
    intro ℓ
    fin_cases ℓ
    · exact ⟨hc₀a, hc₀b⟩
    · exact ⟨hc₁a, hc₁b⟩
  let y : Fin 3 × Fin 2 → F := fun p => ![m (0, p.2), m (1, p.2), c p.2] p.1
  refine ⟨y, mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩⟩
  · intro ℓ o o' e
    have hℓ := h01 ℓ
    have hcℓ := hc ℓ
    fin_cases o <;> fin_cases o' <;> simp [y] at e ⊢
    · exact hℓ e
    · exact hcℓ.1 e.symm
    · exact hℓ e.symm
    · exact hcℓ.2 e.symm
    · exact hcℓ.1 e
    · exact hcℓ.2 e
  · exact hedge ((1, 0), (0, 1)) (by simp [mirrorGraph]) (mem_univ _) (mem_univ _)
  · exact hedge ((0, 0), (1, 1)) (by simp [mirrorGraph]) (mem_univ _) (mem_univ _)

/-- **The exact-marginal matching law `K₁`** (`lem:record:e-law`(a)): uniform on `eSet`. -/
noncomputable def eLaw (hne : (eSet (F := F)).Nonempty) : FiniteLaw (Fin 3 × Fin 2 → F) where
  weight z := if z ∈ eSet then 1 / ((eSet (F := F)).card : ℝ) else 0
  nonneg z := by split_ifs <;> positivity
  total := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    have : ((eSet (F := F)).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
    field_simp

theorem eLaw_support (hne : (eSet (F := F)).Nonempty) {y : Fin 3 × Fin 2 → F}
    (hy : (eLaw hne).weight y ≠ 0) : EGood y := by
  by_contra hn
  apply hy
  have : y ∉ eSet := fun h => hn (mem_filter.mp h).2
  change (if y ∈ eSet then _ else _) = _
  simp only [this, ↓reduceIte]

/-- `EGood` is invariant under translations. -/
theorem eGood_translate (c : F) (y : Fin 3 × Fin 2 → F) :
    EGood (fun w => y w + c) ↔ EGood y := by
  have h1 : ∀ a b : Fin 3 × Fin 2, (y a + c) - (y b + c) = y a - y b := fun a b => by ring
  unfold EGood
  simp only [h1]
  constructor
  · rintro ⟨hi, he⟩
    refine ⟨fun ℓ o o' e => hi ℓ ?_, he⟩
    simp only [e]
  · rintro ⟨hi, he⟩
    refine ⟨fun ℓ o o' e => hi ℓ ?_, he⟩
    exact add_right_cancel e

/-- **`K₁` is translation invariant.** -/
theorem eLaw_translate (hne : (eSet (F := F)).Nonempty) (c : F) (y : Fin 3 × Fin 2 → F) :
    (eLaw hne).weight (fun w => y w + c) = (eLaw hne).weight y := by
  have hmem : (fun w => y w + c) ∈ eSet ↔ y ∈ eSet := by
    simp only [eSet, mem_filter, mem_univ, true_and]
    exact eGood_translate c y
  change (if _ ∈ eSet then _ else _) = (if _ ∈ eSet then _ else _)
  simp only [hmem]

end OnePrime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr)

omit [Fintype ι] [DecidableEq ι] in
/-- `K₁` exists at every prime of a middle block. -/
theorem blockE_nonempty (h : ClassThreeBlock pr) : ∀ i, (eSet (F := ZMod (pr i))).Nonempty :=
  fun i => eSet_nonempty (by rw [ZMod.card]; have := h.ge7 i; omega) (blockMirror_nonempty pr h i)

/-- **The matching replacement of `E_s`** (`lem:record:exact-marginal-e`): the block law
`⊗_p K₁` placed by the matching `E_s` on the two layers. -/
noncomputable def matchRec (s : Fin 2) : FiniteLaw (Slot → BlockLabel pr) :=
  emit (FiniteLaw.tensor fun i => eLaw (blockE_nonempty pr h i)) (midEmission (matching s))

theorem matching_query_source (s : Fin 2) (j : Chamber) :
    midEmission (matching s) (querySource j) = ((0 : Fin 3), (0 : Fin 2)) := by
  revert s j
  decide

theorem matching_query_target (s : Fin 2) (j : Chamber) :
    midEmission (matching s) (queryTarget j) = ((1 : Fin 3), (1 : Fin 2)) := by
  revert s j
  decide

/-- **The matching replacements accept the six queries**: every query reads `x₀ → y₁`
(`cert:record:middle-geometry`), a strict edge of `K₁` at every prime. -/
theorem matchRec_accepts (s : Fin 2) (z : Slot → BlockLabel pr)
    (hz : (matchRec pr h s).weight z ≠ 0) (e : Chamber) :
    blockSquareAccepted pr (z (MainAnchor.paperQueries.source e))
      (z (MainAnchor.paperQueries.target e)) := by
  rw [paperQueries_source_eq, paperQueries_target_eq]
  refine blockSquareAccepted_of pr fun i => ?_
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  rw [tensor_weight, Finset.prod_ne_zero_iff] at hy
  have hgood := eLaw_support _ (hy i (mem_univ i))
  simp only [Function.comp_apply, matching_query_source, matching_query_target]
  exact hgood.2.2

/-- **The matching replacements have uniform one-slot marginals.** -/
theorem matchRec_uniform (s : Fin 2) : HasUniformMarginals (matchRec pr h s) :=
  emit_uniform _ _ fun o g => tensor_vertex_uniform_of_translation pr _
    (fun i c z => eLaw_translate (blockE_nonempty pr h i) c z) o g

end Block

end Sarkozy.MiddleComparison
