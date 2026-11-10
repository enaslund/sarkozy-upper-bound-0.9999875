module

public import Sarkozy.SignedComponents.OptNorm
public import Sarkozy.MiddleComparison.Fixed

@[expose] public section

/-!
# The halves of the changed records and of their replacements lie in the record's support

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`, proof of
`lem:middle-comparison-prices`: "each replacement has the same actual half marginals on both
halves of `ι` as the record it replaces".

The norm of a change `ν' - Π` relative to the actual half marginal `m` of `Π` is finite only if
both halves of every configuration charged by `ν'` or by `Π` lie in the support of `m`. This
file proves that support condition (`HalvesIn`) for ten of the twelve changed records of a middle
block, and for the records themselves:

* `reserved_mem`, `reserved_flip`: the half of `ι` is layer `0`, its reflection swaps the layers;
  `halfRead φ y ℓ` is the half read through a pattern `φ` at layer `ℓ`; `plusHalf_mid`,
  `minusHalf_mid`: an emitted configuration `y ∘ e_φ` has halves `halfRead φ y 0` and
  `halfRead φ y 1`;
* `plusMarginal_emit_pos`: `m(halfRead φ y 0) > 0` for every `y` charged by the field law;
* `record_halves`: a record emitted from a block graph law whose graph has the layer swap as an
  automorphism (the `F` and `E` graphs) has both halves of each of its configurations in its
  support;
* `extend_E`: an injective triple of block labels at layer `0` extends to a configuration of
  the `E` law (`p ≥ 7`), and `extend_two`, `extend_one`;
* **`matchRec_halves`, `mergeRec_halves`, `constRec_halves`**: the constructed replacements of
  the matchings (`lem:record:e-law`(a)), merges (`lem:merge-repair`) and constants
  (`lem:record:accepting-c2`) have both halves in the support of the record they replace.

Only supports are proved here; the exact half-marginal identities of the paper are not needed for
the finiteness of the norms.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison

/-! ## The reserved cut -/

theorem reserved_mem (v : Slot) : v ∈ reservedCut.half ↔ v.2.2 = 0 := by
  revert v
  decide

theorem reserved_flip (v : Slot) : reservedCut.flip v = (v.1, v.2.1, v.2.2 + 1) := by
  revert v
  decide

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The half read through a pattern `φ` at the layer `ℓ`: `v ↦ y_{φ(v), ℓ}`. -/
def halfRead {O : Type*} (φ : ZMod 6 → O) (y : O × Fin 2 → X) (ℓ : Fin 2) :
    reservedCut.Half → X :=
  fun v => y (φ v.1.1, ℓ)

omit [Fintype X] [DecidableEq X] in
theorem plusHalf_mid {O : Type*} (φ : ZMod 6 → O) (y : O × Fin 2 → X) :
    plusHalf (c := reservedCut) (y ∘ midEmission φ) = halfRead φ y 0 := by
  funext v
  have hv : v.1.2.2 = 0 := (reserved_mem v.1).1 v.2
  simp only [plusHalf, halfRead, Function.comp_apply, midEmission, hv]
  rfl

omit [Fintype X] [DecidableEq X] in
theorem minusHalf_mid {O : Type*} (φ : ZMod 6 → O) (y : O × Fin 2 → X) :
    minusHalf (c := reservedCut) (y ∘ midEmission φ) = halfRead φ y 1 := by
  funext v
  have hv : v.1.2.2 = 0 := (reserved_mem v.1).1 v.2
  simp only [minusHalf, halfRead, Function.comp_apply, midEmission, reserved_flip, hv]
  rfl

omit [Fintype X] [DecidableEq X] in
theorem halfRead_swap {O : Type*} (φ : ZMod 6 → O) (y : O × Fin 2 → X) :
    halfRead φ (y ∘ layerSwapMap O) 0 = halfRead φ y 1 := by
  funext v
  simp [halfRead, layerSwapMap]

/-- **The record charges its own halves**: `m(halfRead φ y 0) > 0` for `y` charged by the field
law. -/
theorem plusMarginal_emit_pos {O : Type} [Fintype O] [DecidableEq O]
    (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O) {y : O × Fin 2 → X}
    (hy : lam.weight y ≠ 0) :
    0 < plusMarginal reservedCut (emit lam (midEmission φ)).weight (halfRead φ y 0) := by
  have h1 : lam.weight y ≤ (emit lam (midEmission φ)).weight (y ∘ midEmission φ) :=
    le_map_weight lam (fun y => y ∘ midEmission φ) y
  have h2 : (emit lam (midEmission φ)).weight (y ∘ midEmission φ) ≤
      plusMarginal reservedCut (emit lam (midEmission φ)).weight (halfRead φ y 0) := by
    unfold plusMarginal
    have hz : (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) = halfRead φ y 0 :=
      plusHalf_mid φ y
    refine le_trans (le_of_eq ?_) (single_le_sum (f := fun z =>
      if (fun v : reservedCut.Half => z v.1) = halfRead φ y 0 then
        (emit lam (midEmission φ)).weight z else 0) (fun z _ => ?_) (mem_univ (y ∘ midEmission φ)))
    · simp only [hz, ↓reduceIte]
    · split_ifs
      · exact (emit lam (midEmission φ)).nonneg z
      · exact le_rfl
  exact lt_of_lt_of_le (lt_of_le_of_ne (lam.nonneg y) (Ne.symm hy)) (h1.trans h2)

/-- **A record whose field law is invariant under the layer swap charges both halves of each of
its configurations.** -/
theorem record_halves {O : Type} [Fintype O] [DecidableEq O]
    (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O)
    (hswap : ∀ y, lam.weight (y ∘ layerSwapMap O) = lam.weight y) (z : Slot → X)
    (hz : (emit lam (midEmission φ)).weight z ≠ 0) :
    HalvesIn (c := reservedCut) (plusMarginal reservedCut (emit lam (midEmission φ)).weight) z := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  refine ⟨?_, ?_⟩
  · rw [plusHalf_mid]
    exact plusMarginal_emit_pos lam φ hy
  · rw [minusHalf_mid, ← halfRead_swap]
    exact plusMarginal_emit_pos lam φ (by rw [hswap]; exact hy)

/-- A configuration with halves `halfRead φ y₀ 0`, `halfRead φ y₁ 0` for charged `y₀, y₁` has both
halves in the support. -/
theorem halves_of {O : Type} [Fintype O] [DecidableEq O] (lam : FiniteLaw (O × Fin 2 → X))
    (φ : ZMod 6 → O) {z : Slot → X} {y₀ y₁ : O × Fin 2 → X} (h₀ : lam.weight y₀ ≠ 0)
    (h₁ : lam.weight y₁ ≠ 0) (e₀ : plusHalf (c := reservedCut) z = halfRead φ y₀ 0)
    (e₁ : minusHalf (c := reservedCut) z = halfRead φ y₁ 0) :
    HalvesIn (c := reservedCut) (plusMarginal reservedCut (emit lam (midEmission φ)).weight) z :=
  ⟨by rw [e₀]; exact plusMarginal_emit_pos lam φ h₀,
    by rw [e₁]; exact plusMarginal_emit_pos lam φ h₁⟩

/-! ## Extensions to the `E` law -/

section Extension

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **Prime by prime to the block**: if at every prime some charged labelling has prescribed
values `f a` at the vertices `e a`, so does the tensor law. -/
theorem tensor_extend {V A : Type} [Fintype V] [DecidableEq V]
    (μ : ∀ i, FiniteLaw (V → ZMod (pr i))) (e : A → V) (f : A → BlockLabel pr)
    (h : ∀ i, ∃ y : V → ZMod (pr i), (μ i).weight y ≠ 0 ∧ ∀ a, y (e a) = f a i) :
    ∃ y : V → BlockLabel pr, (FiniteLaw.tensor μ).weight y ≠ 0 ∧ ∀ a, y (e a) = f a := by
  choose yi hyi using h
  refine ⟨fun v i => yi i v, ?_, fun a => funext fun i => (hyi i).2 a⟩
  rw [tensor_weight]
  exact prod_ne_zero_iff.mpr fun i _ => (hyi i).1

/-- An element outside a finite set of size at most `n < |F|`. -/
theorem exists_not_mem_of_card {F : Type} [Fintype F] [DecidableEq F] (s : Finset F)
    (hs : s.card < Fintype.card F) : ∃ c, c ∉ s := by
  by_contra hcon
  push Not at hcon
  have : s = univ := eq_univ_of_forall hcon
  rw [this, card_univ] at hs
  exact lt_irrefl _ hs

/-- **One prime**: an injective triple at layer `0` extends to an injective six-label labelling
(`p ≥ 6`). -/
theorem extend_E_prime {F : Type} [Field F] [Fintype F] [DecidableEq F] (h6 : 6 ≤ Fintype.card F)
    (t : Fin 3 → F) (ht : Function.Injective t) :
    ∃ y : Fin 3 × Fin 2 → F, y ∈ injLabellings F (matchGraph (Fin 2)) ∧ ∀ o, y (o, 0) = t o := by
  have hcard : 3 ≤ Fintype.card ((univ.image t)ᶜ : Finset F) := by
    rw [Fintype.card_coe, card_compl]
    have := card_image_le (s := (univ : Finset (Fin 3))) (f := t)
    rw [card_univ, Fintype.card_fin] at this
    omega
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 3)
    (β := ((univ.image t)ᶜ : Finset F)) (by rw [Fintype.card_fin]; exact hcard)
  let u : Fin 3 → F := fun o => (emb o).1
  have hu : Function.Injective u := fun a b hab => emb.injective (Subtype.ext hab)
  have hut : ∀ o o', u o ≠ t o' := by
    intro o o' e
    have hmem : (emb o).1 ∈ (univ.image t)ᶜ := (emb o).2
    rw [mem_compl] at hmem
    exact hmem (mem_image.mpr ⟨o', mem_univ _, e.symm⟩)
  refine ⟨fun w => if w.2 = 0 then t w.1 else u w.1, ?_, fun o => by simp⟩
  rw [mem_injLabellings_iff_feasible]
  refine ⟨fun a _ b _ hab => ?_, fun e he => absurd he (Finset.notMem_empty _)⟩
  obtain ⟨o, ℓ⟩ := a
  obtain ⟨o', ℓ'⟩ := b
  fin_cases ℓ <;> fin_cases ℓ'
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at hab
    rw [ht hab]
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero] at hab
    exact absurd hab.symm (hut o' o)
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Fin.zero_eta] at hab
    exact absurd hab (hut o o')
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at hab
    rw [hu hab]

/-- **The block**: a triple of block labels, injective at every prime, extends to a configuration
charged by the `E` law at layer `0`. -/
theorem extend_E (h7 : ∀ i, 7 ≤ pr i)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    (t : Fin 3 → BlockLabel pr) (ht : ∀ i, Function.Injective fun o => t o i) :
    ∃ y, (blockGraphLaw pr (matchGraph (Fin 2)) hne).weight y ≠ 0 ∧ ∀ o, y (o, 0) = t o := by
  refine tensor_extend pr _ (fun o => (o, (0 : Fin 2))) t fun i => ?_
  have h6 : 6 ≤ Fintype.card (ZMod (pr i)) := by rw [ZMod.card]; have := h7 i; omega
  obtain ⟨y, hy, hyt⟩ := extend_E_prime h6 (fun o => t o i) (ht i)
  refine ⟨y, ?_, hyt⟩
  change (if y ∈ injLabellings (ZMod (pr i)) (matchGraph (Fin 2)) then
    1 / ((injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).card : ℝ) else 0) ≠ 0
  simp only [hy, ↓reduceIte]
  have : ((injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).card : ℝ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr (hne i)).ne'
  positivity

omit [Fintype ι] [DecidableEq ι] in
theorem injective_three {F : Type} {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro o o' e
  fin_cases o <;> fin_cases o' <;> simp_all [eq_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- A pair of block labels distinct at every prime extends to an injective triple. -/
theorem extend_two (h7 : ∀ i, 7 ≤ pr i) (a b : BlockLabel pr) (hab : ∀ i, a i ≠ b i) :
    ∃ c : BlockLabel pr,
      ∀ i, Function.Injective fun o => (![a, b, c] : Fin 3 → BlockLabel pr) o i := by
  have hc : ∀ i, ∃ c : ZMod (pr i), c ≠ a i ∧ c ≠ b i := fun i =>
    exists_ne_ne (by rw [ZMod.card]; have := h7 i; omega) (a i) (b i)
  choose c hc using hc
  refine ⟨c, fun i => ?_⟩
  have e : (fun o => (![a, b, c] : Fin 3 → BlockLabel pr) o i) = ![a i, b i, c i] := by
    funext o
    fin_cases o <;> rfl
  rw [e]
  exact injective_three (hab i) (hc i).1.symm (hc i).2.symm

omit [Fintype ι] [DecidableEq ι] in
/-- A block label extends to an injective triple. -/
theorem extend_one (h7 : ∀ i, 7 ≤ pr i) (a : BlockLabel pr) :
    ∃ b c : BlockLabel pr,
      ∀ i, Function.Injective fun o => (![a, b, c] : Fin 3 → BlockLabel pr) o i := by
  obtain ⟨c, hc⟩ := extend_two pr h7 a (a + 1) fun i h => by
    have : (1 : ZMod (pr i)) = 0 := by
      have h' : a i + 1 = a i + 0 := by rw [add_zero]; exact (show a i = (a + 1) i from h).symm
      exact add_left_cancel h'
    exact one_ne_zero this
  exact ⟨a + 1, c, hc⟩

end Extension

/-! ## The constructed replacements -/

section Replacements

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)

/-- The `E` law of a middle block. -/
noncomputable abbrev lawE : FiniteLaw (Fin 3 × Fin 2 → BlockLabel pr) :=
  blockGraphLaw pr (matchGraph (Fin 2)) hne.E2

/-- The `F` law of a middle block. -/
noncomputable abbrev lawF : FiniteLaw (Fin 3 × Fin 2 → BlockLabel pr) :=
  blockGraphLaw pr (foldGraph (Fin 2)) hne.F2

theorem lawE_swap (y : Fin 3 × Fin 2 → BlockLabel pr) :
    (lawE pr hne).weight (y ∘ layerSwapMap (Fin 3)) = (lawE pr hne).weight y :=
  blockGraphLaw_weight_auto pr _ _ _ (matchGraph_auto (Fin 2) _) y

theorem lawF_swap (y : Fin 3 × Fin 2 → BlockLabel pr) :
    (lawF pr hne).weight (y ∘ layerSwapMap (Fin 3)) = (lawF pr hne).weight y :=
  blockGraphLaw_weight_auto pr _ _ _ foldGraph_layerSwap y

/-- A layer of a configuration charged by `⊗_p K₁` is injective at every prime. -/
theorem eLaw_layer_injective {y : Fin 3 × Fin 2 → BlockLabel pr}
    (hy : (FiniteLaw.tensor fun i => eLaw (blockE_nonempty pr h i)).weight y ≠ 0) (ℓ : Fin 2)
    (i : ι) :
    Function.Injective fun o => y (o, ℓ) i := by
  rw [tensor_weight, prod_ne_zero_iff] at hy
  exact (eLaw_support _ (hy i (mem_univ i))).1 ℓ

/-- **The matching replacements charge only halves of the matching record**
(`lem:record:e-law`(a): both half marginals of `K₁` are `ν_E`). -/
theorem matchRec_halves (s : Fin 2) (z : Slot → BlockLabel pr)
    (hz : (matchRec pr h s).weight z ≠ 0) :
    HalvesIn (c := reservedCut) (plusMarginal reservedCut
      (emit (lawE pr hne) (midEmission (matching s))).weight) z := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  obtain ⟨y₀, h₀, e₀⟩ := extend_E pr h.ge7 hne.E2 (fun o => y (o, 0))
    (eLaw_layer_injective pr h hy 0)
  obtain ⟨y₁, h₁, e₁⟩ := extend_E pr h.ge7 hne.E2 (fun o => y (o, 1))
    (eLaw_layer_injective pr h hy 1)
  refine halves_of _ _ h₀ h₁ ?_ ?_
  · rw [plusHalf_mid]
    funext v
    simp only [halfRead, e₀]
  · rw [minusHalf_mid]
    funext v
    simp only [halfRead, e₁]

/-- The two labels of a layer of a merge replacement are distinct at every prime. -/
theorem mergeRep_layer_ne (k : Fin 3) {y : Fin 2 × Fin 2 → BlockLabel pr}
    (hy : (blockMergeRepLaw pr h.ringChar_ne (blockMirror_nonempty pr h) k).weight y ≠ 0)
    (ℓ : Fin 2) (i : ι) : y (0, ℓ) i ≠ y (1, ℓ) i := by
  unfold blockMergeRepLaw at hy
  rw [tensor_weight, prod_ne_zero_iff] at hy
  have hi := hy i (mem_univ i)
  unfold mergeRepLaw at hi
  split_ifs at hi
  · obtain ⟨-, h0, h1⟩ := firstLaw_support (h.ringChar_ne i) hi
    fin_cases ℓ
    · exact h0
    · exact h1
  · have hfeas := graphLaw_support mirrorGraph (blockMirror_nonempty pr h i) hi
    intro e
    have := hfeas.1 (0, ℓ) (mem_univ _) (1, ℓ) (mem_univ _) e
    simp at this

/-- **The merge replacements charge only halves of the merge record** (`lem:merge-repair`: the
replacement has the record's actual half marginals). -/
theorem mergeRec_halves (φ : PType.Pat .R) (z : Slot → BlockLabel pr)
    (hz : (mergeRec pr h φ).weight z ≠ 0) :
    HalvesIn (c := reservedCut) (plusMarginal reservedCut
      (emit (lawE pr hne) (midEmission (PType.pat .R φ))).weight) z := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hlayer : ∀ ℓ : Fin 2, ∃ y' : Fin 3 × Fin 2 → BlockLabel pr, (lawE pr hne).weight y' ≠ 0 ∧
      ∀ o : Fin 2, y' (o.castSucc, 0) = y (o, ℓ) := by
    intro ℓ
    obtain ⟨c, hc⟩ := extend_two pr h.ge7 (y (0, ℓ)) (y (1, ℓ)) (mergeRep_layer_ne pr h φ.2 hy ℓ)
    obtain ⟨y', hy', e'⟩ := extend_E pr h.ge7 hne.E2 _ hc
    refine ⟨y', hy', fun o => ?_⟩
    fin_cases o
    · exact e' 0
    · exact e' 1
  obtain ⟨y₀, h₀, e₀⟩ := hlayer 0
  obtain ⟨y₁, h₁, e₁⟩ := hlayer 1
  have hem : mergeEmission φ.1 φ.2 = midEmission (merge φ.1 φ.2) := rfl
  refine halves_of _ _ h₀ h₁ ?_ ?_
  · rw [hem, plusHalf_mid]
    funext v
    simp only [halfRead, PType.pat, e₀]
  · rw [hem, minusHalf_mid]
    funext v
    simp only [halfRead, PType.pat, e₁]

include h in
/-- **The constant replacements charge only halves of the constant record**
(`lem:record:accepting-c2`: "both norm envelopes are uniform one-label reserved diagonals"). -/
theorem constRec_halves (k : PType.Pat .C) (z : Slot → BlockLabel pr)
    (hz : (constRec pr).weight z ≠ 0) :
    HalvesIn (c := reservedCut) (plusMarginal reservedCut
      (emit (lawE pr hne) (midEmission (PType.pat .C k))).weight) z := by
  obtain ⟨y, -, rfl⟩ := emit_support _ _ hz
  have hlayer : ∀ ℓ : Fin 2, ∃ y' : Fin 3 × Fin 2 → BlockLabel pr, (lawE pr hne).weight y' ≠ 0 ∧
      y' (0, 0) = y ℓ := by
    intro ℓ
    obtain ⟨b, c, hc⟩ := extend_one pr h.ge7 (y ℓ)
    obtain ⟨y', hy', e'⟩ := extend_E pr h.ge7 hne.E2 _ hc
    exact ⟨y', hy', e' 0⟩
  obtain ⟨y₀, h₀, e₀⟩ := hlayer 0
  obtain ⟨y₁, h₁, e₁⟩ := hlayer 1
  refine halves_of _ _ h₀ h₁ ?_ ?_
  · funext v
    have hv : v.1.2.2 = 0 := (reserved_mem v.1).1 v.2
    simp only [plusHalf, halfRead, PType.pat, e₀, Function.comp_apply, layerEmission, hv]
    rfl
  · funext v
    have hv : v.1.2.2 = 0 := (reserved_mem v.1).1 v.2
    simp only [minusHalf, halfRead, PType.pat, e₁, Function.comp_apply, layerEmission,
      reserved_flip, hv]
    rfl

end Replacements

end Sarkozy.SignedComponents
