module

public import Sarkozy.MiddleComparison.Block
public import Sarkozy.PartVRecords.MergeQueried
public import Sarkozy.PartVRecords.MergeMarginals

@[expose] public section

/-!
# The merge replacements of a middle block, constructed (`lem:merge-repair`, `cor:merge-repair`)

`paper/sections/21_middle_records.tex`, `lem:merge-repair`, `cor:merge-repair` and
`subsec:middle-comparison` ("the six two-layer merge records (weight `w_R r²`), replaced by the
repairs of `cor:merge-repair`").

V3 (`PartVRecords.MergeRecords`) defines the replacement of the merge record `G_{sk}` at one prime
(`mergeRepLaw`: the mirror-edge law for `k ≠ 2`, the first-coordinate law for `k = 2`), its block
product `blockMergeRepLaw` and proves that the placed law accepts the six queries
(`blockMergeRep_accepts`). Here:

* `mirror_nonempty`: the mirror graph has injective strict-square labellings at every prime
  `p ≡ 3 (4)`, `p ≥ 7` (from V3's count `mirror_count_total`, `(q-3)(q-2)q(q-1)/4 > 0`), so the
  replacement exists on every middle block (`blockMirror_nonempty`);
* `mergeRepLaw_translate`: its weight is translation invariant (`firstLaw_affine`,
  `graphLaw_weight_translate`), so the placed block law `mergeRec` has uniform one-slot marginals
  (`mergeRec_uniform`); `mergeRec_accepts`: acceptance in the form of `def:cp4`(a);

The norm table of `lem:merge-repair` (W6's `MergeRepairBounds`) for `mergeRec - Π_{G_{sk}}` is not
proved here; `Sarkozy.MiddleComparison.Fixed` uses `mergeRec` in `ReplacementData`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.Labellings

section OnePrime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The mirror graph has injective strict-square labellings** at every `q ≡ 3 (4)`, `q ≥ 7`:
their number is `q(q-1)(q-3)(q-2)/4 > 0` (V3's `mirror_count_total`). -/
theorem mirror_nonempty (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h7 : 7 ≤ Fintype.card F) : (injLabellings F mirrorGraph).Nonempty := by
  by_contra hne
  have hall : ∀ t : F × F × F × F, ¬ MirrorCond t := fun t ht =>
    hne ⟨_, (mem_inj_mirror_iff t).mpr ht⟩
  have h := mirror_count_total hF h3
  simp only [hall, ↓reduceIte, sum_const_zero] at h
  have hq : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast h7
  have h1 : 0 < (Fintype.card F : ℝ) - 3 := by linarith
  have h2 : 0 < (Fintype.card F : ℝ) - 2 := by linarith
  have h3' : 0 < (Fintype.card F : ℝ) - 1 := by linarith
  have h4 : 0 < (Fintype.card F : ℝ) := by linarith
  have : 0 < (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) *
      (((Fintype.card F : ℝ) - 3) * ((Fintype.card F : ℝ) - 2) / 4) := by positivity
  linarith

/-- **The merge replacement is translation invariant** (`lem:merge-repair`: invariance under the
square-affine maps, here with `α = 1`). -/
theorem mergeRepLaw_translate (hF : ringChar F ≠ 2) (hne : (injLabellings F mirrorGraph).Nonempty)
    (k : Fin 3) (c : F) (z : Fin 2 × Fin 2 → F) :
    (mergeRepLaw hF hne k).weight (fun w => z w + c) = (mergeRepLaw hF hne k).weight z := by
  unfold mergeRepLaw
  split_ifs
  · let e : (Fin 2 × Fin 2 → F) ≃ (Fin 2 × Fin 2 → F) :=
      Equiv.piCongrRight fun _ => Equiv.addRight c
    refine weight_comp_of_expect (firstLaw F hF) e (fun f => ?_) z
    have h := firstLaw_affine hF (α := 1) (by simp) c f
    simp only [one_mul] at h
    exact h
  · exact graphLaw_weight_translate mirrorGraph hne c z

end OnePrime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr)

omit [Fintype ι] [DecidableEq ι] in
/-- The mirror graph has labellings at every prime of a middle block. -/
theorem blockMirror_nonempty (h : ClassThreeBlock pr) :
    ∀ i, (injLabellings (ZMod (pr i)) mirrorGraph).Nonempty :=
  fun i => mirror_nonempty (h.ringChar_ne i) (h.card_mod i) (by rw [ZMod.card]; exact h.ge7 i)

/-- **The placed block replacement of the merge record `G_{sk}`** (`lem:merge-repair`): V3's
`blockMergeRepLaw` emitted by `G_{sk}` on the two layers. -/
noncomputable def mergeRec (φ : PType.Pat .R) : FiniteLaw (Slot → BlockLabel pr) :=
  emit (blockMergeRepLaw pr h.ringChar_ne (blockMirror_nonempty pr h) φ.2) (mergeEmission φ.1 φ.2)

/-- **The merge replacements accept the six queries** (`def:cp4`(a), V3's
`blockMergeRep_accepts`). -/
theorem mergeRec_accepts (φ : PType.Pat .R) (z : Slot → BlockLabel pr)
    (hz : (mergeRec pr h φ).weight z ≠ 0) (e : Chamber) :
    blockSquareAccepted pr (z (MainAnchor.paperQueries.source e))
      (z (MainAnchor.paperQueries.target e)) := by
  rw [paperQueries_source_eq, paperQueries_target_eq]
  exact blockSquareAccepted_of pr fun i =>
    blockMergeRep_accepts pr h.ringChar_ne (blockMirror_nonempty pr h) φ.1 φ.2 hz e i

/-- **The merge replacements have uniform one-slot marginals** (translation invariance at every
prime). -/
theorem mergeRec_uniform (φ : PType.Pat .R) : HasUniformMarginals (mergeRec pr h φ) :=
  emit_uniform _ _ fun o g => tensor_vertex_uniform_of_translation pr _
    (fun i c z => mergeRepLaw_translate (h.ringChar_ne i) (blockMirror_nonempty pr h i) φ.2 c z) o g

end Block

end Sarkozy.MiddleComparison
