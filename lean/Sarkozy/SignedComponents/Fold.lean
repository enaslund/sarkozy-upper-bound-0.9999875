module

public import Sarkozy.SignedComponents.Support

@[expose] public section

/-!
# The signed fold components of a middle block, from their per-prime properties

`paper/sections/21_middle_records.tex`, `lem:signed-components`, `def:record:mixture`(b)–(e),
the paragraph "Acceptance" after it, and `cert:record:middle-geometry`.

At every prime `p` of a middle block the paper fixes three component laws `P_{++,p}`, `P_{-+,p}`,
`P_{--,p}` on pairs of halves of the fold record (`lem:signed-components`(d)), and takes their
tensor products over the block; the record of `F₁` is `⊗P_{++} + (t/2)⊗P_{-+} - (t/2)⊗P_{--}`,
placed by `F₁`, and the record of `F₂` is the reflected transpose, placed by `F₂`.

* **`FoldPrimeComponents p hF`** (the per-prime input): for `F₁` and `F₂` (`j = 0, 1`) and each
  of the three components `c`, a law on two-layer labellings of the fold objects such that
  - `query`: the query edge of the fold holds on its support (`x₁ → y₀` for `F₁`, `x₂ → y₁` for
    `F₂`; `lem:signed-components`(a),(d): "supported on `x₁ → y₀`", and `𝖢^ς = χ(y₁ - x₂)`);
  - `translate`: it is translation invariant (part of the `𝒢_p`-invariance of
    `lem:signed-components`(a),(d));
  - `half`: both of its half marginals (layers `0` and `1`) are the half marginal of the fold
    graph law, `m_{0,p}` (`lem:signed-components`(d): "with both half marginals `m₀`").
* `foldQuery`: the queries read `foldSrc j → foldTgt j` (W6's `fold_query`).
* **`foldRec C j c`**: the block law `⊗_p P_{c,p}` of `F_{j+1}`, placed by the fold pattern
  `foldPat j`. `foldRec_accepts` (the six queries are accepted), `foldRec_uniform` (uniform
  one-slot marginals), **`foldRec_halves`** (both halves in the support of the fold record's
  actual half marginal).

`FoldPrimeComponents` is the conclusion of `lem:signed-components`(a),(d). It is constructed in
`Sarkozy.SignedComponents.PrimeComponents` (`primeComponents`, from the paper's `U_{uv}` and the
marginal repair, given the defect bound of (c)). The structure itself does not require the
reflected-transpose relation between the components of `F₁` and `F₂` (`def:record:mixture`(d));
`primeComponents` has it by construction.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.ComparisonLawPaper

/-- The source of the query edge of the fold `F_{j+1}`: `x₁` for `F₁`, `x₂` for `F₂`. -/
def foldSrc : Fin 2 → Fin 3 × Fin 2 := ![(1, 0), (2, 0)]

/-- The target of the query edge of the fold `F_{j+1}`: `y₀` for `F₁`, `y₁` for `F₂`. -/
def foldTgt : Fin 2 → Fin 3 × Fin 2 := ![(0, 1), (1, 1)]

/-- **The queries of the folds** (`cert:record:middle-geometry`, W6's `fold_query`): every query
of `𝓔₆` reads `x₁ → y₀` in `F₁` and `x₂ → y₁` in `F₂`. -/
theorem foldQuery (j : Fin 2) (e : Chamber) :
    midEmission (fold (foldPat j)) (querySource e) = foldSrc j ∧
      midEmission (fold (foldPat j)) (queryTarget e) = foldTgt j := by
  revert j e
  decide

/-- **The per-prime fold components** (the conclusion of `lem:signed-components`(a),(d)): for
`F₁, F₂` (`j`) and the three components `P_{++}, P_{-+}, P_{--}` (`c`), laws on the two-layer
labellings of the fold objects, supported on the query edge of the fold, translation invariant,
with both half marginals equal to the half marginal `m_{0,p}` of the fold graph law. -/
structure FoldPrimeComponents (p : ℕ) [Fact p.Prime]
    (hF : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty) where
  law : Fin 2 → Fin 3 → FiniteLaw (Fin 3 × Fin 2 → ZMod p)
  query : ∀ j c (y : Fin 3 × Fin 2 → ZMod p), (law j c).weight y ≠ 0 →
    quadraticChar (ZMod p) (y (foldTgt j) - y (foldSrc j)) = 1
  translate : ∀ j c (a : ZMod p) (y : Fin 3 × Fin 2 → ZMod p),
    (law j c).weight (fun w => y w + a) = (law j c).weight y
  half : ∀ j c (ℓ : Fin 2) (g : (Fin 3 → ZMod p) → ℝ),
    (law j c).expect (fun y => g fun o => y (o, ℓ)) =
      (graphLaw (foldGraph (Fin 2)) hF).expect (fun y => g fun o => y (o, 0))

namespace FoldPrimeComponents

variable {p : ℕ} [Fact p.Prime] {hF : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty}
  (C : FoldPrimeComponents p hF)

/-- **Each layer of a charged configuration is a layer-`0` half charged by the fold graph law**
(from `half`). -/
theorem half_support (j : Fin 2) (c : Fin 3) {y : Fin 3 × Fin 2 → ZMod p}
    (hy : (C.law j c).weight y ≠ 0) (ℓ : Fin 2) :
    ∃ y' : Fin 3 × Fin 2 → ZMod p, (graphLaw (foldGraph (Fin 2)) hF).weight y' ≠ 0 ∧
      ∀ o, y' (o, 0) = y (o, ℓ) := by
  classical
  let x : Fin 3 → ZMod p := fun o => y (o, ℓ)
  let g : (Fin 3 → ZMod p) → ℝ := fun x' => if x' = x then 1 else 0
  have hpos : 0 < (C.law j c).expect (fun y' => g fun o => y' (o, ℓ)) := by
    have h1 : (C.law j c).weight y ≤ (C.law j c).expect (fun y' => g fun o => y' (o, ℓ)) := by
      unfold FiniteLaw.expect
      refine le_trans (le_of_eq ?_) (single_le_sum (f := fun y' => (C.law j c).weight y' *
        g fun o => y' (o, ℓ)) (fun y' _ => mul_nonneg ((C.law j c).nonneg y') ?_) (mem_univ y))
      · simp [g, x]
      · simp only [g]
        split_ifs <;> norm_num
    exact lt_of_lt_of_le (lt_of_le_of_ne ((C.law j c).nonneg y) (Ne.symm hy)) h1
  rw [C.half j c ℓ g] at hpos
  obtain ⟨y', -, hy'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  refine ⟨y', left_ne_zero_of_mul hy', fun o => ?_⟩
  have hg := right_ne_zero_of_mul hy'
  simp only [g] at hg
  split_ifs at hg with hx
  · exact congrFun hx o
  · exact absurd rfl hg

end FoldPrimeComponents

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hne : MiddleNonempty pr)

/-- **The fold components of a middle block**: the per-prime components at every prime. -/
abbrev FoldComponents : Type := ∀ i, FoldPrimeComponents (pr i) (hne.F2 i)

variable {pr} {hne} (C : FoldComponents pr hne)

/-- The block law `⊗_p P_{c,p}` of the fold `F_{j+1}`. -/
noncomputable def foldLaw (j : Fin 2) (c : Fin 3) : FiniteLaw (Fin 3 × Fin 2 → BlockLabel pr) :=
  FiniteLaw.tensor fun i => (C i).law j c

/-- **The normalized component `⊗_p P_{c,p}` of the signed record of `F_{j+1}`**, placed by the
fold `F_{j+1}` (`def:record:mixture`(c)–(e)). -/
noncomputable def foldRec (j : Fin 2) (c : Fin 3) : FiniteLaw (Slot → BlockLabel pr) :=
  emit (foldLaw C j c) (midEmission (fold (foldPat j)))

/-- **The fold components accept the six queries** (the paragraph "Acceptance" after
`def:record:mixture`). -/
theorem foldRec_accepts (j : Fin 2) (c : Fin 3) (z : Slot → BlockLabel pr)
    (hz : (foldRec C j c).weight z ≠ 0) (e : Chamber) :
    blockSquareAccepted pr (z (MainAnchor.paperQueries.source e))
      (z (MainAnchor.paperQueries.target e)) := by
  rw [paperQueries_source_eq, paperQueries_target_eq]
  refine blockSquareAccepted_of pr fun i => ?_
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  unfold foldLaw at hy
  rw [tensor_weight, prod_ne_zero_iff] at hy
  have hq := (C i).query j c _ (hy i (mem_univ i))
  simp only [Function.comp_apply, (foldQuery j e).1, (foldQuery j e).2]
  exact hq

/-- **The fold components have uniform one-slot marginals** (translation invariance at every
prime). -/
theorem foldRec_uniform (j : Fin 2) (c : Fin 3) : HasUniformMarginals (foldRec C j c) :=
  emit_uniform _ _ fun o g => tensor_vertex_uniform_of_translation pr _
    (fun i a z => (C i).translate j c a z) o g

/-- Each layer of a configuration charged by the block law `⊗_p P_{c,p}` is a layer-`0` half
charged by the block fold law. -/
theorem foldLaw_half (j : Fin 2) (c : Fin 3) {y : Fin 3 × Fin 2 → BlockLabel pr}
    (hy : (foldLaw C j c).weight y ≠ 0) (ℓ : Fin 2) :
    ∃ y', (lawF pr hne).weight y' ≠ 0 ∧ ∀ o, y' (o, 0) = y (o, ℓ) := by
  unfold foldLaw at hy
  rw [tensor_weight, prod_ne_zero_iff] at hy
  refine tensor_extend pr _ (fun o => (o, (0 : Fin 2))) (fun o => y (o, ℓ)) fun i => ?_
  exact (C i).half_support j c (hy i (mem_univ i)) ℓ

/-- **The fold components charge only halves of the fold record** (`lem:signed-components`(d):
both half marginals are `m₀`). -/
theorem foldRec_halves (j : Fin 2) (c : Fin 3) (z : Slot → BlockLabel pr)
    (hz : (foldRec C j c).weight z ≠ 0) :
    HalvesIn (c := reservedCut) (plusMarginal reservedCut
      (emit (lawF pr hne) (midEmission (fold (foldPat j)))).weight) z := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  obtain ⟨y₀, h₀, e₀⟩ := foldLaw_half C j c hy 0
  obtain ⟨y₁, h₁, e₁⟩ := foldLaw_half C j c hy 1
  refine halves_of _ _ h₀ h₁ ?_ ?_
  · rw [plusHalf_mid]
    funext v
    simp only [halfRead, e₀]
  · rw [minusHalf_mid]
    funext v
    simp only [halfRead, e₁]

end Block

end Sarkozy.SignedComponents
