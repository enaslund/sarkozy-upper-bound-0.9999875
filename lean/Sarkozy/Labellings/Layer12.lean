module

public import Sarkozy.Labellings.Patterns

/-!
# The twelve-label graphs (`lem:layer12-geometry`)

`paper/sections/20_middle_reference.tex`, `subsec:push:layer12spectral`.

The graphs, with layer set `{0, 1}` and their one-layer versions:
* the twelve-label root `G_{L,2}` is `recordGraph (Fin 2)`;
* the `F` graph `G_{F,2}` is `foldGraph (Fin 2)`;
* the `E` graph `G_{E,2}` (`matchGraph`) has no edges.

Proved:
* `G_{L,2}` has 12 vertices and 24 edges, and every vertex has in- and out-degree 2, so total
  degree 4 (`decide`);
* (a): the chamber reflections, the translation and the layer swap are automorphisms of
  `G_{L,2}`; the first two also of `G_{L,1}`; the layer swap of `G_{F,2}` and `G_{E,2}`;
* (b): the subgraph of `G_{L,j}` induced on the plus half `H_0 = {0, 1, 2}` is `G_{F,j}`;
* (c): layer `0` of `G_{𝔣,2}` is `G_{𝔣,1}`;
* (d): `G_{F,j}` and `G_{E,j}` induce the same graph, with no edges, on the object pairs
  `{0, 1}` and `{1, 2}`.

The paper's block laws `λ_𝔅(G)` are tensors over the primes, and automorphisms act factorwise
(`graphLaw_expect_comp` for each factor).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

variable (Λ : Type*) [Fintype Λ]

/-- **The `E` graph** on `{0, 1, 2} × Λ`: no edges. -/
def matchGraph : OrientedGraph (Fin 3 × Λ) where
  E := ∅
  loopless _ := Finset.notMem_empty _
  oriented _ _ h := absurd h (Finset.notMem_empty _)

omit [Fintype Λ] in
/-- Every bijection is an automorphism of the edgeless `E` graph. -/
theorem matchGraph_auto (π : Fin 3 × Λ ≃ Fin 3 × Λ) : IsAutomorphism (matchGraph Λ) π := by
  intro u v
  simp [matchGraph]

/-- **`G_{L,2}` has 24 edges.** -/
theorem recordGraph_two_card : (recordGraph (Fin 2)).E.card = 24 := by
  unfold recordGraph rot
  decide

/-- **Every vertex of `G_{L,2}` has out-degree 2 and in-degree 2**, so total degree 4. -/
theorem recordGraph_two_degrees (u : ZMod 6 × Fin 2) :
    ((recordGraph (Fin 2)).E.filter fun e => e.1 = u).card = 2 ∧
      ((recordGraph (Fin 2)).E.filter fun e => e.2 = u).card = 2 := by
  revert u
  unfold recordGraph rot
  decide

/-- **`lem:layer12-geometry`(a).** The chamber reflections `u ↦ k − u` (`k = 1, 3, 5`) and the
translation `u ↦ u + 2` are automorphisms of `G_{L,j}` for every layer set; the layer swap is an
automorphism of `G_{L,2}`, `G_{F,2}` and `G_{E,2}`. -/
theorem layer12_automorphisms :
    (∀ k : ZMod 6, (k = 1 ∨ k = 3 ∨ k = 5) →
      IsAutomorphism (recordGraph Λ) (reflectionMap Λ k)) ∧
    IsAutomorphism (recordGraph Λ) (translationMap Λ) ∧
    IsAutomorphism (recordGraph (Fin 2)) (layerSwapMap (ZMod 6)) ∧
    IsAutomorphism (foldGraph (Fin 2)) (layerSwapMap (Fin 3)) ∧
    IsAutomorphism (matchGraph (Fin 2)) (layerSwapMap (Fin 3)) :=
  ⟨fun k hk => recordGraph_reflection Λ k hk, recordGraph_translation Λ, recordGraph_layerSwap,
    foldGraph_layerSwap, matchGraph_auto (Fin 2) _⟩

/-- **`lem:layer12-geometry`(b).** The subgraph of `G_{L,j}` induced on the plus half
`H_0 = {0, 1, 2}`, read in order, is `G_{F,j}`. -/
theorem layer12_restrict_half (a b : Fin 3 × Λ) :
    (halfEmb Λ 0 a, halfEmb Λ 0 b) ∈ (recordGraph Λ).E ↔ (a, b) ∈ (foldGraph Λ).E :=
  halfEmb_edge_iff Λ 0 a b

/-- **`lem:layer12-geometry`(c).** Layer `0` of `G_{L,2}` is `G_{L,1}`, and likewise for `F`;
`E` has no edges at any layer. -/
theorem layer12_layer_zero (u v : ZMod 6) (o o' : Fin 3) :
    (((u, (0 : Fin 2)), (v, (0 : Fin 2))) ∈ (recordGraph (Fin 2)).E ↔
      ((u, (0 : Fin 1)), (v, (0 : Fin 1))) ∈ (recordGraph (Fin 1)).E) ∧
    (((o, (0 : Fin 2)), (o', (0 : Fin 2))) ∈ (foldGraph (Fin 2)).E ↔
      ((o, (0 : Fin 1)), (o', (0 : Fin 1))) ∈ (foldGraph (Fin 1)).E) := by
  simp [mem_recordGraph, mem_foldGraph]

/-- **`lem:layer12-geometry`(d).** On the object pairs `{0, 1}` and `{1, 2}`, `G_{F,j}` has no
edges, like `G_{E,j}`. -/
theorem layer12_fold_pairs (a b : Fin 3 × Λ) (h : (a.1 ≠ 2 ∧ b.1 ≠ 2) ∨ (a.1 ≠ 0 ∧ b.1 ≠ 0)) :
    (a, b) ∉ (foldGraph Λ).E ∧ (a, b) ∉ (matchGraph Λ).E := by
  refine ⟨?_, by simp [matchGraph]⟩
  rw [mem_foldGraph]
  rintro ⟨ha, hb⟩
  rcases h with ⟨_, hb2⟩ | ⟨ha0, _⟩
  · exact hb2 hb
  · exact ha0 ha

end Sarkozy.Labellings
