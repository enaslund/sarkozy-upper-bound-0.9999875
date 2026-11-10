module

public import Sarkozy.Labellings.Patterns

/-!
# The two-layer graphs (`lem:upper-geometry`)

`paper/sections/25_upper_reference.tex`, `subsec:push:layer72spectral`.

There are three field types, each with a relation and a forward relation on its objects:
* `L` on `ℤ/6ℤ`: `x → y` is related if `y ∈ {x + 1, x − 1, rot x}`, and forward if
  `y = rot x`;
* `F` on `{0, 1, 2}`: the restrictions of `L`'s relations. The related pairs are `0→1`, `1→0`,
  `1→2`, `2→1` and `0→2`, and only `0→2` is forward;
* `E` on `{0, 1, 2}`: all ordered pairs of distinct objects are related, and none is forward.

For two field types, `G_{φ₀φ₁}` (`twoLayerGraph`) is the graph on `O_{φ₀} × O_{φ₁} × Λ` with an
edge `(u₀, u₁, ℓ) → (v₀, v₁, ℓ')` whenever both coordinate relations hold and at least one is
forward. There is no condition on the layers. The root is `G_{LL,2}`.

Proved (`lem:upper-geometry`):
* (a) every `G_{φ₀φ₁}` is an oriented graph. The root has 72 vertices and 720 edges, with 10
  out-neighbours and 10 in-neighbours at every vertex, and it contains every query
  `(u₀, u₁, ℓ) → (rot u₀, rot u₁, 1 − ℓ)`. The counts are checked by `decide` in the kernel.
* (b) maps preserving both relations coordinatewise are automorphisms (`twoLayer_auto`):
  - the chamber reflections `u ↦ k − u` (k = 1, 3, 5) of an `L` coordinate;
  - the layer swap;
  - every permutation of `O_E`.
* (c) on the plus half `{0, 1, 2}` of an `L` coordinate, `L`'s relations are `F`'s, so the
  induced subgraph is `G_{F φ}`. Layer `0` of `G_{φφ',2}` is `G_{φφ',1}`.
* (d) `F` and `E` agree on the objects `{0, 1}` and on `{1, 2}`, and neither relates an object to
  itself.

The twelve physical queries of `eq:upper-twelve`, `((u, v, 0), (rot u, rot v, 1))` with
`u ∈ {0, 5}`, are the instances `ℓ = 0` of `root_query`, since `1 − 0 = 1`. The six queries
`𝓔_6` are the case `u = 0`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

/-- A field type: a relation and a forward relation on its objects, as Boolean functions. -/
structure FieldType (O : Type*) where
  rel : O → O → Bool
  fwd : O → O → Bool

/-- The root field type `L` on `ℤ/6ℤ`. -/
def typeL : FieldType (ZMod 6) where
  rel x y := decide (y = x + 1) || decide (y = x - 1) || decide (y = rot x)
  fwd x y := decide (y = rot x)

/-- The fold field type `F` on `{0, 1, 2}`. -/
def typeF : FieldType (Fin 3) where
  rel x y := decide ((x, y) = (0, 1)) || decide ((x, y) = (1, 0)) || decide ((x, y) = (1, 2)) ||
    decide ((x, y) = (2, 1)) || decide ((x, y) = (0, 2))
  fwd x y := decide ((x, y) = (0, 2))

/-- The matching field type `E` on `{0, 1, 2}`. -/
def typeE : FieldType (Fin 3) where
  rel x y := decide (x ≠ y)
  fwd _ _ := false

variable {O₀ O₁ Λ : Type*}

/-- The edge relation of `G_{φ₀φ₁}`. -/
def twoLayerEdge (c₀ : FieldType O₀) (c₁ : FieldType O₁) (a b : O₀ × O₁ × Λ) : Bool :=
  c₀.rel a.1 b.1 && c₁.rel a.2.1 b.2.1 && (c₀.fwd a.1 b.1 || c₁.fwd a.2.1 b.2.1)

/-- A field type is *proper* when no object is related to itself and the reverse of a forward
pair is not related. -/
def FieldType.Proper {O : Type*} (c : FieldType O) : Prop :=
  (∀ x, c.rel x x = false) ∧ ∀ x y, c.fwd x y = true → c.rel y x = false

theorem typeL_proper : typeL.Proper := by
  refine ⟨?_, ?_⟩ <;> unfold typeL <;> decide

theorem typeF_proper : typeF.Proper := by
  refine ⟨?_, ?_⟩ <;> unfold typeF <;> decide

theorem typeE_proper : typeE.Proper := by
  refine ⟨?_, ?_⟩ <;> unfold typeE <;> decide

variable [Fintype O₀] [Fintype O₁] [Fintype Λ]

/-- The edge set of `G_{φ₀φ₁}`. -/
def twoLayerEdges (c₀ : FieldType O₀) (c₁ : FieldType O₁) (Λ : Type*) [Fintype Λ] :
    Finset ((O₀ × O₁ × Λ) × (O₀ × O₁ × Λ)) :=
  univ.filter fun e => twoLayerEdge c₀ c₁ e.1 e.2 = true

omit [Fintype Λ] in
theorem mem_twoLayerEdges (c₀ : FieldType O₀) (c₁ : FieldType O₁) {Λ : Type*} [Fintype Λ]
    (e : (O₀ × O₁ × Λ) × (O₀ × O₁ × Λ)) :
    e ∈ twoLayerEdges c₀ c₁ Λ ↔ twoLayerEdge c₀ c₁ e.1 e.2 = true := by
  unfold twoLayerEdges
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- **The two-layer graph `G_{φ₀φ₁}`**, an oriented graph for proper field types
(`lem:upper-geometry`(a)). -/
def twoLayerGraph (c₀ : FieldType O₀) (c₁ : FieldType O₁) (h₀ : c₀.Proper) (h₁ : c₁.Proper)
    (Λ : Type*) [Fintype Λ] : OrientedGraph (O₀ × O₁ × Λ) where
  E := twoLayerEdges c₀ c₁ Λ
  loopless u := by
    rw [mem_twoLayerEdges]
    simp only [twoLayerEdge, h₀.1 u.1, Bool.false_and, Bool.false_eq_true, not_false_eq_true]
  oriented u v := by
    rw [mem_twoLayerEdges, mem_twoLayerEdges]
    simp only [twoLayerEdge, Bool.and_eq_true, Bool.or_eq_true]
    rintro ⟨⟨_, _⟩, hf | hf⟩ ⟨⟨h0, h1⟩, _⟩
    · rw [h₀.2 _ _ hf] at h0
      exact Bool.false_ne_true h0
    · rw [h₁.2 _ _ hf] at h1
      exact Bool.false_ne_true h1

omit [Fintype Λ] in
theorem mem_twoLayerGraph (c₀ : FieldType O₀) (c₁ : FieldType O₁) (h₀ : c₀.Proper)
    (h₁ : c₁.Proper) {Λ : Type*} [Fintype Λ] (e : (O₀ × O₁ × Λ) × (O₀ × O₁ × Λ)) :
    e ∈ (twoLayerGraph c₀ c₁ h₀ h₁ Λ).E ↔ twoLayerEdge c₀ c₁ e.1 e.2 = true :=
  mem_twoLayerEdges c₀ c₁ e

/-- **The root `G_{LL,2}`.** -/
def rootGraph : OrientedGraph (ZMod 6 × ZMod 6 × Fin 2) :=
  twoLayerGraph typeL typeL typeL_proper typeL_proper (Fin 2)

/-! ## (a): counts in the root -/

/-- Every vertex of the root has exactly 10 out-neighbours. -/
theorem root_outDegree :
    ∀ u : ZMod 6 × ZMod 6 × Fin 2,
      (univ.filter fun v => twoLayerEdge (Λ := Fin 2) typeL typeL u v = true).card = 10 := by
  unfold twoLayerEdge typeL
  decide +kernel

/-- Every vertex of the root has exactly 10 in-neighbours. -/
theorem root_inDegree :
    ∀ v : ZMod 6 × ZMod 6 × Fin 2,
      (univ.filter fun u => twoLayerEdge (Λ := Fin 2) typeL typeL u v = true).card = 10 := by
  unfold twoLayerEdge typeL
  decide +kernel

/-- **The root has 720 edges.** -/
theorem root_card_edges : rootGraph.E.card = 720 := by
  unfold rootGraph twoLayerGraph twoLayerEdges twoLayerEdge typeL
  decide +kernel

/-- **The root contains every query** `(u₀, u₁, ℓ) → (rot u₀, rot u₁, 1 − ℓ)`. -/
theorem root_query (u₀ u₁ : ZMod 6) (ℓ : Fin 2) :
    ((u₀, u₁, ℓ), (rot u₀, rot u₁, 1 - ℓ)) ∈ rootGraph.E := by
  rw [rootGraph, mem_twoLayerGraph]
  revert u₀ u₁ ℓ
  unfold twoLayerEdge typeL
  decide

/-! ## (b): automorphisms -/

/-- A map of objects preserving a field type's relation and forward relation. -/
def FieldType.Preserves {O : Type*} (c : FieldType O) (σ : O → O) : Prop :=
  ∀ x y, c.rel (σ x) (σ y) = c.rel x y ∧ c.fwd (σ x) (σ y) = c.fwd x y

/-- **Coordinatewise relation-preserving bijections are automorphisms**, whatever they do to the
layers (`lem:upper-geometry`(b)). -/
theorem twoLayer_auto (c₀ : FieldType O₀) (c₁ : FieldType O₁) (h₀ : c₀.Proper)
    (h₁ : c₁.Proper) (σ₀ : O₀ ≃ O₀) (σ₁ : O₁ ≃ O₁) (τ : Λ ≃ Λ) (hσ₀ : c₀.Preserves σ₀)
    (hσ₁ : c₁.Preserves σ₁) :
    IsAutomorphism (twoLayerGraph c₀ c₁ h₀ h₁ Λ) (σ₀.prodCongr (σ₁.prodCongr τ)) := by
  intro u v
  simp only [mem_twoLayerGraph, twoLayerEdge, Equiv.prodCongr_apply, Prod.map]
  rw [(hσ₀ u.1 v.1).1, (hσ₀ u.1 v.1).2, (hσ₁ u.2.1 v.2.1).1, (hσ₁ u.2.1 v.2.1).2]

/-- The chamber reflections `u ↦ k − u` (`k = 1, 3, 5`) preserve the `L` relations. -/
theorem typeL_preserves_reflection (k : ZMod 6) (hk : k = 1 ∨ k = 3 ∨ k = 5) :
    typeL.Preserves (chamberRefl k) := by
  unfold FieldType.Preserves
  rcases hk with rfl | rfl | rfl <;> unfold typeL chamberRefl <;> decide

/-- Every permutation of `O_E` preserves the `E` relations (exchangeability). -/
theorem typeE_preserves (σ : Equiv.Perm (Fin 3)) : typeE.Preserves σ := by
  intro x y
  simp only [typeE, ne_eq, EmbeddingLike.apply_eq_iff_eq, and_self]

/-- The chamber reflection as a bijection of `ℤ/6ℤ`. -/
def chamberReflEquiv (k : ZMod 6) : ZMod 6 ≃ ZMod 6 where
  toFun := chamberRefl k
  invFun := chamberRefl k
  left_inv u := by simp [chamberRefl]
  right_inv u := by simp [chamberRefl]

/-- **The chamber reflections of either root coordinate and the layer swap are automorphisms of
the root** (`lem:upper-geometry`(b)). -/
theorem root_automorphisms (k₀ k₁ : ZMod 6) (hk₀ : k₀ = 1 ∨ k₀ = 3 ∨ k₀ = 5)
    (hk₁ : k₁ = 1 ∨ k₁ = 3 ∨ k₁ = 5) (τ : Equiv.Perm (Fin 2)) :
    IsAutomorphism rootGraph ((chamberReflEquiv k₀).prodCongr ((chamberReflEquiv k₁).prodCongr τ)) :=
  twoLayer_auto typeL typeL _ _ _ _ τ (typeL_preserves_reflection k₀ hk₀)
    (typeL_preserves_reflection k₁ hk₁)

/-! ## (c), (d): restrictions -/

/-- **On the plus half `{0, 1, 2}` of an `L` coordinate, `L`'s relations are `F`'s**, so the
subgraph of `G_{L φ, j}` induced there is `G_{F φ, j}` (`lem:upper-geometry`(c)). -/
theorem typeL_restrict_F :
    ∀ o o' : Fin 3, typeL.rel (o.val : ZMod 6) (o'.val : ZMod 6) = typeF.rel o o' ∧
      typeL.fwd (o.val : ZMod 6) (o'.val : ZMod 6) = typeF.fwd o o' := by
  unfold typeL typeF
  decide

omit [Fintype O₁] [Fintype Λ] in
/-- The induced-subgraph statement of (c) for the first coordinate. -/
theorem twoLayer_restrict_first (c₁ : FieldType O₁) (a b : Fin 3 × O₁ × Λ) :
    twoLayerEdge typeL c₁ ((a.1.val : ZMod 6), a.2) ((b.1.val : ZMod 6), b.2) =
      twoLayerEdge typeF c₁ a b := by
  have h := typeL_restrict_F a.1 b.1
  simp only [twoLayerEdge, h.1, h.2]

/-- **`F` and `E` agree on the objects `{0, 1}` and on `{1, 2}`** (`lem:upper-geometry`(d)), and
neither relates an object to itself. -/
theorem typeF_typeE_agree :
    (∀ x y : Fin 3, x ≠ 2 → y ≠ 2 → typeF.rel x y = typeE.rel x y ∧ typeF.fwd x y = typeE.fwd x y) ∧
    (∀ x y : Fin 3, x ≠ 0 → y ≠ 0 → typeF.rel x y = typeE.rel x y ∧ typeF.fwd x y = typeE.fwd x y) ∧
    (∀ x : Fin 3, typeF.rel x x = false ∧ typeE.rel x x = false) := by
  unfold typeF typeE
  decide

omit [Fintype O₀] [Fintype O₁] [Fintype Λ] in
/-- Layer `0` of `G_{φφ',2}` is `G_{φφ',1}`: the edge relation does not depend on the layers. -/
theorem twoLayerEdge_layer (c₀ : FieldType O₀) (c₁ : FieldType O₁) {Λ' : Type*}
    (a b : O₀ × O₁ × Λ) (a' b' : O₀ × O₁ × Λ') (ha : a.1 = a'.1 ∧ a.2.1 = a'.2.1)
    (hb : b.1 = b'.1 ∧ b.2.1 = b'.2.1) : twoLayerEdge c₀ c₁ a b = twoLayerEdge c₀ c₁ a' b' := by
  simp only [twoLayerEdge, ha.1, ha.2, hb.1, hb.2]

end Sarkozy.Labellings
