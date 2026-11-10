module

public import Sarkozy.Labellings.GraphLaw

/-!
# Graph laws are invariant under graph automorphisms

`lem:record:fold-identification`(a), `paper/sections/17_completion_repair.tex`.

A vertex bijection `π` that maps the edge set onto itself (`IsAutomorphism`) preserves the
injective strict-square labellings (`mem_injLabellings_comp_iff`). So the graph law, which is
uniform on them, is invariant under the relabelling `z ↦ z ∘ π` (`graphLaw_expect_comp`).

The record graph `G_L` (`recordGraph Λ`) lives on `ℤ/6ℤ × Λ`. Its edges are
`(u, ℓ) → (rot u, ℓ')` for all layers `ℓ, ℓ'`, where `rot` follows the two rotation cycles
`0 → 2 → 4 → 0` and `1 → 5 → 3 → 1`. The reflections `u ↦ k − u` (k ∈ {1, 3, 5}) and the
translation `u ↦ u + 2` are automorphisms of it (`recordGraph_reflection`,
`recordGraph_translation`), each checked by `decide` over `ℤ/6ℤ`. Hence the graph law of
`G_L` is invariant under the group they generate. In particular, at each reflection the law
is symmetric, so it couples two copies of one half law: the first assertion of (a).

The statement here is for one field `F`. The paper's block law `λ_𝔅(G_L)` is the tensor over
the primes of the block, and each factor is invariant. Parts (b)–(d) of the lemma are not
formalized here.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Labellings

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A vertex bijection that maps the edge set onto itself. -/
def IsAutomorphism (G : OrientedGraph W) (π : W ≃ W) : Prop :=
  ∀ u v, (π u, π v) ∈ G.E ↔ (u, v) ∈ G.E

omit [Fintype W] [DecidableEq W] in
theorem IsAutomorphism.symm {G : OrientedGraph W} {π : W ≃ W} (hπ : IsAutomorphism G π) :
    IsAutomorphism G π.symm := by
  intro u v
  have h := hπ (π.symm u) (π.symm v)
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

omit [DecidableEq W] in
theorem feasible_comp_of_auto (G : OrientedGraph W) (π : W ≃ W) (hπ : IsAutomorphism G π)
    (z : W → F) (hz : Feasible F G univ z) : Feasible F G univ (z ∘ π) := by
  obtain ⟨hinj, hedge⟩ := hz
  refine ⟨fun a _ b _ hab => π.injective (hinj _ (mem_univ _) _ (mem_univ _) hab),
    fun e he _ _ => ?_⟩
  obtain ⟨u, v⟩ := e
  exact hedge _ ((hπ u v).mpr he) (mem_univ _) (mem_univ _)

omit [DecidableEq W] in
/-- Automorphisms preserve feasibility. -/
theorem feasible_comp_iff (G : OrientedGraph W) (π : W ≃ W) (hπ : IsAutomorphism G π)
    (z : W → F) : Feasible F G univ (z ∘ π) ↔ Feasible F G univ z := by
  refine ⟨fun h => ?_, feasible_comp_of_auto G π hπ z⟩
  have h' := feasible_comp_of_auto G π.symm hπ.symm (z ∘ π) h
  have he : (z ∘ π) ∘ π.symm = z := by
    funext w
    simp
  rwa [he] at h'

theorem mem_injLabellings_iff_feasible (G : OrientedGraph W) (z : W → F) :
    z ∈ injLabellings F G ↔ Feasible F G univ z := by
  classical
  unfold injLabellings
  simp

/-- **Automorphisms preserve the injective strict-square labellings.** -/
theorem mem_injLabellings_comp_iff (G : OrientedGraph W) (π : W ≃ W) (hπ : IsAutomorphism G π)
    (z : W → F) : z ∘ π ∈ injLabellings F G ↔ z ∈ injLabellings F G := by
  rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
  exact feasible_comp_iff G π hπ z

/-- Relabelling the vertices by a bijection, as an equivalence of labellings. -/
def relabel (π : W ≃ W) : (W → F) ≃ (W → F) where
  toFun z := z ∘ π
  invFun z := z ∘ π.symm
  left_inv z := by funext w; simp
  right_inv z := by funext w; simp

/-- **The graph law is invariant under graph automorphisms.** -/
theorem graphLaw_expect_comp (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    (π : W ≃ W) (hπ : IsAutomorphism G π) (f : (W → F) → ℝ) :
    (graphLaw G hne).expect (fun z => f (z ∘ π)) = (graphLaw G hne).expect f := by
  unfold FiniteLaw.expect
  have hw : ∀ z : W → F, (graphLaw G hne).weight z = (graphLaw G hne).weight (z ∘ π) := by
    intro z
    simp only [graphLaw, mem_injLabellings_comp_iff G π hπ z]
  calc ∑ z, (graphLaw G hne).weight z * f (z ∘ π)
      = ∑ z, (graphLaw G hne).weight (relabel π z) * f (relabel π z) :=
        sum_congr rfl fun z _ => by rw [hw z]; rfl
    _ = ∑ y, (graphLaw G hne).weight y * f y :=
        Fintype.sum_equiv (relabel π) _ _ fun _ => rfl

/-! ## The record graph `G_L` -/

/-- The rotation of the two triangles `0 → 2 → 4 → 0` and `1 → 5 → 3 → 1`. -/
def rot (u : ZMod 6) : ZMod 6 := if u.val % 2 = 0 then u + 2 else u + 4

theorem rot_ne (u : ZMod 6) : rot u ≠ u := by decide +revert

theorem rot_rot_ne (u : ZMod 6) : rot (rot u) ≠ u := by decide +revert

variable (Λ : Type*) [Fintype Λ]

/-- **The record graph `G_L`** on `ℤ/6ℤ × Λ`: edges `(u, ℓ) → (rot u, ℓ')` for all layers. -/
def recordGraph : OrientedGraph (ZMod 6 × Λ) where
  E := univ.filter fun e => e.2.1 = rot e.1.1
  loopless u := by
    simp only [mem_filter, mem_univ, true_and]
    exact fun h => rot_ne u.1 h.symm
  oriented u v := by
    simp only [mem_filter, mem_univ, true_and]
    intro h h'
    rw [h] at h'
    exact rot_rot_ne u.1 h'.symm

theorem mem_recordGraph (e : (ZMod 6 × Λ) × (ZMod 6 × Λ)) :
    e ∈ (recordGraph Λ).E ↔ e.2.1 = rot e.1.1 := by
  simp [recordGraph]

/-- The chamber map `u ↦ k − u` on the first coordinate. -/
def reflectionMap (k : ZMod 6) : ZMod 6 × Λ ≃ ZMod 6 × Λ where
  toFun x := (k - x.1, x.2)
  invFun x := (k - x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The chamber map `u ↦ u + 2` on the first coordinate. -/
def translationMap : ZMod 6 × Λ ≃ ZMod 6 × Λ where
  toFun x := (x.1 + 2, x.2)
  invFun x := (x.1 - 2, x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- **The reflections `u ↦ k − u`, `k ∈ {1, 3, 5}`, are automorphisms of `G_L`**
(`lem:record:fold-identification`(a)). -/
theorem recordGraph_reflection (k : ZMod 6) (hk : k = 1 ∨ k = 3 ∨ k = 5) :
    IsAutomorphism (recordGraph Λ) (reflectionMap Λ k) := by
  have key : ∀ u v : ZMod 6, (k - v = rot (k - u) ↔ v = rot u) := by
    rcases hk with rfl | rfl | rfl <;> decide
  intro u v
  simp only [mem_recordGraph]
  exact key u.1 v.1

/-- **The translation `u ↦ u + 2` is an automorphism of `G_L`**
(`lem:record:fold-identification`(a)). -/
theorem recordGraph_translation : IsAutomorphism (recordGraph Λ) (translationMap Λ) := by
  have key : ∀ u v : ZMod 6, (v + 2 = rot (u + 2) ↔ v = rot u) := by decide
  intro u v
  simp only [mem_recordGraph]
  exact key u.1 v.1

/-- **`lem:record:fold-identification`(a)**: the graph law of `G_L` is invariant under the
reflections `u ↦ k − u` (`k ∈ {1, 3, 5}`) and the translation `u ↦ u + 2`. -/
theorem recordGraphLaw_invariant [DecidableEq Λ] (hne : (injLabellings F (recordGraph Λ)).Nonempty)
    (f : (ZMod 6 × Λ → F) → ℝ) :
    (∀ k : ZMod 6, (k = 1 ∨ k = 3 ∨ k = 5) →
      (graphLaw (recordGraph Λ) hne).expect (fun z => f (z ∘ reflectionMap Λ k)) =
        (graphLaw (recordGraph Λ) hne).expect f) ∧
    (graphLaw (recordGraph Λ) hne).expect (fun z => f (z ∘ translationMap Λ)) =
      (graphLaw (recordGraph Λ) hne).expect f :=
  ⟨fun k hk => graphLaw_expect_comp _ hne _ (recordGraph_reflection Λ k hk) f,
    graphLaw_expect_comp _ hne _ (recordGraph_translation Λ) f⟩

/-! ## The halves `H_{2j}` and the fold graph `G_F` (`lem:record:fold-identification`(c)) -/

/-- The fold graph `G_F` on `{0, 1, 2} × Λ`: edges `(0, ℓ) → (2, ℓ')` for all layers. -/
def foldGraph : OrientedGraph (Fin 3 × Λ) where
  E := univ.filter fun e => e.1.1 = 0 ∧ e.2.1 = 2
  loopless u := by
    simp only [mem_filter, mem_univ, true_and, not_and]
    intro h
    rw [h]
    decide
  oriented u v := by
    simp only [mem_filter, mem_univ, true_and, not_and, and_imp]
    intro hu _ _
    rw [hu]
    decide

theorem mem_foldGraph (e : (Fin 3 × Λ) × (Fin 3 × Λ)) :
    e ∈ (foldGraph Λ).E ↔ e.1.1 = 0 ∧ e.2.1 = 2 := by
  simp [foldGraph]

/-- The half `H_{2j} = {2j, 2j+1, 2j+2}`, read in order: `(o, ℓ) ↦ (2j + o, ℓ)`. -/
def halfEmb (j : Fin 3) (a : Fin 3 × Λ) : ZMod 6 × Λ :=
  (((2 * j.val + a.1.val : ℕ) : ZMod 6), a.2)

omit [Fintype Λ] in
theorem halfEmb_injective (j : Fin 3) : Function.Injective (halfEmb Λ j) := by
  have key : ∀ j o o' : Fin 3, (((2 * j.val + o.val : ℕ) : ZMod 6) =
      ((2 * j.val + o'.val : ℕ) : ZMod 6)) → o = o' := by decide
  intro a b h
  simp only [halfEmb, Prod.mk.injEq] at h
  exact Prod.ext (key j a.1 b.1 h.1) h.2

/-- **Inside `H_{2j}` the only rotation edge is `2j → 2j + 2`**: the subgraph of `G_L` induced
on `H_{2j} × Λ`, read in order, is `G_F`. -/
theorem halfEmb_edge_iff (j : Fin 3) (a b : Fin 3 × Λ) :
    (halfEmb Λ j a, halfEmb Λ j b) ∈ (recordGraph Λ).E ↔ (a, b) ∈ (foldGraph Λ).E := by
  have key : ∀ j o o' : Fin 3, (((2 * j.val + o'.val : ℕ) : ZMod 6) =
      rot ((2 * j.val + o.val : ℕ) : ZMod 6)) ↔ (o = 0 ∧ o' = 2) := by decide
  rw [mem_recordGraph, mem_foldGraph]
  exact key j a.1 b.1

/-- **`lem:record:fold-identification`(c), support**: the restriction of an injective
strict-square labelling of `G_L` to `H_{2j} × Λ`, read in order, is one of `G_F`. -/
theorem restrict_mem_foldGraph [DecidableEq Λ] (j : Fin 3) (z : ZMod 6 × Λ → F)
    (hz : z ∈ injLabellings F (recordGraph Λ)) :
    z ∘ halfEmb Λ j ∈ injLabellings F (foldGraph Λ) := by
  rw [mem_injLabellings_iff_feasible] at hz ⊢
  obtain ⟨hinj, hedge⟩ := hz
  refine ⟨fun a _ b _ hab => halfEmb_injective Λ j (hinj _ (mem_univ _) _ (mem_univ _) hab),
    fun e he _ _ => ?_⟩
  obtain ⟨a, b⟩ := e
  exact hedge _ ((halfEmb_edge_iff Λ j a b).mpr he) (mem_univ _) (mem_univ _)

omit [Fintype Λ] in
theorem halfEmb_succ (j : Fin 3) (hj : j.val < 2) (a : Fin 3 × Λ) :
    halfEmb Λ ⟨j.val + 1, by omega⟩ a = translationMap Λ (halfEmb Λ j a) := by
  simp only [halfEmb, translationMap, Equiv.coe_fn_mk, Prod.mk.injEq, and_true]
  push_cast
  ring

/-- **`lem:record:fold-identification`(c), independence of `j`**: the half marginal of the
graph law of `G_L` on `H_{2j}`, read in order, does not depend on `j`. -/
theorem recordGraphLaw_half_marginal [DecidableEq Λ]
    (hne : (injLabellings F (recordGraph Λ)).Nonempty) (j : Fin 3)
    (f : (Fin 3 × Λ → F) → ℝ) :
    (graphLaw (recordGraph Λ) hne).expect (fun z => f (z ∘ halfEmb Λ j)) =
      (graphLaw (recordGraph Λ) hne).expect (fun z => f (z ∘ halfEmb Λ 0)) := by
  have step : ∀ (k : Fin 3) (hk : k.val < 2),
      (graphLaw (recordGraph Λ) hne).expect (fun z => f (z ∘ halfEmb Λ ⟨k.val + 1, by omega⟩)) =
        (graphLaw (recordGraph Λ) hne).expect (fun z => f (z ∘ halfEmb Λ k)) := by
    intro k hk
    have hfun : (fun z : ZMod 6 × Λ → F => f (z ∘ halfEmb Λ ⟨k.val + 1, by omega⟩)) =
        fun z => (fun y : ZMod 6 × Λ → F => f (y ∘ halfEmb Λ k)) (z ∘ translationMap Λ) := by
      funext z
      congr 1
      funext a
      simp only [Function.comp_apply, halfEmb_succ Λ k hk a]
    rw [hfun]
    exact graphLaw_expect_comp _ hne _ (recordGraph_translation Λ)
      (fun y => f (y ∘ halfEmb Λ k))
  fin_cases j
  · rfl
  · exact step 0 (by decide)
  · exact (step 1 (by decide)).trans (step 0 (by decide))

end Sarkozy.Labellings
