module

public import Sarkozy.F7Repair.Tail

@[expose] public section

/-!
# The repaired graph `G^new` of a tail record ((F7), "the repair")

`paper/sections/26_upper_comparison.tex`, paragraph "The repair": "Let `G^new` be the oriented
graph whose edges are those of the two copies of `H` together with the `m_×` images, under the
pattern maps of the emission, of the twelve queries: the cross-layer edges of `G` are removed and
the projected queries are imposed. Put `π^new = λ_p(G^new)`. … It is supported in the support of
`π^new`, so it accepts all twelve queries."

* `newGraph f₀ f₁ Q`: the two layers of `G_{φ₀φ₁,2}` (its edges inside a layer) and the cross
  edges `(a, 0) → (b, 1)` for `(a, b) ∈ Q`; an oriented graph (`loopless`, `oriented` proved);
* `queryPairs φ₀ φ₁`, `twelvePairs φ₀ φ₁`: the projected `𝓔₆` queries and the projected twelve
  queries `eq:upper-twelve`; `queryPairs_subset_twelve`;
* **`newGraph_layersSupported`**: both layers of `λ_p(G^new)` lie where `λ_H` is;
* **`newGraph_accepts`**: if `Q` contains the projected `𝓔₆` queries, the emitted `λ_p(G^new)`
  accepts `𝓔₆`;
* **`newGraph_affine`**: `λ_p(G^new)` is square-affine invariant;
* **`TailF7Graph`**, **`TailF7Graph.toTailF7`**: the (F7) inputs with `π^new = λ_p(G^new)`: what
  remains are the nonemptiness of `Inj_p(G^new)` and the analytic constants of (F7).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured
  Sarkozy.TailPrices

/-- The cross edge `(a, 0) → (b, 1)`. -/
def crossEdge {V₀ V₁ : Type*} (q : (V₀ × V₁) × (V₀ × V₁)) : (V₀ × V₁ × Fin 2) × (V₀ × V₁ × Fin 2) :=
  ((q.1.1, q.1.2, 0), (q.2.1, q.2.2, 1))

/-- The edges of `G^new`: the edges of `G_{φ₀φ₁,2}` inside a layer and the cross edges of `Q`. -/
noncomputable def newEdges (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj))) :
    Finset ((f₀.Obj × f₁.Obj × Fin 2) × (f₀.Obj × f₁.Obj × Fin 2)) := by
  classical exact ((fieldGraph f₀ f₁ (Fin 2)).E.filter fun e => e.1.2.2 = e.2.2.2) ∪ Q.image crossEdge

theorem mem_newEdges (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj)))
    (e : (f₀.Obj × f₁.Obj × Fin 2) × (f₀.Obj × f₁.Obj × Fin 2)) :
    e ∈ newEdges f₀ f₁ Q ↔ (e ∈ (fieldGraph f₀ f₁ (Fin 2)).E ∧ e.1.2.2 = e.2.2.2) ∨
      ∃ q ∈ Q, crossEdge q = e := by
  classical
  unfold newEdges
  rw [mem_union, mem_filter, mem_image]

theorem crossEdge_layers {V₀ V₁ : Type*} (q : (V₀ × V₁) × (V₀ × V₁)) :
    (crossEdge q).1.2.2 = 0 ∧ (crossEdge q).2.2.2 = 1 := ⟨rfl, rfl⟩

/-- **The repaired graph `G^new`**: the two copies of `H` and the cross edges `Q` from layer `0`
to layer `1`. -/
noncomputable def newGraph (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj))) :
    OrientedGraph (f₀.Obj × f₁.Obj × Fin 2) where
  E := newEdges f₀ f₁ Q
  loopless u h := by
    rcases (mem_newEdges f₀ f₁ Q _).mp h with ⟨h1, _⟩ | ⟨q, _, hq⟩
    · exact (fieldGraph f₀ f₁ (Fin 2)).loopless u h1
    · have h0 := (crossEdge_layers q).1
      have h1 := (crossEdge_layers q).2
      rw [hq] at h0 h1
      rw [h0] at h1
      exact absurd h1 (by decide)
  oriented u v h h' := by
    rcases (mem_newEdges f₀ f₁ Q _).mp h with ⟨h1, hl⟩ | ⟨q, _, hq⟩
    · rcases (mem_newEdges f₀ f₁ Q _).mp h' with ⟨h1', _⟩ | ⟨q', _, hq'⟩
      · exact (fieldGraph f₀ f₁ (Fin 2)).oriented u v h1 h1'
      · have a := (crossEdge_layers q').1
        have b := (crossEdge_layers q').2
        rw [hq'] at a b
        simp only at hl a b
        rw [a, b] at hl
        exact absurd hl (by decide)
    · rcases (mem_newEdges f₀ f₁ Q _).mp h' with ⟨_, hl'⟩ | ⟨q', _, hq'⟩
      · have a := (crossEdge_layers q).1
        have b := (crossEdge_layers q).2
        rw [hq] at a b
        simp only at hl' a b
        rw [a, b] at hl'
        exact absurd hl' (by decide)
      · have a := (crossEdge_layers q).1
        have b := (crossEdge_layers q').1
        have c := (crossEdge_layers q).2
        rw [hq] at a c
        rw [hq'] at b
        simp only at a b c
        rw [b] at c
        exact absurd c (by decide)

/-- The projected `𝓔₆` queries `((φ₀ 0, φ₁ j), (φ₀ 2, φ₁ (rot j)))`. -/
noncomputable def queryPairs {O₀ O₁ : Type*} [DecidableEq O₀] [DecidableEq O₁]
    (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) : Finset ((O₀ × O₁) × (O₀ × O₁)) :=
  univ.image fun j : Chamber => ((φ₀ 0, φ₁ j), (φ₀ 2, φ₁ (chamberRotation j)))

/-- The projected twelve queries `eq:upper-twelve`:
`((φ₀ u, φ₁ v), (φ₀ (rot u), φ₁ (rot v)))`, `u ∈ {0, 5}`. -/
noncomputable def twelvePairs {O₀ O₁ : Type*} [DecidableEq O₀] [DecidableEq O₁]
    (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) : Finset ((O₀ × O₁) × (O₀ × O₁)) :=
  (({0, 5} : Finset Chamber) ×ˢ (univ : Finset Chamber)).image fun uv =>
    ((φ₀ uv.1, φ₁ uv.2), (φ₀ (chamberRotation uv.1), φ₁ (chamberRotation uv.2)))

/-- The twelve queries contain `𝓔₆` (the queries with `u = 0`). -/
theorem queryPairs_subset_twelve {O₀ O₁ : Type*} [DecidableEq O₀] [DecidableEq O₁]
    (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) : queryPairs φ₀ φ₁ ⊆ twelvePairs φ₀ φ₁ := by
  intro e he
  obtain ⟨j, _, rfl⟩ := mem_image.mp he
  refine mem_image.mpr ⟨(0, j), mem_product.mpr ⟨by simp, mem_univ _⟩, ?_⟩
  have h2 : chamberRotation 0 = 2 := by decide
  simp only [h2]

variable {p : ℕ} [Fact p.Prime]

/-- Each layer of a labelling of `G^new` is a labelling of `H = G_{φ₀φ₁,1}`. -/
theorem newLayer_feasible (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj)))
    (k : Fin 2) (y : f₀.Obj × f₁.Obj × Fin 2 → ZMod p)
    (hy : y ∈ injLabellings (ZMod p) (newGraph f₀ f₁ Q)) :
    (fun o : f₀.Obj × f₁.Obj × Fin 1 => y (o.1, o.2.1, k)) ∈
      injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 1)) := by
  rw [mem_injLabellings_iff_feasible] at hy ⊢
  obtain ⟨hinj, hedge⟩ := hy
  refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
  · have h := hinj _ (mem_univ _) _ (mem_univ _) hab
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 (Subsingleton.elim _ _))
  · have he' : ((e.1.1, e.1.2.1, k), (e.2.1, e.2.2.1, k)) ∈ (fieldGraph f₀ f₁ (Fin 2)).E := by
      simp only [fieldGraph, mem_twoLayerGraph] at he ⊢
      exact he
    have hn : ((e.1.1, e.1.2.1, k), (e.2.1, e.2.2.1, k)) ∈ (newGraph f₀ f₁ Q).E :=
      (mem_newEdges f₀ f₁ Q _).mpr (Or.inl ⟨he', rfl⟩)
    exact hedge _ hn (mem_univ _) (mem_univ _)

variable (hne : TailNonempty p)

/-- **Both layers of `λ_p(G^new)` lie where `λ_H` is** (the new graph keeps the old halves). -/
theorem newGraph_layersSupported (f₀ f₁ : FType)
    (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj)))
    (hN : (injLabellings (ZMod p) (newGraph f₀ f₁ Q)).Nonempty) :
    LayersSupported (graphLaw (newGraph f₀ f₁ Q) hN) (tailHalf p hne f₀ f₁) := by
  intro y hy
  have hfeas : y ∈ injLabellings (ZMod p) (newGraph f₀ f₁ Q) :=
    (graphLaw_weight_ne_zero _ _ _).mp hy
  have key : ∀ k : Fin 2, (tailHalf p hne f₀ f₁).weight (layerOf y k) ≠ 0 := by
    intro k
    set y' : f₀.Obj × f₁.Obj × Fin 1 → ZMod p := fun o => y (o.1, o.2.1, k) with hy'
    have hw : (graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y' ≠ 0 :=
      (graphLaw_weight_ne_zero _ _ _).mpr (newLayer_feasible f₀ f₁ Q k _ hfeas)
    have hpos : 0 < (graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y' :=
      lt_of_le_of_ne ((graphLaw _ (hne.one f₀ f₁)).nonneg y') (Ne.symm hw)
    have hmap : (fun o : f₀.Obj × f₁.Obj => y' (o.1, o.2, 0)) = layerOf y k := rfl
    change (∑ y'', if (fun o : f₀.Obj × f₁.Obj => y'' (o.1, o.2, 0)) = layerOf y k then
      (graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)).weight y'' else 0) ≠ 0
    apply ne_of_gt
    refine Finset.sum_pos' (fun y'' _ => ?_) ⟨y', mem_univ _, ?_⟩
    · split_ifs
      · exact (graphLaw _ (hne.one f₀ f₁)).nonneg y''
      · exact le_rfl
    · simp only [hmap, ↓reduceIte]
      exact hpos
  exact ⟨key 0, key 1⟩

omit [Fact p.Prime] in
/-- **The emitted `λ_p(G^new)` accepts `𝓔₆`** when `Q` contains the projected `𝓔₆` queries. -/
theorem newGraph_accepts (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj)))
    (φ₀ : ZMod 6 → f₀.Obj) (φ₁ : ZMod 6 → f₁.Obj)
    (hQ : ∀ j : Chamber, ((φ₀ 0, φ₁ j), (φ₀ 2, φ₁ (chamberRotation j))) ∈ Q)
    [Fact p.Prime] (hN : (injLabellings (ZMod p) (newGraph f₀ f₁ Q)).Nonempty)
    (z : Slot → ZMod p) (hz : (emit (graphLaw (newGraph f₀ f₁ Q) hN) (upEmission φ₀ φ₁)).weight z ≠ 0)
    (j : Chamber) : quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  change (∑ y, if y ∘ upEmission φ₀ φ₁ = z then (graphLaw (newGraph f₀ f₁ Q) hN).weight y
    else 0) ≠ 0 at hz
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hφ : y ∘ upEmission φ₀ φ₁ = z := by
    by_contra hne'
    simp only [hne', ↓reduceIte] at hy
    exact hy rfl
  simp only [hφ, ↓reduceIte] at hy
  have hfeas := (mem_injLabellings_iff_feasible _ _).mp ((graphLaw_weight_ne_zero _ _ _).mp hy)
  have hedge : crossEdge ((φ₀ 0, φ₁ j), (φ₀ 2, φ₁ (chamberRotation j))) ∈ (newGraph f₀ f₁ Q).E :=
    (mem_newEdges f₀ f₁ Q _).mpr (Or.inr ⟨_, hQ j, rfl⟩)
  have h := hfeas.2 _ hedge (mem_univ _) (mem_univ _)
  rw [← hφ]
  exact h

/-- **`λ_p(G^new)` is square-affine invariant.** -/
theorem newGraph_affine (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj)))
    (hN : (injLabellings (ZMod p) (newGraph f₀ f₁ Q)).Nonempty) (α β : ZMod p)
    (hα : quadraticChar (ZMod p) α = 1) (y : f₀.Obj × f₁.Obj × Fin 2 → ZMod p) :
    (graphLaw (newGraph f₀ f₁ Q) hN).weight (fun w => α * y w + β) =
      (graphLaw (newGraph f₀ f₁ Q) hN).weight y :=
  graphLaw_weight_affine' p _ hN hα β y

/-- **The (F7) inputs of a changed tail record with `π^new = λ_p(G^new)`**. *Hypotheses*: the cross
edges `Q` (containing the projected `𝓔₆` queries; the paper takes the twelve, `twelvePairs`), the
nonemptiness of `Inj_p(G^new)`, and the analytic data of (F7) for `λ_p(G^new)`: the one-way data
(`U`, `ρ_new`, `K_∞`, the gate) with targets `μ^old`, and `ρ_old` with its bound. -/
structure TailF7Graph (t : PType × PType) (φ : t.1.Pat × t.2.Pat) where
  /-- The imposed cross pairs. -/
  Q : Finset ((t.1.field.Obj × t.2.field.Obj) × (t.1.field.Obj × t.2.field.Obj))
  /-- `Q` contains the projected `𝓔₆` queries. -/
  hQ : ∀ j : Chamber,
    ((t.1.pat φ.1 0, t.2.pat φ.2 j), (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j))) ∈ Q
  /-- `Inj_p(G^new)` is nonempty. -/
  hN : (injLabellings (ZMod p) (newGraph t.1.field t.2.field Q)).Nonempty
  /-- The one-way data of `λ_p(G^new)` with targets `μ^old`. -/
  D : OneWayData (pairLaw (graphLaw (newGraph t.1.field t.2.field Q) hN) lay0 lay1)
    (oldHalf (tailOld p hne t)) (oldHalf (tailOld p hne t))
  /-- `ρ_old`. -/
  ρold : ℝ
  ρold_nonneg : 0 ≤ ρold
  /-- `ρ(π^old) ≤ ρ_old` relative to `μ^old`. -/
  old_corr : ∀ h k, (oldHalf (tailOld p hne t)).expect h = 0 →
    (oldHalf (tailOld p hne t)).expect k = 0 →
    |(tailOld p hne t).expect (fun y => h (lay0 y) * k (lay1 y))| ≤
      ρold * nrm (oldHalf (tailOld p hne t)) h * nrm (oldHalf (tailOld p hne t)) k

variable {hne}

/-- **`TailF7` from `G^new`**: support, acceptance and invariance of `π^new` are proved. -/
noncomputable def TailF7Graph.toTailF7 {t : PType × PType} {φ : t.1.Pat × t.2.Pat}
    (G : TailF7Graph hne t φ) : TailF7 hne t φ where
  data :=
    { lamN := graphLaw (newGraph t.1.field t.2.field G.Q) G.hN
      suppN := newGraph_layersSupported hne _ _ G.Q G.hN
      D := G.D
      ρold := G.ρold
      ρold_nonneg := G.ρold_nonneg
      old_corr := G.old_corr }
  accepts z hz j := newGraph_accepts _ _ G.Q _ _ G.hQ G.hN z hz j
  inv α β hα y := newGraph_affine _ _ G.Q G.hN α β hα y

end Sarkozy.F7Repair
