module

public import Sarkozy.UpperRepair.NewGraphBlock
public import Sarkozy.PartVLaws.Labellable

@[expose] public section

/-!
# `Inj_p(G^new) ≠ ∅` at every upper and tail prime, from H1 (`lem:graphs:sequential`)

`paper/sections/26_upper_comparison.tex`, "The repair" (`π^new = λ_p(G^new)` must be defined), with
`paper/sections/12_labellings.tex`, `lem:graphs:sequential`. FR's tail inputs and
`OneWayGraphInput` take the nonemptiness of `Inj_p(G^new)` as a hypothesis (`hN`); FR's count
(`F7Repair.nonempty_of_large`) needs `q ≥ 2⁵¹²`. Here it is proved at every prime
`p ≥ 81·10¹² < P₃`, so at every prime of every upper band and of the tail, for the graphs `G^new`
with at most six imposed cross pairs (the six projections `queryPairs` of `𝓔₆`):

* `sameLayer_*_le` (kernel, nine field pairs): inside one layer every vertex of `G_{φ₀φ₁,2}` has at
  most `14` neighbours;
* **`newGraph_degree_le`**: every vertex of `G^new` has at most `14 + |Q| ≤ 20` neighbours;
* **`newGraph_nonempty`**: under Weil's bound at `p ≥ 81·10¹²`, `Inj_p(G^new) ≠ ∅` (V1's
  `injLabellings_nonempty_of_degree` with `threshold_twenty`, as `tailNonempty_explicit`);
* `newGraph_nonempty_block`: the same at every prime of a block;
* **`OneWayGraphInput.ofQueries`**: the one-way input of a record of an upper block with
  `Q = queryPairs` from the analytic data alone (the one-way data of `λ_𝔅(G^new)`, `ρ_old`): the
  cross pairs, their acceptance and `hN` are proved.

The paper's tail graph imposes the twelve queries (`twelvePairs`); with `|Q| ≤ 12` this crude count
would give `26` neighbours, beyond `threshold_twenty`. The formal atom needs only `𝓔₆` (T2's fate,
FR's `queryPairs`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured Sarkozy.Recentering Sarkozy.F7Repair
  Sarkozy.Labellings Sarkozy.PartVLaws

/-! ## Degrees inside one layer (kernel) -/

theorem sameLayer_LL_le : ∀ v : ZMod 6 × ZMod 6 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeL typeL u v = true ∨
      twoLayerEdge typeL typeL v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeL
  decide +kernel

theorem sameLayer_LF_le : ∀ v : ZMod 6 × Fin 3 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeL typeF u v = true ∨
      twoLayerEdge typeL typeF v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeF typeL
  decide +kernel

theorem sameLayer_LE_le : ∀ v : ZMod 6 × Fin 3 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeL typeE u v = true ∨
      twoLayerEdge typeL typeE v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem sameLayer_FL_le : ∀ v : Fin 3 × ZMod 6 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeF typeL u v = true ∨
      twoLayerEdge typeF typeL v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeF typeL
  decide +kernel

theorem sameLayer_FF_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeF typeF u v = true ∨
      twoLayerEdge typeF typeF v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeF
  decide +kernel

theorem sameLayer_FE_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeF typeE u v = true ∨
      twoLayerEdge typeF typeE v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeF typeE
  decide +kernel

theorem sameLayer_EL_le : ∀ v : Fin 3 × ZMod 6 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeE typeL u v = true ∨
      twoLayerEdge typeE typeL v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem sameLayer_EF_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeE typeF u v = true ∨
      twoLayerEdge typeE typeF v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem sameLayer_EE_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge typeE typeE u v = true ∨
      twoLayerEdge typeE typeE v u = true)).card ≤ 14 := by
  unfold twoLayerEdge typeE
  decide +kernel

theorem sameLayer_le (f₀ f₁ : FType) (v : f₀.Obj × f₁.Obj × Fin 2) :
    (univ.filter fun u => u.2.2 = v.2.2 ∧ (twoLayerEdge f₀.rel f₁.rel u v = true ∨
      twoLayerEdge f₀.rel f₁.rel v u = true)).card ≤ 14 := by
  cases f₀ <;> cases f₁
  · exact sameLayer_LL_le v
  · exact sameLayer_LF_le v
  · exact sameLayer_LE_le v
  · exact sameLayer_FL_le v
  · exact sameLayer_FF_le v
  · exact sameLayer_FE_le v
  · exact sameLayer_EL_le v
  · exact sameLayer_EF_le v
  · exact sameLayer_EE_le v

/-! ## The degree of `G^new` and its labellings -/

/-- **Every vertex of `G^new` has at most `14 + |Q|` neighbours**: the edges inside a layer are
those of `G_{φ₀φ₁,2}`, and each imposed pair gives a vertex at most one cross neighbour. -/
theorem newGraph_degree_le (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj)))
    (hQ : Q.card ≤ 6) (v : f₀.Obj × f₁.Obj × Fin 2) : nbrCount (newGraph f₀ f₁ Q) univ v ≤ 20 := by
  classical
  unfold nbrCount
  set S := univ.filter fun u : f₀.Obj × f₁.Obj × Fin 2 => u.2.2 = v.2.2 ∧
    (twoLayerEdge f₀.rel f₁.rel u v = true ∨ twoLayerEdge f₀.rel f₁.rel v u = true) with hS
  set g : (f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj) → f₀.Obj × f₁.Obj × Fin 2 := fun q =>
    if v.2.2 = 1 then (q.1.1, q.1.2, 0) else (q.2.1, q.2.2, 1) with hg
  have hsub : (univ.filter fun u => (u, v) ∈ (newGraph f₀ f₁ Q).E ∨
      (v, u) ∈ (newGraph f₀ f₁ Q).E) ⊆ S ∪ Q.image g := by
    intro u hu
    rw [mem_filter] at hu
    rcases hu.2 with h | h
    · rcases (mem_newEdges f₀ f₁ Q _).mp h with ⟨he, hl⟩ | ⟨q, hq, hqe⟩
      · simp only [fieldGraph, mem_twoLayerGraph] at he
        exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hl, Or.inl he⟩)
      · simp only [crossEdge, Prod.mk.injEq] at hqe
        obtain ⟨h1, h2⟩ := hqe
        refine mem_union_right _ (mem_image.mpr ⟨q, hq, ?_⟩)
        subst h1 h2
        simp [hg]
    · rcases (mem_newEdges f₀ f₁ Q _).mp h with ⟨he, hl⟩ | ⟨q, hq, hqe⟩
      · simp only [fieldGraph, mem_twoLayerGraph] at he
        exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hl.symm, Or.inr he⟩)
      · simp only [crossEdge, Prod.mk.injEq] at hqe
        obtain ⟨h1, h2⟩ := hqe
        refine mem_union_right _ (mem_image.mpr ⟨q, hq, ?_⟩)
        subst h1 h2
        simp [hg]
  calc _ ≤ (S ∪ Q.image g).card := card_le_card hsub
    _ ≤ S.card + (Q.image g).card := card_union_le _ _
    _ ≤ 14 + 6 := add_le_add (sameLayer_le f₀ f₁ v) (card_image_le.trans hQ)

/-- The six projected queries are at most six pairs. -/
theorem queryPairs_card_le {O₀ O₁ : Type*} [DecidableEq O₀] [DecidableEq O₁]
    (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) : (queryPairs φ₀ φ₁).card ≤ 6 := by
  unfold queryPairs
  exact card_image_le.trans (by simp)

/-- **`Inj_p(G^new) ≠ ∅` at every prime `p ≥ 81·10¹²`** under Weil's bound, for at most six
imposed cross pairs (`lem:graphs:sequential`, the empty labelling extends). -/
theorem newGraph_nonempty (p : ℕ) [Fact p.Prime] (hW : WeilBound (ZMod p))
    (hp : (81 * 10 ^ 12 : ℝ) ≤ p) (f₀ f₁ : FType)
    (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj))) (hQ : Q.card ≤ 6) :
    (injLabellings (ZMod p) (newGraph f₀ f₁ Q)).Nonempty := by
  have hq : (81 * 10 ^ 12 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) := by rw [ZMod.card]; exact hp
  exact injLabellings_nonempty_of_degree hW _ (newGraph_degree_le f₀ f₁ Q hQ)
    (threshold_twenty hq (Nat.cast_nonneg _) (card_fieldVertices_le f₀ f₁ (by simp)))

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
/-- `Inj_p(G^new) ≠ ∅` at every prime of a block of primes `≥ 81·10¹²`. -/
theorem newGraph_nonempty_block (hW : ∀ i, WeilBound (ZMod (pr i)))
    (hp : ∀ i, (81 * 10 ^ 12 : ℝ) ≤ pr i) (f₀ f₁ : FType)
    (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj))) (hQ : Q.card ≤ 6) :
    ∀ i, (injLabellings (ZMod (pr i)) (newGraph f₀ f₁ Q)).Nonempty :=
  fun i => newGraph_nonempty (pr i) (hW i) (hp i) f₀ f₁ Q hQ

/-- The six projected queries of a record lie in `queryPairs`. -/
theorem mem_queryPairs (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (j : Chamber) :
    ((t.1.pat φ.1 0, t.2.pat φ.2 j), (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j))) ∈
      queryPairs (t.1.pat φ.1) (t.2.pat φ.2) := by
  unfold queryPairs
  exact mem_image.mpr ⟨j, mem_univ _, rfl⟩

namespace OneWayGraphInput

variable {pr} {hne : UpperNonempty pr} {t : PType × PType} {φ : t.1.Pat × t.2.Pat}

/-- **The one-way input of a record at a block of primes `≥ 81·10¹²` with `Q = queryPairs`, from
the analytic data alone** (`it:record:upper-F7`): the imposed pairs, their acceptance and
`Inj_p(G^new) ≠ ∅` are proved (H1); what is assumed is the one-way data of `λ_𝔅(G^new)` with
targets `μ^old` and the bound `ρ_old`. -/
noncomputable def ofQueries (hW : ∀ i, WeilBound (ZMod (pr i)))
    (hp : ∀ i, (81 * 10 ^ 12 : ℝ) ≤ pr i)
    (D : OneWayData (pairLaw (newBlockLaw pr t (queryPairs (t.1.pat φ.1) (t.2.pat φ.2))
      (newGraph_nonempty_block pr hW hp _ _ _ (queryPairs_card_le _ _))) lay0 lay1)
      (oldHalf (recOld pr hne t)) (oldHalf (recOld pr hne t)))
    (ρold : ℝ) (hρ : 0 ≤ ρold)
    (old_corr : ∀ h k, (oldHalf (recOld pr hne t)).expect h = 0 →
      (oldHalf (recOld pr hne t)).expect k = 0 →
      |(recOld pr hne t).expect (fun y => h (lay0 y) * k (lay1 y))| ≤
        ρold * nrm (oldHalf (recOld pr hne t)) h * nrm (oldHalf (recOld pr hne t)) k) :
    OneWayGraphInput pr hne t φ :=
  ofData (queryPairs (t.1.pat φ.1) (t.2.pat φ.2)) (mem_queryPairs t φ)
    (newGraph_nonempty_block pr hW hp _ _ _ (queryPairs_card_le _ _)) D ρold hρ old_corr

end OneWayGraphInput

end Sarkozy.UpperRepair
