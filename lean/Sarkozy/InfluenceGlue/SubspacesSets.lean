module

public import Sarkozy.InfluenceGlue.Subspaces

/-!
# `lem:mid:subspaces` for sets of vertices

The statements of `lem:mid:subspaces` in the paper's generality: disjoint nonempty sets
`β, β'` of free vertices in (ii) and (iii), and the description of `V_A` as an intersection
in (i). `Sarkozy.InfluenceGlue.Subspaces` has the single-vertex forms used by
`lem:mid:allpin`.

* (i) `coordSubspace_free_eq_const`: `V_{F'}` is the constants;
  `coordSubspace_eq_inf_iInf`: `V_A = V_∅ ⊓ ⨅_{i ∈ A} V_{{i}}`, i.e. the paper's definition
  `V_A = ⋂_{i ∈ A} V_i` agrees with the functions of `y_{F' \ A}`.
* (ii) `friedrichsCos_coordSubspace_le`: if `ρ(y_β; y_{β'} | y_{U \ (β ∪ β')} = z) ≤ ε̄` for
  every feasible `z` extending `s'`, then `cos∠(V_β, V_{β'}) ≤ ε̄`.
* (iii) `friedrichsCos_coordSubspace_compl_eq_maxCorr`:
  `cos∠(V_{F' \ β'}, V_{F' \ β}) = ρ(y_β; y_{β'} | y_{S'} = s')`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.InfluenceGlue

open Sarkozy Sarkozy.Peyre Sarkozy.Angles Sarkozy.Influence

section Symm

variable {Ω : Type*} [Fintype Ω] {α β : Type*}

theorem corrSet_comm (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) :
    corrSet μ X Y = corrSet μ Y X := by
  ext c
  constructor <;> rintro ⟨f, g, hf, hg, hf2, hg2, rfl⟩ <;>
    exact ⟨g, f, hg, hf, hg2, hf2, by simp_rw [mul_comm]⟩

/-- The maximal correlation is symmetric. -/
theorem maxCorr_comm (μ : FiniteLaw Ω) (X : Ω → α) (Y : Ω → β) :
    maxCorr μ X Y = maxCorr μ Y X := by
  rw [maxCorr, maxCorr, corrSet_comm]

end Symm

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [NeZero p]

/-- The labels `y_β = (ω v)_{v ∈ β}`. -/
def labels (β : Finset U) (ω : U → ZMod p) : β → ZMod p := fun v => ω v

omit [Fintype U] [DecidableEq U] [NeZero p] in
theorem labels_eq_iff {β : Finset U} {ω ω' : U → ZMod p} :
    labels β ω = labels β ω' ↔ ∀ v ∈ β, ω v = ω' v := by
  constructor
  · intro h v hv
    exact congrFun h ⟨v, hv⟩
  · intro h
    funext v
    exact h v v.2

omit [NeZero p] in
/-- The event `{y_{U \ B} = z} ∩ {y_{S'} = s'}` is the full pinning of `U \ B` by `z`
(extended arbitrarily on `B`), when it is nonempty and `B` avoids `S'`. -/
theorem event_eq_pinEvent_compl (S' : Finset U) (s' : U → ZMod p) {B : Finset U}
    (hB : ∀ v ∈ B, v ∉ S') (z : {u // u ∉ B} → ZMod p) {ω₀ : U → ZMod p}
    (hω₀ : restr B ω₀ = z) (hω₀S : pinEvent S' s' ω₀) :
    (fun ω => restr B ω = z ∧ pinEvent S' s' ω) =
      pinEvent (Finset.univ \ B) (fun u => if h : u ∉ B then z ⟨u, h⟩ else 0) := by
  have hmem : ∀ v, v ∈ Finset.univ \ B ↔ v ∉ B := fun v => by simp
  funext ω
  apply propext
  constructor
  · rintro ⟨hz, -⟩ v hv
    have hv' := (hmem v).mp hv
    show ω v = (if h : v ∉ B then z ⟨v, h⟩ else 0)
    rw [dite_eq_left hv', ← hz]
    rfl
  · intro hpin
    have hz : restr B ω = z := by
      funext u
      have := hpin u ((hmem u).mpr u.2)
      change ω u = (if h : (u : U) ∉ B then z ⟨u, h⟩ else 0) at this
      rw [dite_eq_left u.2] at this
      exact this
    refine ⟨hz, fun v hv => ?_⟩
    have hvB : v ∉ B := fun h => hB v h hv
    have h1 : ω v = z ⟨v, hvB⟩ := congrFun hz ⟨v, hvB⟩
    have h2 : ω₀ v = z ⟨v, hvB⟩ := congrFun hω₀ ⟨v, hvB⟩
    rw [h1, ← h2]
    exact hω₀S v hv

section Pinned

variable (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)

/-- **`lem:mid:subspaces` (i), the constants**: `V_{F'}` is the space of constants. -/
theorem coordSubspace_free_eq_const (S' : Finset U) (s' : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) :
    coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (free S') =
      l2Const (condLaw (graphLaw G p hInj) (pinEvent S' s') h) := by
  have hsupp := condLaw_graphLaw_weight_ne_zero G hInj S' s' h
  refine l2_congr fun ω ω' hω hω' => ?_
  obtain ⟨-, hωS⟩ := (hsupp ω).mp hω
  obtain ⟨-, hω'S⟩ := (hsupp ω').mp hω'
  refine ⟨fun _ => rfl, fun _ => restr_eq_iff.mpr fun u hu => ?_⟩
  have huS : u ∈ S' := by
    by_contra h'
    exact hu (mem_free.mpr h')
  rw [hωS u huS, hω'S u huS]

/-- **`lem:mid:subspaces` (i), the intersection description**: for a set `A` of free
vertices, `V_A = V_∅ ⊓ ⨅_{i ∈ A} V_{{i}}`. So the paper's `V_A = ⋂_{i ∈ A} V_i` (with
`V_∅ = L²(μ_{S',s'})`) is the space of functions of `y_{F' \ A}`. -/
theorem coordSubspace_eq_inf_iInf {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) (A : Finset U)
    (hA : ∀ v ∈ A, v ∉ S') :
    coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) A =
      coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) ∅ ⊓
        ⨅ i ∈ A, coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) {i} := by
  set ν := condLaw (graphLaw G p hInj) (pinEvent S' s') h with hν
  induction A using Finset.induction_on with
  | empty =>
    simp
  | insert a A haA ih =>
    have hA' : ∀ v ∈ A, v ∉ S' := fun v hv => hA v (Finset.mem_insert_of_mem hv)
    have ha : a ∉ S' := hA a (Finset.mem_insert_self a A)
    have hins : insert a A = {a} ∪ A := by
      ext v
      simp
    have hsplit : coordSubspace ν {a} ⊓ coordSubspace ν A = coordSubspace ν ({a} ∪ A) :=
      coordSubspace_inf G hInj hw hconn S' s' hΔ h (B := {a}) (B' := A)
        (fun v hv => by
          rcases Finset.mem_union.mp hv with hv | hv
          · rw [Finset.mem_singleton.mp hv]; exact ha
          · exact hA' v hv)
    have hlhs : coordSubspace ν (insert a A) = coordSubspace ν {a} ⊓ coordSubspace ν A := by
      rw [hins]
      exact hsplit.symm
    rw [hlhs, ih hA', Finset.iInf_insert]
    ac_rfl

/-- **`lem:mid:subspaces` (ii).** Let `β, β'` be sets of free vertices of a feasible pinning
`(S', s')` (the paper takes them disjoint and nonempty; the proof does not need this), and
`ε̄ ≥ 0` with `ρ(y_β; y_{β'} | y_{U \ (β ∪ β')} = z) ≤ ε̄` for every feasible `z` that extends
`s'`. Then `cos∠(V_β, V_{β'}) ≤ ε̄`. -/
theorem friedrichsCos_coordSubspace_le (S' : Finset U) (s' : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) {β β' : Finset U}
    (hβ : ∀ v ∈ β, v ∉ S') (hβ' : ∀ v ∈ β', v ∉ S') {ε : ℝ} (hε : 0 ≤ ε)
    (hpin : ∀ (z : U → ZMod p) (hz : 0 < prob (graphLaw G p hInj)
        (pinEvent (Finset.univ \ (β ∪ β')) z)), pinEvent S' s' z →
      maxCorr (condLaw (graphLaw G p hInj) (pinEvent (Finset.univ \ (β ∪ β')) z) hz)
        (labels β) (labels β') ≤ ε) :
    friedrichsCos (coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) β)
      (coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) β') ≤ ε := by
  set μ := graphLaw G p hInj with hμ
  set ν := condLaw μ (pinEvent S' s') h with hν
  refine friedrichsCos_l2_le_of_cond ν (labels β') (labels β) (restr (β ∪ β')) (restr β)
    (restr β') hε ?_ ?_ ?_ ?_ ?_
  · intro ω ω' hX hZ
    refine restr_eq_iff.mpr fun u hu => ?_
    by_cases hu' : u ∈ β'
    · exact labels_eq_iff.mp hX u hu'
    · exact restr_eq_iff.mp hZ u (by simp [hu, hu'])
  · intro ω ω' hY hZ
    refine restr_eq_iff.mpr fun u hu => ?_
    by_cases hu' : u ∈ β
    · exact labels_eq_iff.mp hY u hu'
    · exact restr_eq_iff.mp hZ u (by simp [hu, hu'])
  · intro ω ω' hA
    exact restr_eq_iff.mpr fun u hu => restr_eq_iff.mp hA u (fun h' => hu
      (Finset.mem_union_left _ h'))
  · intro ω ω' hB
    exact restr_eq_iff.mpr fun u hu => restr_eq_iff.mp hB u (fun h' => hu
      (Finset.mem_union_right _ h'))
  · intro z hz
    have hFE := prob_and_pos_of_cond μ (pinEvent S' s') h _ hz
    rw [cond_cond μ (pinEvent S' s') h _ hz hFE]
    obtain ⟨ω₀, hω₀z, hω₀w⟩ := exists_of_prob_pos hz
    have hω₀S : pinEvent S' s' ω₀ :=
      ((condLaw_graphLaw_weight_ne_zero G hInj S' s' h ω₀).mp hω₀w).2
    have hBS : ∀ v ∈ β ∪ β', v ∉ S' := fun v hv => by
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hβ v hv
      · exact hβ' v hv
    have hev := event_eq_pinEvent_compl S' s' hBS z hω₀z hω₀S
    set z' : U → ZMod p := fun u => if h : u ∉ β ∪ β' then z ⟨u, h⟩ else 0 with hz'
    have h' : 0 < prob μ (pinEvent (Finset.univ \ (β ∪ β')) z') := hev ▸ hFE
    rw [cond_congr μ hev hFE h', maxCorr_comm]
    refine hpin z' h' fun v hv => ?_
    have hvB : v ∉ β ∪ β' := fun h'' => hBS v h'' hv
    have h1 : z' v = z ⟨v, hvB⟩ := by simp only [hz', dite_eq_left hvB]
    rw [h1, ← congrFun hω₀z ⟨v, hvB⟩]
    exact hω₀S v hv

/-- **`lem:mid:subspaces` (iii).** For disjoint sets `β, β'` of free vertices of a feasible
pinning `(S', s')`, `cos∠(V_{F' \ β'}, V_{F' \ β}) = ρ(y_β; y_{β'} | y_{S'} = s')`. -/
theorem friedrichsCos_coordSubspace_compl_eq_maxCorr {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) {β β' : Finset U}
    (hβ : β ⊆ free S') (hβ' : β' ⊆ free S') (hdisj : Disjoint β β') :
    friedrichsCos
        (coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (free S' \ β'))
        (coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (free S' \ β)) =
      maxCorr (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (labels β) (labels β') := by
  set ν := condLaw (graphLaw G p hInj) (pinEvent S' s') h with hν
  have hsupp := condLaw_graphLaw_weight_ne_zero G hInj S' s' h
  -- `V_{F' \ γ}` is `L²(y_γ)` on the completions
  have hcompl : ∀ γ : Finset U, γ ⊆ free S' →
      coordSubspace ν (free S' \ γ) = l2 ν (labels γ) := by
    intro γ hγ
    refine l2_congr fun ω ω' hω hω' => ?_
    obtain ⟨-, hωS⟩ := (hsupp ω).mp hω
    obtain ⟨-, hω'S⟩ := (hsupp ω').mp hω'
    constructor
    · intro hr
      exact labels_eq_iff.mpr fun v hv => restr_eq_iff.mp hr v (fun h' =>
        (Finset.mem_sdiff.mp h').2 hv)
    · intro hl
      refine restr_eq_iff.mpr fun u hu => ?_
      by_cases huγ : u ∈ γ
      · exact labels_eq_iff.mp hl u huγ
      · have huS : u ∈ S' := by
          by_contra h'
          exact hu (Finset.mem_sdiff.mpr ⟨mem_free.mpr h', huγ⟩)
        rw [hωS u huS, hω'S u huS]
  -- `L²(y_{β'}) ⊓ L²(y_β)` is the constants
  have hinf : l2 ν (labels β') ⊓ l2 ν (labels β) = l2Const ν := by
    refine le_antisymm (l2_inf_le fun φ ψ hagree ω ω' hω hω' _ => ?_)
      (le_inf (l2Const_le ν _) (l2Const_le ν _))
    obtain ⟨hωI, hωS⟩ := (hsupp ω).mp hω
    obtain ⟨hω'I, hω'S⟩ := (hsupp ω').mp hω'
    refine funOf_disjoint_const G hw hconn S' s' hΔ hdisj.symm (fun ω => φ (labels β' ω)) ?_
      ?_ hωI hωS hω'I hω'S
    · intro a b _ _ _ _ hab
      show φ (labels β' a) = φ (labels β' b)
      rw [labels_eq_iff.mpr hab]
    · intro a b ha haS hb hbS hab
      show φ (labels β' a) = φ (labels β' b)
      rw [hagree a ((hsupp a).mpr ⟨ha, haS⟩), hagree b ((hsupp b).mpr ⟨hb, hbS⟩),
        labels_eq_iff.mpr hab]
  rw [hcompl β' hβ', hcompl β hβ, friedrichsCos_l2_eq_maxCorr ν _ _ hinf, maxCorr_comm]

end Pinned

end Sarkozy.InfluenceGlue
