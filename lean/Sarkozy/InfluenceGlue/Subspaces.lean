module

public import Sarkozy.InfluenceGlue.L2
public import Sarkozy.Influence.Connect

/-!
# `lem:mid:subspaces`: coordinate subspaces of `L²(μ_{S',s'})`

Paper `13_cuts_correlations.tex`, `lem:mid:subspaces`. Let `μ = λ_p(G)` be the graph law and
`(S', s')` a feasible pinning, with conditional law `ν = μ(· | y_{S'} = s')`, which is uniform
on the completions `Ω_{S',s'}` (`condLaw_graphLaw_weight_ne_zero`). In `L²(ν)` (realized as a
Euclidean space by `l2Map`, `Sarkozy.InfluenceGlue.L2`) let `V_B = l2 ν (restr B)` be the
functions of `y_{U \ B}`, for `B` a set of free vertices of `(S', s')`; on the completions
this is the paper's space of functions of `y_{F' \ B}`.

* (i) `coordSubspace_inf`: `V_B ⊓ V_{B'} = V_{B ∪ B'}`, by connectivity (`subspaces_funOf`).
* (ii) `friedrichsCos_coordSubspace_singleton_le`: `cos∠(V_{{i}}, V_{{j}}) ≤ ε_ij`, from the
  fully pinned bound `lem:mid:pinpair` (`pinpair`) and `cor:cond-decorrelation`.
* (iii) `friedrichsCos_label_eq_maxCorr`: `cos∠(L²(y_i), L²(y_j)) = ρ(y_i; y_j | y_{S'} = s')`,
  since `L²(y_i) ⊓ L²(y_j)` is the constants (`funOf_disjoint_const`); and
  `coordSubspace_compl_singleton`: `V_{F' \ {j}} = L²(y_j)`.

The count errors enter through `CountErrors G p (free S) w wconn` for a pinning `(S, s)` that
`(S', s')` extends: the first inequality for (ii), the second (connectivity) for (i), (iii).
Statement (ii) is proved for single vertices, which is what `lem:mid:allpin` uses.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.InfluenceGlue

open Sarkozy Sarkozy.Peyre Sarkozy.Angles Sarkozy.Influence

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [NeZero p]

/-- The labels outside `B`: `ω ↦ ω|_{U \ B}`. -/
def restr (B : Finset U) (ω : U → ZMod p) : {u // u ∉ B} → ZMod p := fun u => ω u

omit [Fintype U] [DecidableEq U] [NeZero p] in
theorem restr_eq_iff {B : Finset U} {ω ω' : U → ZMod p} :
    restr B ω = restr B ω' ↔ ∀ u, u ∉ B → ω u = ω' u := by
  constructor
  · intro h u hu
    exact congrFun h ⟨u, hu⟩
  · intro h
    funext u
    exact h u u.2

omit [DecidableEq U] in
theorem graphLaw_weight_ne_zero_iff [DecidableEq U] (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) (ω : U → ZMod p) :
    (graphLaw G p hInj).weight ω ≠ 0 ↔ ω ∈ injLabellings G p := by
  have hc : ((injLabellings G p).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hInj).ne'
  change (if ω ∈ injLabellings G p then 1 / ((injLabellings G p).card : ℝ) else 0) ≠ 0 ↔ _
  split_ifs with h
  · simp [h, hc]
  · simp [h]

/-- The support of `ν = λ_p(G)(· | y_{S'} = s')`: the completions of the pinning. -/
theorem condLaw_graphLaw_weight_ne_zero (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) (S' : Finset U) (s' : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) (ω : U → ZMod p) :
    (condLaw (graphLaw G p hInj) (pinEvent S' s') h).weight ω ≠ 0 ↔
      ω ∈ injLabellings G p ∧ pinEvent S' s' ω := by
  constructor
  · intro hω
    obtain ⟨hE, hw⟩ := cond_weight_ne_zero hω
    exact ⟨(graphLaw_weight_ne_zero_iff G hInj ω).mp hw, hE⟩
  · rintro ⟨hInjω, hE⟩
    rw [cond_weight, ind_of_pos hE, one_mul]
    exact div_ne_zero ((graphLaw_weight_ne_zero_iff G hInj ω).mpr hInjω) h.ne'

/-- The coordinate subspace `V_B` of `L²(ν)`: the functions of `y_{U \ B}`. -/
noncomputable abbrev coordSubspace (ν : FiniteLaw (U → ZMod p)) (B : Finset U) :
    Submodule ℝ (EuclideanSpace ℝ (U → ZMod p)) :=
  l2 ν (restr B)

section Pinned

variable (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)

/-- **`lem:mid:subspaces` (i).** For sets `B, B'` of free vertices of a feasible pinning
`(S', s')` whose free vertices have degree at most `Δ`, and `w^{conn} < 1` satisfying the second
inequality of `eq:mid:standing` with `Δ`: `V_B ⊓ V_{B'} = V_{B ∪ B'}`. -/
theorem coordSubspace_inf {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) {B B' : Finset U}
    (hB : ∀ v ∈ B ∪ B', v ∉ S') :
    coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) B ⊓
        coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) B' =
      coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (B ∪ B') := by
  set ν := condLaw (graphLaw G p hInj) (pinEvent S' s') h with hν
  have hsupp := condLaw_graphLaw_weight_ne_zero G hInj S' s' h
  apply le_antisymm
  · refine l2_inf_le fun φ ψ hagree ω ω' hω hω' hC => ?_
    obtain ⟨hωI, hωS⟩ := (hsupp ω).mp hω
    obtain ⟨hω'I, hω'S⟩ := (hsupp ω').mp hω'
    refine subspaces_funOf G hw hconn S' s' hΔ (B ∪ B') hB (fun ω => φ (restr B ω)) ?_
      hωI hωS hω'I (restr_eq_iff.mp hC)
    intro i hi a b ha haS hb hbS hab
    rcases Finset.mem_union.mp hi with hiB | hiB'
    · congr 1
      exact restr_eq_iff.mpr fun u hu => hab u (fun h => hu (h ▸ hiB))
    · have ha' : ν.weight a ≠ 0 := (hsupp a).mpr ⟨ha, haS⟩
      have hb' : ν.weight b ≠ 0 := (hsupp b).mpr ⟨hb, hbS⟩
      show φ (restr B a) = φ (restr B b)
      rw [hagree a ha', hagree b hb']
      congr 1
      exact restr_eq_iff.mpr fun u hu => hab u (fun h => hu (h ▸ hiB'))
  · refine le_inf (l2_mono fun ω ω' _ _ hE => ?_) (l2_mono fun ω ω' _ _ hE => ?_)
    · exact restr_eq_iff.mpr fun u hu =>
        restr_eq_iff.mp hE u (fun h => hu (Finset.mem_union_left _ h))
    · exact restr_eq_iff.mpr fun u hu =>
        restr_eq_iff.mp hE u (fun h => hu (Finset.mem_union_right _ h))

omit [NeZero p] in
/-- The event `{y_{U \ {i,j}} = z} ∩ {y_{S'} = s'}` is a full pinning of `U \ {i, j}`, when it
has positive probability. -/
theorem event_eq_pinEvent_offPair (S' : Finset U) (s' : U → ZMod p) {i j : U}
    (hi : i ∉ S') (hj : j ∉ S') (z : {u // u ∉ ({i, j} : Finset U)} → ZMod p)
    {ω₀ : U → ZMod p} (hω₀ : restr {i, j} ω₀ = z) (hω₀S : pinEvent S' s' ω₀) :
    (fun ω => restr {i, j} ω = z ∧ pinEvent S' s' ω) =
      pinEvent (offPair j i) (fun u => if h : u ∉ ({i, j} : Finset U) then z ⟨u, h⟩ else 0) := by
  have hoff : ∀ v, v ∈ offPair j i ↔ v ∉ ({i, j} : Finset U) := fun v => by
    rw [mem_offPair]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    tauto
  funext ω
  apply propext
  constructor
  · rintro ⟨hz, -⟩ v hv
    have hv' := (hoff v).mp hv
    show ω v = (if h : v ∉ ({i, j} : Finset U) then z ⟨v, h⟩ else 0)
    rw [dite_eq_left hv', ← hz]
    rfl
  · intro hpin
    have hz : restr {i, j} ω = z := by
      funext u
      have := hpin u ((hoff u).mpr u.2)
      change ω u = (if h : (u : U) ∉ ({i, j} : Finset U) then z ⟨u, h⟩ else 0) at this
      rw [dite_eq_left u.2] at this
      exact this
    refine ⟨hz, fun v hv => ?_⟩
    have hvij : v ∉ ({i, j} : Finset U) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hi (h ▸ hv), fun h => hj (h ▸ hv)⟩
    have h1 : ω v = z ⟨v, hvij⟩ := congrFun hz ⟨v, hvij⟩
    have h2 : ω₀ v = z ⟨v, hvij⟩ := congrFun hω₀ ⟨v, hvij⟩
    rw [h1, ← h2]
    exact hω₀S v hv

/-- **`lem:mid:subspaces` (ii)** for single vertices. Let `(S', s')` be a feasible pinning that
extends `(S, s)`, with count errors for `(G, F)`, `F = free S` (first inequality, `w`), and
`SquareShiftBound p`. Then `cos∠(V_{{i}}, V_{{j}}) ≤ ε_ij` for distinct free `i, j` of
`(S', s')`. -/
theorem friedrichsCos_coordSubspace_singleton_le (hsq : SquareShiftBound p) (S : Finset U)
    {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hw : StandingBound p (maxDeg G (free S)) (Fintype.card U) w) (S' : Finset U)
    (s' : U → ZMod p) (hSS' : S ⊆ S') (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s'))
    {i j : U} (hi : i ∉ S') (hj : j ∉ S') (hij : i ≠ j) :
    friedrichsCos (coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) {i})
      (coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) {j}) ≤
        influence G p w i j := by
  set μ := graphLaw G p hInj with hμ
  set ν := condLaw μ (pinEvent S' s') h with hν
  have hiF : i ∈ free S := by
    simp only [free, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h' => hi (hSS' h')
  have hjF : j ∈ free S := by
    simp only [free, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h' => hj (hSS' h')
  have hε : 0 ≤ influence G p w i j := influence_nonneg G p (by linarith) i j
  refine friedrichsCos_l2_le_of_cond ν (fun ω => ω j) (fun ω => ω i) (restr {i, j})
    (restr {i}) (restr {j}) hε ?_ ?_ ?_ ?_ ?_
  · -- `y_{U \ {i}}` is a function of `(y_j, y_{U \ {i,j}})`
    intro ω ω' hX hZ
    refine restr_eq_iff.mpr fun u hu => ?_
    by_cases huj : u = j
    · rw [huj]; exact hX
    · refine restr_eq_iff.mp hZ u ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h' => hu (Finset.mem_singleton.mpr h'), huj⟩
  · intro ω ω' hY hZ
    refine restr_eq_iff.mpr fun u hu => ?_
    by_cases hui : u = i
    · rw [hui]; exact hY
    · refine restr_eq_iff.mp hZ u ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hui, fun h' => hu (Finset.mem_singleton.mpr h')⟩
  · intro ω ω' hA
    refine restr_eq_iff.mpr fun u hu => restr_eq_iff.mp hA u ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
    exact fun h' => hu.1 (Finset.mem_singleton.mp h')
  · intro ω ω' hB
    refine restr_eq_iff.mpr fun u hu => restr_eq_iff.mp hB u ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
    exact fun h' => hu.2 (Finset.mem_singleton.mp h')
  · -- the fully pinned correlations
    intro z hz
    have hFE := prob_and_pos_of_cond μ (pinEvent S' s') h _ hz
    rw [cond_cond μ (pinEvent S' s') h _ hz hFE]
    obtain ⟨ω₀, hω₀z, hω₀w⟩ := exists_of_prob_pos hz
    have hω₀S : pinEvent S' s' ω₀ :=
      ((condLaw_graphLaw_weight_ne_zero G hInj S' s' h ω₀).mp hω₀w).2
    have hev := event_eq_pinEvent_offPair S' s' hi hj z hω₀z hω₀S
    have h' : 0 < prob μ (pinEvent (offPair j i)
        (fun u => if h : u ∉ ({i, j} : Finset U) then z ⟨u, h⟩ else 0)) := hev ▸ hFE
    rw [cond_congr μ hev hFE h']
    have hpp := pinpair G hInj hsq (free S) hw0 hw1 hw hjF hiF (Ne.symm hij) _ h'
    rwa [influence_symm] at hpp

/-- **`lem:mid:subspaces` (iii), intersection.** For distinct free vertices `i, j` of a feasible
pinning, `L²(y_i) ⊓ L²(y_j)` is the constants. -/
theorem l2_label_inf_eq_const {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) {i j : U} (hij : i ≠ j) :
    l2 (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (fun ω => ω i) ⊓
        l2 (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (fun ω => ω j) =
      l2Const (condLaw (graphLaw G p hInj) (pinEvent S' s') h) := by
  set ν := condLaw (graphLaw G p hInj) (pinEvent S' s') h with hν
  have hsupp := condLaw_graphLaw_weight_ne_zero G hInj S' s' h
  refine le_antisymm (l2_inf_le fun φ ψ hagree ω ω' hω hω' _ => ?_)
    (le_inf (l2Const_le ν _) (l2Const_le ν _))
  obtain ⟨hωI, hωS⟩ := (hsupp ω).mp hω
  obtain ⟨hω'I, hω'S⟩ := (hsupp ω').mp hω'
  have hdisj : Disjoint ({i} : Finset U) {j} := Finset.disjoint_singleton.mpr hij
  refine funOf_disjoint_const G hw hconn S' s' hΔ hdisj (fun ω => φ (ω i)) ?_ ?_ hωI hωS
    hω'I hω'S
  · intro a b _ _ _ _ hab
    show φ (a i) = φ (b i)
    rw [hab i (Finset.mem_singleton_self i)]
  · intro a b ha haS hb hbS hab
    show φ (a i) = φ (b i)
    rw [hagree a ((hsupp a).mpr ⟨ha, haS⟩), hagree b ((hsupp b).mpr ⟨hb, hbS⟩),
      hab j (Finset.mem_singleton_self j)]

/-- **`lem:mid:subspaces` (iii).** For distinct free vertices `i, j` of a feasible pinning,
`cos∠(L²(y_i), L²(y_j)) = ρ(y_i; y_j | y_{S'} = s')`. -/
theorem friedrichsCos_label_eq_maxCorr {Δ : ℕ} {wconn : ℝ} (hw : wconn < 1)
    (hconn : StandingBound p (Δ + 1) (2 * Fintype.card U) wconn) (S' : Finset U)
    (s' : U → ZMod p) (hΔ : ∀ v, v ∉ S' → G.deg v ≤ Δ)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) {i j : U} (hij : i ≠ j) :
    friedrichsCos (l2 (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (fun ω => ω i))
      (l2 (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (fun ω => ω j)) =
        maxCorr (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (fun ω => ω i)
          (fun ω => ω j) :=
  friedrichsCos_l2_eq_maxCorr _ _ _ (l2_label_inf_eq_const G hInj hw hconn S' s' hΔ h hij)

/-- On the completions, `V_{F' \ {j}}` (functions of `y_{S' ∪ {j}}`) is `L²(y_j)`. -/
theorem coordSubspace_compl_singleton (S' : Finset U) (s' : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) {B : Finset U} {j : U}
    (hB : ∀ u, u ∉ B ↔ u ∈ S' ∨ u = j) :
    coordSubspace (condLaw (graphLaw G p hInj) (pinEvent S' s') h) B =
      l2 (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (fun ω => ω j) := by
  have hsupp := condLaw_graphLaw_weight_ne_zero G hInj S' s' h
  refine l2_congr fun ω ω' hω hω' => ?_
  obtain ⟨-, hωS⟩ := (hsupp ω).mp hω
  obtain ⟨-, hω'S⟩ := (hsupp ω').mp hω'
  constructor
  · intro hr
    exact restr_eq_iff.mp hr j ((hB j).mpr (Or.inr rfl))
  · intro hj
    refine restr_eq_iff.mpr fun u hu => ?_
    rcases (hB u).mp hu with huS | rfl
    · rw [hωS u huS, hω'S u huS]
    · exact hj

end Pinned

end Sarkozy.InfluenceGlue
