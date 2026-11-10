module

public import Sarkozy.InfluenceGlue.Subspaces
public import Sarkozy.Angles.AllPinBridge
public import Sarkozy.Influence.Corollaries
public import Sarkozy.Influence.SquareShift

/-!
# The pinned-influence chain closed: `lem:mid:allpin` for the graph law, `prop:middle-negative`

`allpin_graph` proves the pairwise bounds of `prop:middle-negative` (a),
`ρ(y_i; y_j | y_{S''} = s'') ≤ [(I - 𝓔)^{-1}]_ij`, for the graph law `λ_p(G)`, every feasible
pinning `(S'', s'')` extending `(S, s)` and distinct free `i, j` of `S''`. This is the
hypothesis `ha` of `Sarkozy.Influence.pinned_influence_b`. Its inputs are only:
* the count errors `CountErrors G p (free S) w wconn` (`eq:mid:standing`);
* `lem:square-shift` (a) as `SquareShiftBound p`, which holds for odd `p`
  (`Sarkozy.Influence.squareShiftBound`);
* `‖𝓔_{FF}‖ ≤ e < 1` and `Q = (I - 𝓔)^{-1}` on `F = free S`.

The proof is `lem:mid:allpin` (`Sarkozy.Angles.allpin_elementary`). It is applied to the
coordinate subspaces of `L²(μ_{S'',s''})` (`lem:mid:subspaces` (i)–(iii),
`Sarkozy.InfluenceGlue.Subspaces`), with the pair bounds of `lem:mid:pinpair`.

Then:
* `middle_negative_a`: `prop:middle-negative` (a), the chain
  `ρ ≤ [(I - 𝓔_{F'F'})^{-1}]_ij ≤ [(I - 𝓔)^{-1}]_ij ≤ ε_ij + e²/(1-e)`;
* `middle_negative_b`: `prop:middle-negative` (b);
* `single_label_maxCorr_le_of_countErrors`: the single-label form of (b) for the empty
  pinning, `ρ(y_v; y_{U \ {v}}) ≤ min{1, Λ + e²/(1-e)}`;
* `_odd` variants, for odd `p`, with no square-shift hypothesis.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.InfluenceGlue

open Sarkozy Sarkozy.Peyre Sarkozy.Angles Sarkozy.Influence

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [NeZero p]

omit [DecidableEq U] [NeZero p] in
theorem maxDeg_mono (G : OrientedGraph U) {F F' : Finset U} (h : F' ⊆ F) :
    maxDeg G F' ≤ maxDeg G F :=
  Finset.sup_mono h

omit [Fintype U] [DecidableEq U] in
theorem standingBound_mono {T T' M : ℕ} {w : ℝ} (h : StandingBound p T M w) (hT : T' ≤ T) :
    StandingBound p T' M w :=
  fun t a sg E' ha hsg haE ht hE' => h t a sg E' ha hsg haE (ht.trans hT) hE'

omit [DecidableEq U] in
/-- Count errors for `(G, F)` are count errors for `(G, F')`, `F' ⊆ F`. -/
theorem countErrors_mono {G : OrientedGraph U} {F F' : Finset U} {w wconn : ℝ}
    (h : CountErrors G p F w wconn) (hF : F' ⊆ F) : CountErrors G p F' w wconn :=
  ⟨h.w_nonneg, h.w_lt_one, h.wconn_nonneg, h.wconn_lt_one,
    standingBound_mono h.first (maxDeg_mono G hF),
    standingBound_mono h.conn (Nat.add_le_add_right (maxDeg_mono G hF) 1)⟩

/-- **`lem:mid:allpin` for the graph law** (the pairwise bounds of `prop:middle-negative` (a)).
For every feasible pinning `(S'', s'')` extending `(S, s)` and distinct free `i, j` of `S''`,
`ρ(y_i; y_j | y_{S''} = s'') ≤ Q_ij`, where `Q = (I - 𝓔)^{-1}` on `F = free S`. This is the
hypothesis `ha` of `pinned_influence_b`. -/
theorem allpin_graph (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    (hsq : SquareShiftBound p) (S : Finset U) (s : U → ZMod p) {w wconn : ℝ}
    (hce : CountErrors G p (free S) w wconn) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, influence G p w i l * Q l j) :
    ∀ (S'' : Finset U) (s'' : U → ZMod p), Extends S'' s'' S s →
      ∀ h : 0 < prob (graphLaw G p hInj) (pinEvent S'' s''), ∀ i ∈ free S'', ∀ j ∈ free S'',
        i ≠ j → maxCorr (condLaw (graphLaw G p hInj) (pinEvent S'' s'') h) (fun ω => ω i)
          (fun ω => ω j) ≤ Q i j := by
  intro S'' s'' hext h i hi j hj hij
  set ν := condLaw (graphLaw G p hInj) (pinEvent S'' s'') h with hν
  have hF' : free S'' ⊆ free S := free_antitone hext.1
  have hΔ : ∀ v, v ∉ S'' → G.deg v ≤ maxDeg G (free S) := fun v hv =>
    Finset.le_sup (f := G.deg) (hF' (mem_free.mpr hv))
  -- the coordinate subspaces, indexed by the subsets of `F' = free S''`
  let emb : free S'' ↪ U := Function.Embedding.subtype _
  let V : Finset (free S'') → Submodule ℝ (EuclideanSpace ℝ (U → ZMod p)) :=
    fun 𝒴 => coordSubspace ν (𝒴.map emb)
  have hmap : ∀ (𝒴 : Finset (free S'')) (v : U), v ∈ 𝒴.map emb → v ∉ S'' := by
    intro 𝒴 v hv
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hv
    exact mem_free.mp a.2
  have hV : ∀ 𝒴 𝒴' : Finset (free S''), V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴') := by
    intro 𝒴 𝒴'
    show coordSubspace ν (𝒴.map emb) ⊓ coordSubspace ν (𝒴'.map emb) =
      coordSubspace ν ((𝒴 ∪ 𝒴').map emb)
    rw [Finset.map_union]
    refine coordSubspace_inf G hInj hce.wconn_lt_one hce.conn S'' s'' hΔ h fun v hv => ?_
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hmap 𝒴 v hv
    · exact hmap 𝒴' v hv
  have hcos : ∀ a b : free S'', a ≠ b →
      friedrichsCos (V {a}) (V {b}) ≤ influence G p w a b := by
    intro a b hab
    show friedrichsCos (coordSubspace ν (({a} : Finset (free S'')).map emb))
      (coordSubspace ν (({b} : Finset (free S'')).map emb)) ≤ _
    rw [Finset.map_singleton, Finset.map_singleton]
    exact friedrichsCos_coordSubspace_singleton_le G hInj hsq S hce.w_nonneg hce.w_lt_one
      hce.first S'' s'' hext.1 h (mem_free.mp a.2) (mem_free.mp b.2)
      (fun h' => hab (Subtype.ext h'))
  have hne : (⟨i, hi⟩ : free S'') ≠ ⟨j, hj⟩ := fun h' => hij (congrArg Subtype.val h')
  have hmain := allpin_elementary (free S) (free S'') hF' (influence G p w)
    (influence_symm G p w) (influence_self G p w)
    (influence_nonneg G p (by linarith [hce.w_nonneg])) he0 he1 hE Q hQ V hV hcos hne
  -- `V_{F' \ {j}} = L²(y_j)` and `V_{F' \ {i}} = L²(y_i)`
  have hcompl : ∀ (k : U) (hk : k ∈ free S''),
      V (Finset.univ \ {⟨k, hk⟩}) = l2 ν (fun ω => ω k) := by
    intro k hk
    refine coordSubspace_compl_singleton G hInj S'' s'' h fun u => ?_
    constructor
    · intro hu
      by_cases huS : u ∈ S''
      · exact Or.inl huS
      · right
        by_contra hne'
        apply hu
        refine Finset.mem_map.mpr ⟨⟨u, mem_free.mpr huS⟩, ?_, rfl⟩
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
        intro h'
        exact hne' (congrArg Subtype.val h')
    · rintro (huS | rfl) hu
      · obtain ⟨a, -, ha⟩ := Finset.mem_map.mp hu
        have ha' : (a : U) = u := ha
        exact mem_free.mp a.2 (by rw [ha']; exact huS)
      · obtain ⟨a, ha, ha'⟩ := Finset.mem_map.mp hu
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at ha
        exact ha (Subtype.ext ha')
  rw [hcompl j hj, hcompl i hi, friedrichsCos_comm,
    friedrichsCos_label_eq_maxCorr G hInj hce.wconn_lt_one hce.conn S'' s'' hΔ h hij] at hmain
  exact hmain

/-- **`prop:middle-negative` (a)**, with only the count errors and `SquareShiftBound p` as
inputs: for a feasible pinning `(S', s')` extending `(S, s)` and distinct free `i, j` of `S'`,
`ρ(y_i; y_j | y_{S'} = s') ≤ [(I - 𝓔_{F'F'})^{-1}]_ij ≤ [(I - 𝓔)^{-1}]_ij ≤ ε_ij + e²/(1-e)`.
Here `Q` and `Q'` are `(I - 𝓔)^{-1}` on `F = free S` and on `F' = free S'`. -/
theorem middle_negative_a (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    (hsq : SquareShiftBound p) (S : Finset U) (s : U → ZMod p) {w wconn : ℝ}
    (hce : CountErrors G p (free S) w wconn) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) (influence G p w) e) (Q Q' : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, influence G p w i l * Q l j)
    (S' : Finset U) (s' : U → ZMod p) (hext : Extends S' s' S s)
    (hQ' : ∀ i ∈ free S', ∀ j ∈ free S',
      Q' i j = (if i = j then 1 else 0) + ∑ l ∈ free S', influence G p w i l * Q' l j)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) {i j : U} (hi : i ∈ free S')
    (hj : j ∈ free S') (hij : i ≠ j) :
    maxCorr (condLaw (graphLaw G p hInj) (pinEvent S' s') h) (fun ω => ω i) (fun ω => ω j) ≤
        Q' i j ∧ Q' i j ≤ Q i j ∧ Q i j ≤ influence G p w i j + e ^ 2 / (1 - e) := by
  have hF' : free S' ⊆ free S := free_antitone hext.1
  -- the first inequality: `allpin_graph` at the pinning `(S', s')` itself
  have hfirst := allpin_graph G hInj hsq S' s' (countErrors_mono hce hF') he0 he1
    (hE.subset hF' hF') Q' hQ' S' s' ⟨Finset.Subset.refl _, fun _ _ => rfl⟩ h i hi j hj hij
  exact pinned_influence_a hF' (influence G p w) Q Q'
    (influence_nonneg G p (by linarith [hce.w_nonneg])) he0 he1 hE hQ hQ' hi hj hij hfirst

/-- **`prop:middle-negative` (b)**, with only the count errors and `SquareShiftBound p` as
inputs: for a feasible pinning `(S', s')` extending `(S, s)` and disjoint `X, Y ⊆ F'`,
`ρ(y_X; y_Y | y_{S'} = s') ≤ min{1, Λ + e²/(1-e)}` for every `Λ ≥ ‖𝓔_{XY}‖`. -/
theorem middle_negative_b (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    (hsq : SquareShiftBound p) (S : Finset U) (s : U → ZMod p) {w wconn : ℝ}
    (hce : CountErrors G p (free S) w wconn) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, influence G p w i l * Q l j)
    (S' : Finset U) (s' : U → ZMod p) (hext : Extends S' s' S s)
    (hS' : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) (X Y : Finset U) (hX : X ⊆ free S')
    (hY : Y ⊆ free S') (hXY : Disjoint X Y) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : OpBound X Y (influence G p w) Λ) :
    maxCorr (condLaw (graphLaw G p hInj) (pinEvent S' s') hS') (fun ω (v : X) => ω v)
      (fun ω (v : Y) => ω v) ≤ min 1 (Λ + e ^ 2 / (1 - e)) :=
  pinned_influence_b (graphLaw G p hInj) S s (influence G p w) he0 he1 hE Q hQ
    (allpin_graph G hInj hsq S s hce he0 he1 hE Q hQ) S' s' hext hS' X Y hX hY hXY hΛ0 hΛ

/-- **Single label against the others** (`prop:middle-negative` (b) for the empty pinning),
with only the count errors for `F = U` and `SquareShiftBound p` as inputs:
`ρ(y_v; y_{U \ {v}}) ≤ min{1, Λ + e²/(1-e)}` for `Λ ≥ ‖𝓔_{v, U \ {v}}‖`. -/
theorem single_label_maxCorr_le_of_countErrors (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) (hsq : SquareShiftBound p) {w wconn : ℝ}
    (hce : CountErrors G p Finset.univ w wconn) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound Finset.univ Finset.univ (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ (Finset.univ : Finset U), ∀ j ∈ (Finset.univ : Finset U),
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ Finset.univ, influence G p w i l * Q l j)
    (v : U) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : OpBound {v} (Finset.univ.erase v) (influence G p w) Λ) :
    maxCorr (graphLaw G p hInj) (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤
      min 1 (Λ + e ^ 2 / (1 - e)) := by
  have hfree : free (∅ : Finset U) = Finset.univ := by simp [free]
  have hce' : CountErrors G p (free (∅ : Finset U)) w wconn := by rw [hfree]; exact hce
  have hE' : OpBound (free (∅ : Finset U)) (free (∅ : Finset U)) (influence G p w) e := by
    rw [hfree]; exact hE
  have hQ' : ∀ i ∈ free (∅ : Finset U), ∀ j ∈ free (∅ : Finset U),
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free ∅, influence G p w i l * Q l j := by
    rw [hfree]; exact hQ
  have ha := allpin_graph G hInj hsq ∅ (fun _ => 0) hce' he0 he1 hE' Q hQ'
  exact single_label_maxCorr_le (graphLaw G p hInj) (influence G p w) he0 he1 hE Q hQ
    (fun S'' s'' h i hi j hj hij =>
      ha S'' s'' ⟨Finset.empty_subset _, fun w hw => absurd hw (Finset.notMem_empty w)⟩ h i hi
        j hj hij) v hΛ0 hΛ

/-- `allpin_graph` for odd `p`, with no square-shift hypothesis. -/
theorem allpin_graph_odd [Fact p.Prime] (hp2 : p ≠ 2) (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) (S : Finset U) (s : U → ZMod p) {w wconn : ℝ}
    (hce : CountErrors G p (free S) w wconn) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, influence G p w i l * Q l j) :
    ∀ (S'' : Finset U) (s'' : U → ZMod p), Extends S'' s'' S s →
      ∀ h : 0 < prob (graphLaw G p hInj) (pinEvent S'' s''), ∀ i ∈ free S'', ∀ j ∈ free S'',
        i ≠ j → maxCorr (condLaw (graphLaw G p hInj) (pinEvent S'' s'') h) (fun ω => ω i)
          (fun ω => ω j) ≤ Q i j :=
  allpin_graph G hInj (squareShiftBound hp2) S s hce he0 he1 hE Q hQ

/-- `middle_negative_b` for odd `p`, with no square-shift hypothesis. -/
theorem middle_negative_b_odd [Fact p.Prime] (hp2 : p ≠ 2) (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) (S : Finset U) (s : U → ZMod p) {w wconn : ℝ}
    (hce : CountErrors G p (free S) w wconn) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, influence G p w i l * Q l j)
    (S' : Finset U) (s' : U → ZMod p) (hext : Extends S' s' S s)
    (hS' : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) (X Y : Finset U) (hX : X ⊆ free S')
    (hY : Y ⊆ free S') (hXY : Disjoint X Y) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : OpBound X Y (influence G p w) Λ) :
    maxCorr (condLaw (graphLaw G p hInj) (pinEvent S' s') hS') (fun ω (v : X) => ω v)
      (fun ω (v : Y) => ω v) ≤ min 1 (Λ + e ^ 2 / (1 - e)) :=
  middle_negative_b G hInj (squareShiftBound hp2) S s hce he0 he1 hE Q hQ S' s' hext hS' X Y
    hX hY hXY hΛ0 hΛ

/-- `single_label_maxCorr_le_of_countErrors` for odd `p`, with no square-shift hypothesis. -/
theorem single_label_maxCorr_le_odd [Fact p.Prime] (hp2 : p ≠ 2) (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) {w wconn : ℝ}
    (hce : CountErrors G p Finset.univ w wconn) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound Finset.univ Finset.univ (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ (Finset.univ : Finset U), ∀ j ∈ (Finset.univ : Finset U),
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ Finset.univ, influence G p w i l * Q l j)
    (v : U) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : OpBound {v} (Finset.univ.erase v) (influence G p w) Λ) :
    maxCorr (graphLaw G p hInj) (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤
      min 1 (Λ + e ^ 2 / (1 - e)) :=
  single_label_maxCorr_le_of_countErrors G hInj (squareShiftBound hp2) hce he0 he1 hE Q hQ v
    hΛ0 hΛ

end Sarkozy.InfluenceGlue
