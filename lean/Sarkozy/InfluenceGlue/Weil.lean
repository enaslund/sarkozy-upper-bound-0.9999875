module

public import Sarkozy.InfluenceGlue.PinnedInfluence
public import Sarkozy.Influence.Weil

/-!
# The pinned-influence chain from Weil's bound

The results of `Sarkozy.InfluenceGlue.PinnedInfluence` for an odd prime `p`, with the count
errors derived from Weil's bound `Labellings.WeilBound (ZMod p)` by WP-P's
`Sarkozy.Influence.countErrors_of_weil`. The remaining inputs are:
* Weil's bound;
* numbers `0 ≤ w, w^{conn} < 1` dominating the graded errors (`eq:graphs:graded`);
* the operator-norm data `‖𝓔_{FF}‖ ≤ e < 1`, and `Q = (I - 𝓔)^{-1}` on `F`, which
  `Sarkozy.Influence.exists_inverse` provides.
-/

@[expose] public section

namespace Sarkozy.InfluenceGlue

open Sarkozy Sarkozy.Peyre Sarkozy.Angles Sarkozy.Influence

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [Fact p.Prime]

/-- **`lem:mid:allpin` for the graph law, from Weil's bound** (odd `p`): the hypothesis `ha` of
`pinned_influence_b`. -/
theorem allpin_graph_weil (hp2 : p ≠ 2) (hW : Labellings.WeilBound (ZMod p))
    (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty) (S : Finset U)
    (s : U → ZMod p) {w wconn : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (hc0 : 0 ≤ wconn)
    (hc1 : wconn < 1)
    (hw : ∀ t ≤ maxDeg G (free S), (Labellings.gradedA t * √(p : ℝ) + Labellings.gradedB t +
      2 ^ t * (Fintype.card U : ℝ)) / p ≤ w)
    (hwc : ∀ t ≤ maxDeg G (free S) + 1, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * ((2 * Fintype.card U : ℕ) : ℝ)) / p ≤ wconn)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, influence G p w i l * Q l j) :
    ∀ (S'' : Finset U) (s'' : U → ZMod p), Extends S'' s'' S s →
      ∀ h : 0 < prob (graphLaw G p hInj) (pinEvent S'' s''), ∀ i ∈ free S'', ∀ j ∈ free S'',
        i ≠ j → maxCorr (condLaw (graphLaw G p hInj) (pinEvent S'' s'') h) (fun ω => ω i)
          (fun ω => ω j) ≤ Q i j :=
  allpin_graph_odd hp2 G hInj S s
    (countErrors_of_weil G hW (free S) hw0 hw1 hc0 hc1 hw hwc) he0 he1 hE Q hQ

/-- **`prop:middle-negative` (b) from Weil's bound** (odd `p`). -/
theorem middle_negative_b_weil (hp2 : p ≠ 2) (hW : Labellings.WeilBound (ZMod p))
    (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty) (S : Finset U)
    (s : U → ZMod p) {w wconn : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (hc0 : 0 ≤ wconn)
    (hc1 : wconn < 1)
    (hw : ∀ t ≤ maxDeg G (free S), (Labellings.gradedA t * √(p : ℝ) + Labellings.gradedB t +
      2 ^ t * (Fintype.card U : ℝ)) / p ≤ w)
    (hwc : ∀ t ≤ maxDeg G (free S) + 1, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * ((2 * Fintype.card U : ℕ) : ℝ)) / p ≤ wconn)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound (free S) (free S) (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ free S, ∀ j ∈ free S,
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ free S, influence G p w i l * Q l j)
    (S' : Finset U) (s' : U → ZMod p) (hext : Extends S' s' S s)
    (hS' : 0 < prob (graphLaw G p hInj) (pinEvent S' s')) (X Y : Finset U) (hX : X ⊆ free S')
    (hY : Y ⊆ free S') (hXY : Disjoint X Y) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : OpBound X Y (influence G p w) Λ) :
    maxCorr (condLaw (graphLaw G p hInj) (pinEvent S' s') hS') (fun ω (v : X) => ω v)
      (fun ω (v : Y) => ω v) ≤ min 1 (Λ + e ^ 2 / (1 - e)) :=
  middle_negative_b_odd hp2 G hInj S s
    (countErrors_of_weil G hW (free S) hw0 hw1 hc0 hc1 hw hwc) he0 he1 hE Q hQ S' s' hext hS'
    X Y hX hY hXY hΛ0 hΛ

/-- **Single label against the others, from Weil's bound** (odd `p`, empty pinning):
`ρ(y_v; y_{U \ {v}}) ≤ min{1, Λ + e²/(1-e)}`. -/
theorem single_label_maxCorr_le_of_weil (hp2 : p ≠ 2) (hW : Labellings.WeilBound (ZMod p))
    (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty) {w wconn : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) (hc0 : 0 ≤ wconn) (hc1 : wconn < 1)
    (hw : ∀ t ≤ maxDeg G Finset.univ, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * (Fintype.card U : ℝ)) / p ≤ w)
    (hwc : ∀ t ≤ maxDeg G Finset.univ + 1, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * ((2 * Fintype.card U : ℕ) : ℝ)) / p ≤ wconn)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1)
    (hE : OpBound Finset.univ Finset.univ (influence G p w) e) (Q : U → U → ℝ)
    (hQ : ∀ i ∈ (Finset.univ : Finset U), ∀ j ∈ (Finset.univ : Finset U),
      Q i j = (if i = j then 1 else 0) + ∑ l ∈ Finset.univ, influence G p w i l * Q l j)
    (v : U) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : OpBound {v} (Finset.univ.erase v) (influence G p w) Λ) :
    maxCorr (graphLaw G p hInj) (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤
      min 1 (Λ + e ^ 2 / (1 - e)) :=
  single_label_maxCorr_le_odd hp2 G hInj
    (countErrors_of_weil G hW Finset.univ hw0 hw1 hc0 hc1 hw hwc) he0 he1 hE Q hQ v hΛ0 hΛ

end Sarkozy.InfluenceGlue
