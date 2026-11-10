module

public import Sarkozy.InfluenceGlue.Weil

/-!
# Single-label correlation from row sums of the influence matrix

This is the form consumed by the tail-graph assembly: one label against all the others.
Suppose every row sum of the influence matrix `𝓔 = (ε_ij)` (`eq:mid:epsij`) is at most
`q < 1`, so `‖𝓔‖ ≤ q` by the Schur test. Then `ρ(y_v; y_{U \ {v}}) ≤ q / (1 - q)` for the
graph law `λ_p(G)`. This is `prop:middle-negative` (b) for the empty pinning, with
`Λ = e = q`; the inverse `Q = (I - 𝓔)^{-1}` is produced internally
(`Sarkozy.Influence.exists_inverse`).

* `single_label_maxCorr_le_rowSum`: from count errors and `SquareShiftBound p`.
* `single_label_maxCorr_le_rowSum_weil`: from Weil's bound, for odd `p`.
-/

@[expose] public section

namespace Sarkozy.InfluenceGlue

open Sarkozy Sarkozy.Peyre Sarkozy.Angles Sarkozy.Influence

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ}

/-- **Single label against the others, from row sums**: with count errors for `F = U` and
`SquareShiftBound p`, if `∑_j ε_ij ≤ q < 1` for every `i`, then
`ρ(y_v; y_{U \ {v}}) ≤ q / (1 - q)`. -/
theorem single_label_maxCorr_le_rowSum [NeZero p] (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) (hsq : SquareShiftBound p) {w wconn : ℝ}
    (hce : CountErrors G p Finset.univ w wconn) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrow : ∀ i, ∑ j, influence G p w i j ≤ q) (v : U) :
    maxCorr (graphLaw G p hInj) (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤
      q / (1 - q) := by
  have hw : -1 ≤ w := by linarith [hce.w_nonneg]
  have hE : OpBound Finset.univ Finset.univ (influence G p w) q :=
    influence_opBound G p hw Finset.univ hq0 (fun i _ => hrow i)
  obtain ⟨Q, hQ⟩ := exists_inverse Finset.univ (influence G p w) hq0 hq1 hE
  have hΛ : OpBound {v} (Finset.univ.erase v) (influence G p w) q :=
    hE.subset (Finset.subset_univ _) (Finset.subset_univ _)
  have h := single_label_maxCorr_le_of_countErrors G hInj hsq hce hq0 hq1 hE Q hQ v hq0 hΛ
  have h1q : 0 < 1 - q := by linarith
  have e : q + q ^ 2 / (1 - q) = q / (1 - q) := by
    field_simp
    ring
  rw [e] at h
  exact h.trans (min_le_right _ _)

/-- **Single label against the others, from Weil's bound** (odd `p`): with `0 ≤ w, w^{conn} < 1`
dominating the graded errors (`eq:graphs:graded`) for `F = U`, and row sums
`∑_j ε_ij ≤ q < 1`, `ρ(y_v; y_{U \ {v}}) ≤ q / (1 - q)`. -/
theorem single_label_maxCorr_le_rowSum_weil [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : Labellings.WeilBound (ZMod p)) (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) {w wconn : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hc0 : 0 ≤ wconn) (hc1 : wconn < 1)
    (hw : ∀ t ≤ maxDeg G Finset.univ, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * (Fintype.card U : ℝ)) / p ≤ w)
    (hwc : ∀ t ≤ maxDeg G Finset.univ + 1, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * ((2 * Fintype.card U : ℕ) : ℝ)) / p ≤ wconn)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hrow : ∀ i, ∑ j, influence G p w i j ≤ q) (v : U) :
    maxCorr (graphLaw G p hInj) (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤
      q / (1 - q) :=
  single_label_maxCorr_le_rowSum G hInj (squareShiftBound hp2)
    (countErrors_of_weil G hW Finset.univ hw0 hw1 hc0 hc1 hw hwc) hq0 hq1 hrow v

end Sarkozy.InfluenceGlue
