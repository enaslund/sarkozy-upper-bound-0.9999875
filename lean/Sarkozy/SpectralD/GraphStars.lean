module

public import Sarkozy.SpectralD.GraphLawBridge
public import Sarkozy.SpectralD.PivotCross

@[expose] public section

/-!
# `lem:general-star`(c), (d) for the graph law

`paper/sections/14_spectral.tex`, the remark after `lem:general-star`: "For the uniform law on
the injective strict-square labellings of a graph on `n` vertices, the label `x_j` is
conditionally uniform on its admissible set (`lem:graphs:vertex`(dens)), so
`lem:extension`(coarse) gives the pivot density `D_j = 2^t/(1 − e_t(p, n))`".

This file instantiates S1's bounds at `μ = λ_p(G)` (`graphWeight`), with every hypothesis
discharged except `thm:weil` (`Labellings.WeilBound`, from `Target.Weil`) and the positivity
of the count:

* `graph_star_pivot_bound`: `eq:star-cross-bound` with the pivot density of `j ∈ S△T`
  (`graphWeight_condLaw_le`, the lower count of `lem:extension`);
* `graph_vert_star_out_bound`, `graph_vert_star_mem_bound`: `eq:singleton-star`.

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators symmDiff

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

/-- **`lem:general-star`(c) for the graph law** (`p ≡ 3 (mod 4)`, Weil): for nonempty supports
`S ≠ T` and a pivot `j ∈ S△T` of degree `t` in `G` with `p − 𝔈_t − 2^t(n − 1) > 0`,
`‖W_S^*W_T h‖² ≤ (q/(1 − q))²([a_d + (c + (k − 1)(l − 1))q]² + q(D_j − 1))‖h‖²` with
`D_j = p 2^t/(p − 𝔈_t − 2^t(n − 1))`. -/
theorem graph_star_pivot_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    {S T : Finset W} (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ≠ T) {j : W}
    (hj : j ∈ S ∆ T)
    (hden : 0 < (p : ℝ) - Labellings.softError p (Labellings.nbrCount G (univ.erase j) j) -
      2 ^ Labellings.nbrCount G (univ.erase j) j * ((Fintype.card W : ℝ) - 1))
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp (graphWeight G hne) (starKer S) (starKer T) h) ≤
      ((p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)) ^ 2 * ((aConst p (S ∆ T).card +
        (((S ∩ T).card : ℝ) + ((S.card : ℝ) - 1) * ((T.card : ℝ) - 1)) * (p : ℝ)⁻¹) ^ 2 +
          (p : ℝ)⁻¹ * ((p : ℝ) * 2 ^ Labellings.nbrCount G (univ.erase j) j /
            ((p : ℝ) - Labellings.softError p (Labellings.nbrCount G (univ.erase j) j) -
              2 ^ Labellings.nbrCount G (univ.erase j) j * ((Fintype.card W : ℝ) - 1)) - 1)) *
        l2sq h := by
  obtain ⟨h0, h1, hinv, hinj⟩ := graphWeight_hyps G hne
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine star_pivot_bound hp2 hp3 hW (graphWeight G hne) h0 h1 hinv hinj hS hT hST hj
    (fun x t hx => ?_) h hh
  rw [mul_div_assoc, mul_div_cancel_left₀ _ hp0.ne']
  exact graphWeight_condLaw_le hW G hne j hden x t hx

/-- **`lem:general-star`(d), `i ∉ S`, for the graph law** (`p ≡ 3 (mod 4)`, Weil). -/
theorem graph_vert_star_out_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    {S : Finset W} (hS : S.Nonempty) {i : W} (hi : i ∉ S) (h : ZMod p → ℂ)
    (hh : meanC h = 0) :
    l2sq (gramOp (graphWeight G hne) (vertKer i) (starKer S) h) ≤
      (p : ℝ)⁻¹ * (rp p ^ 2 * (1 + ((S.card : ℝ) - 1) * rp p) ^ 2 +
        (S.card : ℝ) ^ 2 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  obtain ⟨h0, h1, hinv, hinj⟩ := graphWeight_hyps G hne
  exact vert_star_out_bound hp2 hp3 hW (graphWeight G hne) h0 h1 hinv hinj hS hi h hh

/-- **`lem:general-star`(d), `i ∈ S`, `|S| ≥ 2`, for the graph law** (`p ≡ 3 (mod 4)`, Weil). -/
theorem graph_vert_star_mem_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    {S : Finset W} (hS2 : 2 ≤ S.card) {i : W} (hi : i ∈ S) (h : ZMod p → ℂ)
    (hh : meanC h = 0) :
    l2sq (gramOp (graphWeight G hne) (vertKer i) (starKer S) h) ≤
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * (((S.card : ℝ) - 1) * rp p) ^ 2 +
        (aConst p (S.card - 1) + (p : ℝ)⁻¹) ^ 2) / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  obtain ⟨h0, h1, hinv, hinj⟩ := graphWeight_hyps G hne
  exact vert_star_mem_bound hp2 hp3 hW (graphWeight G hne) h0 h1 hinv hinj hS2 hi h hh

end Sarkozy.SpectralD
