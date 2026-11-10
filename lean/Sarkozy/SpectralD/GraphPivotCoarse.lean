module

public import Sarkozy.SpectralD.GraphStars
public import Sarkozy.TraceMixing.Slot

@[expose] public section

/-!
# The pivot density of a graph law in the paper's coarse form

`paper/sections/14_spectral.tex`, the remark after `lem:general-star`: for the uniform law on the
injective strict-square labellings of a graph on `n` vertices, `lem:graphs:vertex`(dens) and
`lem:extension`(coarse) give the pivot density `D_j = 2^t/(1 − e_t(p, n))`, `t` the degree of
`j`, whenever `e_t(p, n) < 1`.

`graphWeight_condLaw_le` (`GraphLawBridge`) gives the graded form
`condLaw ≤ 2^t/(p − 𝔈_t − 2^t(n − 1)) = 2^t/(p(1 − e⁻_t(n − 1)))`. With `e⁻_t(z) ≤ e_t(p, z)`
(`it:et:compare`, `TraceMixing.lowerErr_le_coarseErr`) and the monotonicity of `e_t(p, ·)`, this
is at most `D_j/p` with the paper's `D_j` (`graphWeight_condLaw_le_coarse`), and the pivot bound
of `lem:general-star`(c) for the graph law takes the paper's form
(`graph_star_pivot_bound_coarse`).

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators symmDiff

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

/-- `p − 𝔈_t − 2^t(n − 1) ≥ p(1 − e_t(p, n))` (`it:et:compare` and monotonicity in `n`). -/
lemma graded_den_ge_coarse (t n : ℕ) (hn : 1 ≤ n) :
    (p : ℝ) * (1 - TraceMixing.coarseErr p t n) ≤
      (p : ℝ) - Labellings.softError p t - 2 ^ t * ((n : ℝ) - 1) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 := TraceMixing.lowerErr_le_coarseErr hp1 t (n - 1)
  have h2 : TraceMixing.coarseErr p t (n - 1) ≤ TraceMixing.coarseErr p t n := by
    unfold TraceMixing.coarseErr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add (le_refl _)
    apply div_le_div_of_nonneg_right _ hp0.le
    exact_mod_cast Nat.sub_le n 1
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  have h3 : TraceMixing.lowerErr p t (n - 1) =
      (Labellings.softError p t + 2 ^ t * ((n : ℝ) - 1)) / p := by
    unfold TraceMixing.lowerErr
    rw [hcast]
  have h4 : Labellings.softError p t + 2 ^ t * ((n : ℝ) - 1) ≤
      (p : ℝ) * TraceMixing.coarseErr p t n := by
    have := h1.trans h2
    rw [h3, div_le_iff₀ hp0] at this
    linarith
  linarith

/-- **The pivot density of a graph law, coarse form** (`lem:graphs:vertex`(dens),
`lem:extension`(coarse), `thm:weil`): if `e_t(p, n) < 1` for the degree `t` of `j` and
`n = |W|`, then under `λ_p(G)` every value of `x_j` given the other labels has conditional
probability at most `D_j/p` with `D_j = 2^t/(1 − e_t(p, n))`. -/
theorem graphWeight_condLaw_le_coarse (hW : Labellings.WeilBound (ZMod p))
    (G : Labellings.OrientedGraph W) (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    (j : W)
    (he : TraceMixing.coarseErr p (Labellings.nbrCount G (univ.erase j) j)
      (Fintype.card W) < 1)
    (x : W → ZMod p) (t : ZMod p) (hx : graphWeight G hne x ≠ 0) :
    condLaw (graphWeight G hne) j x t ≤
      2 ^ Labellings.nbrCount G (univ.erase j) j /
        (1 - TraceMixing.coarseErr p (Labellings.nbrCount G (univ.erase j) j)
          (Fintype.card W)) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn : 1 ≤ Fintype.card W := Fintype.card_pos_iff.mpr ⟨j⟩
  set m := Labellings.nbrCount G (univ.erase j) j with hm
  set e := TraceMixing.coarseErr p m (Fintype.card W) with he'
  have hlow := graded_den_ge_coarse (p := p) m (Fintype.card W) hn
  have hpos : 0 < (p : ℝ) * (1 - e) := mul_pos hp0 (by linarith)
  have hden : 0 < (p : ℝ) - Labellings.softError p m - 2 ^ m * ((Fintype.card W : ℝ) - 1) :=
    lt_of_lt_of_le hpos hlow
  have h := graphWeight_condLaw_le hW G hne j hden x t hx
  refine h.trans ?_
  rw [div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by rw [mul_comm]; exact hpos) _
  rw [mul_comm]
  exact hlow

/-- **`lem:general-star`(c) for the graph law with the paper's pivot density**
(`p ≡ 3 (mod 4)`, Weil): for nonempty supports `S ≠ T` and a pivot `j ∈ S△T` of degree `t`
with `e_t(p, n) < 1`,
`‖W_S^*W_T h‖² ≤ (q/(1 − q))²([a_d + (c + (k − 1)(l − 1))q]² + q(D_j − 1))‖h‖²`,
`D_j = 2^t/(1 − e_t(p, n))`. -/
theorem graph_star_pivot_bound_coarse (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    {S T : Finset W} (hS : S.Nonempty) (hT : T.Nonempty) (hST : S ≠ T) {j : W}
    (hj : j ∈ S ∆ T)
    (he : TraceMixing.coarseErr p (Labellings.nbrCount G (univ.erase j) j)
      (Fintype.card W) < 1)
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp (graphWeight G hne) (starKer S) (starKer T) h) ≤
      ((p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)) ^ 2 * ((aConst p (S ∆ T).card +
        (((S ∩ T).card : ℝ) + ((S.card : ℝ) - 1) * ((T.card : ℝ) - 1)) * (p : ℝ)⁻¹) ^ 2 +
          (p : ℝ)⁻¹ * (2 ^ Labellings.nbrCount G (univ.erase j) j /
            (1 - TraceMixing.coarseErr p (Labellings.nbrCount G (univ.erase j) j)
              (Fintype.card W)) - 1)) * l2sq h := by
  obtain ⟨h0, h1, hinv, hinj⟩ := graphWeight_hyps G hne
  exact star_pivot_bound hp2 hp3 hW (graphWeight G hne) h0 h1 hinv hinj hS hT hST hj
    (fun x t hx => graphWeight_condLaw_le_coarse hW G hne j he x t hx) h hh

end Sarkozy.SpectralD
