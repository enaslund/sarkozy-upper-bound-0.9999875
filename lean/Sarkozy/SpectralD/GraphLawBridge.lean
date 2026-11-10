module

public import Sarkozy.SpectralC.All
public import Sarkozy.Cuts.CutInvariance

@[expose] public section

/-!
# The graph law satisfies the hypotheses of the actual-star lemmas (sanity and bridge)

`paper/sections/14_spectral.tex`, `subsec:spec:actual-stars`, the setting: a law `μ` on the
injective tuples, invariant under the diagonal action of `Aff_p`, "for instance the uniform law
on the injective strict-square labellings of an oriented graph (`def:graphs:labeling`)".

WP-K's and S1's statements take such a law as a weight function `μ : (U → ZMod p) → ℝ` with the
hypotheses `hμ0` (nonnegative), `hμ1` (total mass one), `hinv` (invariance under
`affLab s c`, `s` a nonzero square) and `hinj` (injective on the support). This file shows that
the weights of the graph law `λ_p(G)` (`Labellings.graphLaw`, the uniform law on `Inj_p(G)`)
satisfy all four (`graphWeight_nonneg`, `graphWeight_total`, `graphWeight_inv`,
`graphWeight_inj`). It is the non-vacuity check of these hypothesis bundles (guide rule 9) and
the bridge from WP-P's half law `μ = λ_p(G⁺)` to the lemmas of `Sarkozy.SpectralC` and
`Sarkozy.SpectralD`. Invariance is WP-P's `Cuts.affine_mem_inj` (`lem:spec:cutkernel`(d)).

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W]

/-- The weights of the graph law `λ_p(G)`: `1/|Inj_p(G)|` on `Inj_p(G)`, `0` elsewhere. -/
noncomputable def graphWeight (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) : (W → ZMod p) → ℝ :=
  (Labellings.graphLaw G hne).weight

theorem graphWeight_nonneg (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) (x : W → ZMod p) :
    0 ≤ graphWeight G hne x :=
  (Labellings.graphLaw G hne).nonneg x

theorem graphWeight_total (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) :
    ∑ x, graphWeight G hne x = 1 :=
  (Labellings.graphLaw G hne).total

/-- **Invariance** (`lem:spec:cutkernel`(d)): `λ_p(G)` is invariant under `affLab s c` for
nonzero squares `s`. -/
theorem graphWeight_inv (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) (s c : ZMod p) (x : W → ZMod p)
    (hs : s ≠ 0) (hsq : IsSquare s) :
    graphWeight G hne (affLab s c x) = graphWeight G hne x := by
  have hq : quadraticChar (ZMod p) s = 1 := (quadraticChar_one_iff_isSquare hs).mpr hsq
  have hmem := Cuts.affine_mem_inj G hq c x
  have he : affLab s c x = Cuts.affineMap s c x := rfl
  unfold graphWeight Labellings.graphLaw
  simp only [he, hmem]

/-- **Injectivity on the support**: `λ_p(G)` charges only injective labellings. -/
theorem graphWeight_inj (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) (x : W → ZMod p) (k l : W)
    (hx : graphWeight G hne x ≠ 0) (hkl : k ≠ l) : x k ≠ x l := by
  have hmem : x ∈ Labellings.injLabellings (ZMod p) G := by
    by_contra h
    apply hx
    unfold graphWeight Labellings.graphLaw
    simp only [h, ↓reduceIte]
  rw [Cuts.SpecData.mem_inj] at hmem
  exact fun hxe => hkl (hmem.1 k (mem_univ k) l (mem_univ l) hxe)

/-- **All four hypotheses at once**, in the form taken by `SpectralC.star_diagonal`,
`star_pivot_bound`, `vert_star_out_bound`, `features_synthesis` and the other lemmas of the
actual-star subsection. -/
theorem graphWeight_hyps (G : Labellings.OrientedGraph W)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) :
    (∀ x, 0 ≤ graphWeight G hne x) ∧ (∑ x, graphWeight G hne x = 1) ∧
      (∀ (s c : ZMod p) (x : W → ZMod p), s ≠ 0 → IsSquare s →
        graphWeight G hne (affLab s c x) = graphWeight G hne x) ∧
      (∀ (x : W → ZMod p) (k l : W), graphWeight G hne x ≠ 0 → k ≠ l → x k ≠ x l) :=
  ⟨graphWeight_nonneg G hne, graphWeight_total G hne,
    fun s c x hs hsq => graphWeight_inv G hne s c x hs hsq,
    fun x k l hx hkl => graphWeight_inj G hne x k l hx hkl⟩

/-! ## The pivot density of a graph law (`lem:graphs:vertex`(dens) with `lem:extension`) -/

omit [Fintype W] [DecidableEq W] in
lemma feasible_mono {G : Labellings.OrientedGraph W} {A B : Finset W} (hAB : A ⊆ B)
    {x : W → ZMod p} (hx : Labellings.Feasible (ZMod p) G B x) :
    Labellings.Feasible (ZMod p) G A x :=
  ⟨fun a ha b hb h => hx.1 a (hAB ha) b (hAB hb) h,
    fun e he h1 h2 => hx.2 e he (hAB h1) (hAB h2)⟩

/-- **The pivot density of a graph law** (`lem:graphs:vertex`(dens) and the lower count of
`lem:extension`, from `thm:weil`): under `λ_p(G)`, given the other labels, every value of `x_j`
has conditional probability at most `2^t/(p − 𝔈_t − 2^t(n − 1))`, where `t` is the degree of
`j`, `n = |W|` and `𝔈_t = a_t√p + b_t` (`Labellings.softError`), provided the denominator is
positive. In the paper's notation this is `D_j/p` with `D_j = 2^t/(1 − e⁻_t(n − 1))
≤ 2^t/(1 − e_t(p, n))`: the hypothesis `hD` of `star_pivot_bound` (and of
`SpectralC.hidden_feature_star`) for the graph law. -/
theorem graphWeight_condLaw_le (hW : Labellings.WeilBound (ZMod p))
    (G : Labellings.OrientedGraph W) (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    (j : W)
    (hden : 0 < (p : ℝ) - Labellings.softError p (Labellings.nbrCount G (univ.erase j) j) -
      2 ^ Labellings.nbrCount G (univ.erase j) j * ((Fintype.card W : ℝ) - 1))
    (x : W → ZMod p) (t : ZMod p) (hx : graphWeight G hne x ≠ 0) :
    condLaw (graphWeight G hne) j x t ≤
      2 ^ Labellings.nbrCount G (univ.erase j) j /
        ((p : ℝ) - Labellings.softError p (Labellings.nbrCount G (univ.erase j) j) -
          2 ^ Labellings.nbrCount G (univ.erase j) j * ((Fintype.card W : ℝ) - 1)) := by
  classical
  set Inj := Labellings.injLabellings (ZMod p) G with hInj
  set m := Labellings.nbrCount G (univ.erase j) j with hm
  set Adm := Labellings.vertexAdmissible G (univ.erase j) x j with hAdm
  set den := (p : ℝ) - Labellings.softError p m - 2 ^ m * ((Fintype.card W : ℝ) - 1) with hdenv
  have hI : (0 : ℝ) < Inj.card := by exact_mod_cast card_pos.mpr hne
  -- the support
  have hxI : x ∈ Inj := by
    by_contra h
    apply hx
    unfold graphWeight Labellings.graphLaw
    simp only [hInj] at h
    simp only [h, ↓reduceIte]
  have hfe : Labellings.Feasible (ZMod p) G (univ.erase j) x :=
    feasible_mono (subset_univ _) ((Cuts.SpecData.mem_inj G x).mp hxI)
  -- the count of admissible values
  have hcount := (Labellings.card_vertexAdmissible hW G hfe j).2
  rw [ZMod.card, card_erase_of_mem (mem_univ j), card_univ] at hcount
  have hcast : ((Fintype.card W - 1 : ℕ) : ℝ) = (Fintype.card W : ℝ) - 1 := by
    have : 1 ≤ Fintype.card W := Fintype.card_pos_iff.mpr ⟨j⟩
    rw [Nat.cast_sub this, Nat.cast_one]
  rw [hcast] at hcount
  have hAdm_pos : (0 : ℝ) < Adm.card := by
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have : (0 : ℝ) < 2 ^ m * Adm.card := lt_of_lt_of_le hden hcount
    exact pos_of_mul_pos_right this h2.le
  -- admissible values give elements of `Inj_p(G)`
  have hsub : ∀ c ∈ Adm, Function.update x j c ∈ Inj := by
    intro c hc
    have h1 := Labellings.feasible_insert hfe (fun h => (mem_erase.mp h).1 rfl) hc
    rw [insert_erase (mem_univ j)] at h1
    exact (Cuts.SpecData.mem_inj G _).mpr h1
  -- the conditional law
  have hw : ∀ y, graphWeight G hne y = if y ∈ Inj then 1 / (Inj.card : ℝ) else 0 := by
    intro y; rfl
  have hmass : (Adm.card : ℝ) / Inj.card ≤ ∑ t', graphWeight G hne (Function.update x j t') := by
    have h1 : ∑ t' ∈ Adm, graphWeight G hne (Function.update x j t') = (Adm.card : ℝ) / Inj.card := by
      have e : ∀ c ∈ Adm, graphWeight G hne (Function.update x j c) = 1 / (Inj.card : ℝ) := by
        intro c hc; rw [hw]; simp only [hsub c hc, ↓reduceIte]
      rw [sum_congr rfl e, sum_const, nsmul_eq_mul]
      ring
    rw [← h1]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun t' _ _ => graphWeight_nonneg G hne _)
  have hnum : graphWeight G hne (Function.update x j t) ≤ 1 / (Inj.card : ℝ) := by
    rw [hw]; split_ifs
    · exact le_refl _
    · positivity
  unfold condLaw
  rw [cmass_erase]
  have hmpos : 0 < ∑ t', graphWeight G hne (Function.update x j t') :=
    lt_of_lt_of_le (div_pos hAdm_pos hI) hmass
  calc graphWeight G hne (Function.update x j t) / ∑ t', graphWeight G hne (Function.update x j t')
      ≤ (1 / (Inj.card : ℝ)) / ((Adm.card : ℝ) / Inj.card) :=
        div_le_div₀ (by positivity) hnum (div_pos hAdm_pos hI) hmass
    _ = 1 / (Adm.card : ℝ) := by field_simp
    _ ≤ 2 ^ m / den := by
        rw [div_le_div_iff₀ hAdm_pos hden, one_mul]
        linarith

end Sarkozy.SpectralD
