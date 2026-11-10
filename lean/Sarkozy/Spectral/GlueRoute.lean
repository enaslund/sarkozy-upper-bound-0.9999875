module

public import Sarkozy.Spectral.GlueCut
public import Sarkozy.Spectral.GlueStars
public import Sarkozy.Comparison.Recentering

/-!
# Glue, V: the cut realization with the star inputs, and the form bounds for the tensor step

* `glue_star_inputs_cut`: for the cut of spectral data `D` at `F = 𝔽_p`, the star inputs of
  `glue_star_inputs` hold in the realization of `GlueCut`, that is, with `one = cutOne D hne`
  (the constants of `L²(μ)`, `μ = λ(G⁺)` = WP-P's `halfLaw`) and `hs = l2Map μ h_⋆`. The pinned
  half law is `SecondOrder.graphPinned` of the half graph `G⁺`; its law is WP-P's `halfLaw`
  (definitionally). So `cutOp D hne` (symmetric, `⟪1, Op 1⟫ = 1`) and the star inputs `M_⋆`,
  `z_⋆` live in the same space, as `routeB_cde` and `stars_c_inputs` need.
* `routeAInputs_cut`: `RouteAInputs` for `cutOp`, with `symm`, `norm_one`, `rho_mean`
  discharged; the remaining fields are hypotheses.
* `glue_mucentre_star`: with `lem:spec:stars` (c) as the remaining hypothesis, the star
  hypotheses `hstar1` of `mucentre_inputs` and `hstar`, `hZs` of `mucentre_Z`.
* `cutForm_bounds_of_op`: numerical-range bounds of `cutOp` on `EuclideanSpace` give the bounds
  `-c ‖f‖²_μ ≤ cutForm f f ≤ C ‖f‖²_μ` on functions, in the norm `Recentering.nrm` of WP-P's
  `tensorcomp_block` (`lem:spec:tensorcomp` (b), kernel form). That theorem also assumes that
  every `μ_i` has full support, which the half law `λ(G⁺)` does not; see the report.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.InfluenceGlue Sarkozy.Cuts

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- The pinned half law of `λ_p(G⁺)` is WP-P's half law of the cut. -/
theorem pinnedLaw_graphPinned_halfGraph {p : ℕ} [Fact p.Prime]
    (hW : Labellings.WeilBound (ZMod p))
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1) :
    pinnedLaw (SecondOrder.graphPinned hW D.halfGraph (D.half_nonempty hne) he) =
      D.halfLaw hne := rfl

/-- **The star inputs in the cut realization**: `‖h_⋆ - ⟪1, h_⋆⟫ 1‖ ≤ M_⋆`, `|⟪1, h_⋆⟫| ≤ z_⋆`
and `2|⟪1, h_⋆⟫| ≤ 2 z_⋆`, with `1 = cutOne D hne` and `h_⋆ = l2Map (halfLaw) h_⋆`. -/
theorem glue_star_inputs_cut {p : ℕ} [Fact p.Prime] {K : Type*} [Fintype K]
    [LinearOrder D.cut.Half] (hW : Target.Weil) (hMR : Target.MovingRoot) (hp2 : p ≠ 2)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (N : K → Finset D.cut.Half) (c : K → Finset D.cut.Half → ℝ) :
    let L := SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2) D.halfGraph
      (D.half_nonempty hne) he
    ‖l2Map (D.halfLaw hne) (starFunction N c) -
        ⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction N c)⟫_ℝ • cutOne D hne‖ ≤
      starMstar L N c ∧
    ‖⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction N c)⟫_ℝ‖ ≤ starZstar L N c ∧
    2 * ‖⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction N c)⟫_ℝ‖ ≤ 2 * starZstar L N c := by
  intro L
  obtain ⟨-, -, h3, h4, h5⟩ := glue_star_inputs hW hMR hp2 L N c
  exact ⟨h3, h4, h5⟩

/-- **The star hypotheses of `prop:spec2:mucentre`** in the cut realization: if the stars map
`1` to `h_⋆ + E_μ h_⋆` (`lem:spec:stars` (c), the hypothesis `hT1`), then
`‖T_star 1 - ⟪1, T_star 1⟫ 1‖ ≤ M_⋆` (the hypothesis `hstar1` of `mucentre_inputs`),
`⟪1, T_star 1⟫ = 2 hm` with `hm = ⟪1, h_⋆⟫` (the hypothesis `hstar` of `mucentre_Z`) and
`2|hm| ≤ 2 z_⋆` (its `hZs`), with `M_⋆`, `z_⋆` from `lem:star-mean`. -/
theorem glue_mucentre_star {p : ℕ} [Fact p.Prime] {K : Type*} [Fintype K]
    [LinearOrder D.cut.Half] (hW : Target.Weil) (hMR : Target.MovingRoot) (hp2 : p ≠ 2)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (N : K → Finset D.cut.Half) (c : K → Finset D.cut.Half → ℝ)
    (Tstar : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ] EuclideanSpace ℝ (D.cut.Half → ZMod p))
    (hT1 : Tstar (cutOne D hne) = l2Map (D.halfLaw hne) (starFunction N c) +
      ⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction N c)⟫_ℝ • cutOne D hne) :
    let L := SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2) D.halfGraph
      (D.half_nonempty hne) he
    ‖Tstar (cutOne D hne) - ⟪cutOne D hne, Tstar (cutOne D hne)⟫_ℝ • cutOne D hne‖ ≤
      starMstar L N c ∧
    ⟪cutOne D hne, Tstar (cutOne D hne)⟫_ℝ =
      2 * ⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction N c)⟫_ℝ ∧
    2 * |⟪cutOne D hne, l2Map (D.halfLaw hne) (starFunction N c)⟫_ℝ| ≤ 2 * starZstar L N c := by
  intro L
  obtain ⟨h1, h2, h3⟩ := glue_star_inputs_cut D hW hMR hp2 hne he N c
  obtain ⟨e1, e2⟩ := stars_c_inputs (𝕜 := ℝ) Tstar (cutOne D hne)
    (l2Map (D.halfLaw hne) (starFunction N c)) (norm_cutOne D hne) hT1 h1
  refine ⟨e2, e1, ?_⟩
  rw [← Real.norm_eq_abs]
  exact h3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **From operator bounds to form bounds**: if `-c ‖v‖² ≤ ⟪v, Op v⟫ ≤ C ‖v‖²` on
`EuclideanSpace`, then `-c ‖f‖²_μ ≤ cutForm f f ≤ C ‖f‖²_μ` for every function `f`, with
`‖f‖_μ = Recentering.nrm μ f`, the hypotheses of WP-P's `tensorcomp_block` at one prime. -/
theorem cutForm_bounds_of_op (hne : (Labellings.injLabellings F D.G).Nonempty) {c C : ℝ}
    (hlow : ∀ v, -c * ‖v‖ ^ 2 ≤ ⟪v, cutOp D hne v⟫_ℝ)
    (hup : ∀ v, ⟪v, cutOp D hne v⟫_ℝ ≤ C * ‖v‖ ^ 2) (f : (D.cut.Half → F) → ℝ) :
    -c * Recentering.nrm (D.halfLaw hne) f ^ 2 ≤ D.cutForm hne f f ∧
      D.cutForm hne f f ≤ C * Recentering.nrm (D.halfLaw hne) f ^ 2 := by
  have hn : Recentering.nrm (D.halfLaw hne) f ^ 2 = ‖l2Map (D.halfLaw hne) f‖ ^ 2 := by
    rw [norm_l2Map_sq, Recentering.nrm, Real.sq_sqrt]
    · exact (D.halfLaw hne).expect_congr fun x => (sq (f x)).symm
    · exact (D.halfLaw hne).expect_nonneg fun x => mul_self_nonneg (f x)
  rw [hn, ← (cutOp_form D hne f f).1]
  exact ⟨hlow _, hup _⟩

/-- **`RouteAInputs` for the cut operator**: the fields `symm`, `norm_one` and `rho_mean` are
discharged by WP-P's `lem:spec:cutkernel` (b) (`cutOp_isSymmetric`, `norm_cutOne`,
`cutOp_mean`); the other fields remain hypotheses. -/
theorem routeAInputs_cut (hne : (Labellings.injLabellings F D.G).Nonempty)
    {V Sp Sm : Submodule ℝ (EuclideanSpace ℝ (D.cut.Half → F))} {Ξ n : Type*} [Fintype Ξ]
    [Fintype n] {sgn : Ξ → Prop} [DecidablePred sgn]
    {coef : EuclideanSpace ℝ (D.cut.Half → F) → Ξ → n → ℝ} {qA qX : Ξ → (n → ℝ) → ℝ}
    {r ηQ ηB εV ερ aperp : ℝ}
    (hV1 : ∀ v ∈ V, ⟪cutOne D hne, v⟫_ℝ = 0) (hSS : Sp ⟂ Sm)
    (hρV : ∀ v ∈ V, ⟪cutOne D hne, cutOp D hne v⟫_ℝ = 0)
    (hρ : ‖cutOp D hne (cutOne D hne) - cutOne D hne‖ ≤ ερ)
    (hperp : ∀ h, ⟪cutOne D hne, h⟫_ℝ = 0 → (∀ v ∈ V, ⟪v, h⟫_ℝ = 0) →
      |⟪h, cutOp D hne h⟫_ℝ| ≤ aperp * ‖h‖ ^ 2)
    (hlow : ∀ v ∈ V, r * ∑ ξ, (qA ξ (coef v ξ) - ηQ * sqn (coef v ξ)) ≤
      ⟪v, cutOp D hne v⟫_ℝ)
    (hup : ∀ v ∈ V, ⟪v, cutOp D hne v⟫_ℝ ≤ r * ∑ ξ, (qA ξ (coef v ξ) + ηQ * sqn (coef v ξ)))
    (hnorm : ∀ v ∈ V, (1 - εV) * ∑ ξ, sqn (coef v ξ) ≤ ‖v‖ ^ 2)
    (hcoup : ∀ v ∈ V, ∃ vp ∈ V, ∃ vm ∈ V, v = vp + vm ∧
      cutOp D hne vp - V.starProjection (cutOp D hne vp) ∈ Sp ∧
      cutOp D hne vm - V.starProjection (cutOp D hne vm) ∈ Sm ∧
      ‖cutOp D hne vp - V.starProjection (cutOp D hne vp)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ)) ∧
      ‖cutOp D hne vm - V.starProjection (cutOp D hne vm)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with ¬ sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ))) :
    RouteAInputs (cutOp D hne) (cutOne D hne) V Sp Sm sgn coef qA qX r ηQ ηB εV ερ aperp :=
  ⟨cutOp_isSymmetric D hne, norm_cutOne D hne, hV1, hSS, cutOp_mean D hne, hρV, hρ, hperp, hlow,
    hup, hnorm, hcoup⟩

end Sarkozy.Spectral
