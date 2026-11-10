module

public import Sarkozy.SpectralD.CxCouplingCut
public import Sarkozy.Spectral.GlueStarOp

@[expose] public section

/-!
# `prop:spec2:mucentre` (c3), (c4) for the cut, and the spectral criterion for the cut laws

`paper/sections/14_spectral.tex`, `prop:spec2:mucentre` and `thm:spectral-criterion`(a).

* `perp_one_coord`: `h ⊥ 1` and `h ⊥ V_ℝ` (the real degree-one space) imply `h ⊥` every function
  of one coordinate; hence WP-A's `starOp_perp` gives the star hypothesis `hstar` of
  `mucentre_inputs` relative to `V_ℝ` (`starOp_perp_V`).
* `mucentre_cut_real`: WP-A's `mucentre_inputs` for the cut in the real realization, with the
  star part discharged by WP-A's `starOp_perp` and `glue_mucentre_star_closed` (`Target.Weil`,
  `Target.MovingRoot`): `‖ϱ − 1‖ ≤ (M_⋆ + N_ns + D_col)/(1 − ε_Z)` and
  `|⟪h, Op h⟫| ≤ (N_ns + D_col)/(1 − ε_Z) ‖h‖²` on `H_⊥` relative to `V_ℝ`. The inputs that
  remain are those of the character expansion: `Op = K₀/Z₀` with
  `K₀ = 1 ⊗ 1 + T_star + T_ns − T_coll` (`lem:spec:expansion`), `‖T_ns‖ ≤ N_ns`
  (`lem:matching:extractionk`), `‖T_coll‖ ≤ D_col` (`lem:oct24-collision`) and
  `Z₀ ≥ 1 − ε_Z` (`prop:spec2:mucentre`(c1)).
* `spectral_criterion_cut`: **the spectral criterion's conclusion for the actual cut laws**,
  `⟪f, Op f⟫ ≥ −g r ‖f‖²` for every real `f` of WP-A's real cut realization of `λ_p(G⁺)`, from:
  `Target.Weil`, `Target.MovingRoot`; the error conditions; the expansion inputs above; the
  paper's numbers of `cor:spec2:coupling` and `lem:spec:degone`; and WP-A's finite tests.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **Orthogonality to `1` and to `V_ℝ` gives orthogonality to every function of one
coordinate.** -/
theorem perp_one_coord (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (h : EuclideanSpace ℝ (D.cut.Half → ZMod p)) (h1 : ⟪Spectral.cutOne D hne, h⟫_ℝ = 0)
    (hV : ∀ v ∈ realDegSpace (D.halfLaw hne), ⟪v, h⟫_ℝ = 0) (k : D.cut.Half)
    (g : ZMod p → ℝ) : ⟪InfluenceGlue.l2Map (D.halfLaw hne) (fun x => g (x k)), h⟫_ℝ = 0 := by
  set m : ℝ := (p : ℝ)⁻¹ * ∑ a, g a with hm
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set gk : D.cut.Half → ZMod p → ℝ := fun l a => if l = k then g a - m else 0 with hgk
  have hgk0 : ∀ l, ∑ a, gk l a = 0 := by
    intro l
    simp only [hgk]
    split_ifs
    · rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, hm]
      field_simp
      ring
    · simp
  have hmem : InfluenceGlue.l2Map (D.halfLaw hne) (fun x => ∑ l, gk l (x l)) ∈
      realDegSpace (D.halfLaw hne) := ⟨gk, hgk0, rfl⟩
  have hsplit : (fun x : D.cut.Half → ZMod p => g (x k)) =
      m • (fun _ : D.cut.Half → ZMod p => (1 : ℝ)) + (fun x => ∑ l, gk l (x l)) := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, hgk]
    rw [sum_ite_eq']
    simp
  rw [hsplit, map_add, map_smul, inner_add_left, inner_smul_left]
  have h1' : ⟪InfluenceGlue.l2Map (D.halfLaw hne) (fun _ => (1 : ℝ)), h⟫_ℝ = 0 := h1
  rw [h1', hV _ hmem]
  simp

/-- **The star hypothesis relative to `V_ℝ`** (`prop:spec2:mucentre`(a), WP-A's `starOp_perp`). -/
theorem starOp_perp_V (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (h h' : EuclideanSpace ℝ (D.cut.Half → ZMod p)) (h1 : ⟪Spectral.cutOne D hne, h⟫_ℝ = 0)
    (hV : ∀ v ∈ realDegSpace (D.halfLaw hne), ⟪v, h⟫_ℝ = 0)
    (h1' : ⟪Spectral.cutOne D hne, h'⟫_ℝ = 0)
    (hV' : ∀ v ∈ realDegSpace (D.halfLaw hne), ⟪v, h'⟫_ℝ = 0) :
    ⟪h', Spectral.starOp D hne h⟫_ℝ = 0 :=
  Spectral.starOp_perp D hne h h' (perp_one_coord D hne h h1 hV) (perp_one_coord D hne h' h1' hV')

/-- **`prop:spec2:mucentre` (c3), (c4) for the cut, real realization**: WP-A's
`mucentre_inputs` with `T_star = starOp`, the star part discharged (`starOp_perp_V`,
`glue_mucentre_star_closed`); the inputs of the character expansion remain hypotheses. -/
theorem mucentre_cut_real [LinearOrder D.cut.Half] (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖) :
    let L := SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2) D.halfGraph
      (D.half_nonempty hne) he
    ‖Spectral.cutOp D hne (Spectral.cutOne D hne) - Spectral.cutOne D hne‖ ≤
        (Spectral.starMstar L D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol) / (1 - εZ) ∧
      ∀ f, ⟪Spectral.cutOne D hne, f⟫_ℝ = 0 →
        (∀ v ∈ realDegSpace (D.halfLaw hne), ⟪v, f⟫_ℝ = 0) →
        |⟪f, Spectral.cutOp D hne f⟫_ℝ| ≤ (Nns + Dcol) / (1 - εZ) * ‖f‖ ^ 2 := by
  intro L
  have hstar1 := (Spectral.glue_mucentre_star_closed D hW hMR hp2 hne he).1
  have h := Spectral.mucentre_inputs (Spectral.cutOp D hne) K₀ (Spectral.starOp D hne) Tns Tcoll
    (Spectral.cutOne D hne) (Spectral.norm_cutOne D hne) (realDegSpace (D.halfLaw hne)) hεZ hZ
    (fun x => by rw [hT x]; rfl) hK (Spectral.cutOp_mean D hne)
    (fun h h' h1 hV h1' hV' => starOp_perp_V D hne h h' h1 hV h1' hV') hstar1 hns hcoll
  exact ⟨h.1, fun f h1 hV => by simpa using h.2 f h1 hV⟩

end Sarkozy.SpectralD.Cx
