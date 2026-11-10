module

public import Sarkozy.SpectralD.CxMucentre

@[expose] public section

/-!
# `thm:spectral-criterion`(a) for the actual cut laws `λ_p(G⁺)`

`paper/sections/14_spectral.tex`, `thm:spectral-criterion` (Route A), part (a): `Op ⪰ −g r I`,
for the cut operator `Op = T_{K/Z}` of WP-P's cut data (`Cuts.SpecData`) over `𝔽_p`,
`p ≡ 3 (mod 4)` implicit in the finite tests.

`spectral_criterion_cut` chains:
* `couplingBound_cut_counted` (`cor:spec2:coupling`, with instance (A) of `def:coupling-data`
  built from the counts: `rho_counts`, `PA_density`);
* `mucentre_cut_real` (`prop:spec2:mucentre` (c3), (c4), star part discharged by WP-A's glue);
* `cut_lower_real_of_real` (`RouteAInputs` in the complex realization, WP-A's `routeA_lower`,
  and the transfer to real `f`).

Its hypotheses are exactly:
* the literature inputs `Target.Weil`, `Target.MovingRoot`;
* error conditions: `e_{t_i}(p, n') < 1` (`he1`), the sequential lower counts `L_i > 0`
  (`hLpos`) along orderings `l_i`, `graphCountError < 1` (`he`);
* the inputs of the character expansion: `Op = K₀/Z₀`, `K₀ = 1 ⊗ 1 + T_star + T_ns − T_coll`
  (`lem:spec:expansion`), `‖T_ns‖ ≤ N_ns` (`lem:matching:extractionk`), `‖T_coll‖ ≤ D_col`
  (`lem:oct24-collision`), `Z₀ ≥ 1 − ε_Z` (`prop:spec2:mucentre`(c1));
* the numbers of `cor:spec2:coupling` (`Γ_E`, `D_j`, `θ`, `ρ_row`, `ζ̄`, `λ̄(𝐇) + ε_H`, `Λ_nc`,
  `Λ₊`, `Λ_D`) and of `lem:spec:degone` (`η_Q` via `hE`, `ε_V` via `hN`);
* WP-A's finite tests (`htp`, `htm`) and the scalar conditions on `c̄_⊥`, `s_±`, `g`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)`**: `⟪f, Op f⟫ ≥ −g r ‖f‖²` for every
real `f` in WP-A's real cut realization. See the module docstring for the hypotheses. -/
theorem spectral_criterion_cut [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    -- error conditions
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    (hLpos : ∀ i, 0 < Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i))
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the numbers of `cor:spec2:coupling`
    {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : D.cut.Half → ℂ, ∑ x, nuA D hne x * l2sq (fun a => ∑ j, w j *
      ((p : ℂ) * (PA D hne j x a : ℂ) - starProd D.Nset (sgnZ (p := p) D) j x a)) ≤
        ΓE * ∑ j, ‖w j‖ ^ 2)
    (Dj : D.cut.Half → ℝ) (hpiv : ∀ j x t, nuA D hne x ≠ 0 → condLaw (nuA D hne) j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    {ζ Λnc Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hHt : ∀ w : D.cut.Half → ℂ, (qform (gramΓ (nuA D hne) (psiField (PA D hne))) w).re ≤
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re + εH * ∑ j, ‖w j‖ ^ 2)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    (hnc : ∀ w : D.cut.Half → ℂ,
      PaleyB.hncQ Adj D.Nset (sgnZ (p := p) D) w ≤ Λnc * ∑ j, ‖w j‖ ^ 2)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) (sgnZ (p := p) D) ξ) ηQ)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne) he) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹)
        Λp εH θ ρ ΓE lamH ζ Λnc εV ΛD ηQ ≤ ηBbar)
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ : ZMod p, (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) D) ξ) x).re)
        (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ : ZMod p, ¬ (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) D) ξ) x).re)
        (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (f : EuclideanSpace ℝ (D.cut.Half → ZMod p)) :
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp D hne f⟫_ℝ := by
  have hWB := Labellings.weilBound_of_target hW p hp2
  have hbound := couplingBound_cut_counted D Adj hp2 hWB hn hne he1 l hnd hcov hdisj hLpos
    hΓ0 hΛ0 hΓ Dj hpiv hθ0 hθ hρ hζ0 hζ hHt hlam hnc hplus hΛD hηQ0 hDE hE hN hεV
  have hmu := mucentre_cut_real D hW hMR hp2 hne he K₀ Tns Tcoll hεZ hZ hT hK hns hcoll
  exact cut_lower_real_of_real D hp2 hne (sgnZ (p := p) D) hE hN
    (qXcx Adj D.Nset (sgnZ (p := p) D)) (qXcx_zero Adj D.Nset (sgnZ (p := p) D)) hbound
    hmu.1 hmu.2 hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
