module

public import Sarkozy.SpectralD.CxRchain
public import Sarkozy.SpectralOne.CriterionOne

@[expose] public section

/-!
# S1's chain with a density range `[c, R c]` and `R₊`, at both prime classes

`paper/sections/14_spectral.tex`, `thm:spectral-criterion`(a) with `R₊` of
`prop:spec2:mucentre`(c2) (the paper's choice at the root cuts, `lem:upper-completed-root`(ii)),
`subsec:advance:parity`.

S1's `CxRchain` repeats its chain with the density range of `ϱ` as data and ends with
`spectral_criterion_cut_fullRplus`; every step after `spectral_criterion_cut_threeR` uses
`p ≡ 3 (mod 4)` only to call the previous one. As in `ChainGen`, this file repeats it from
`spectral_criterion_cut_genR` (no class hypothesis; `ζ̄` and `Λ₊` as hypotheses), ending with
**`spectral_criterion_cut_fullRplus_gen`**.

New material for this paper.
-/

namespace Sarkozy.SpectralOne

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx Sarkozy.Characters
open scoped BigOperators InnerProductSpace

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`thm:spectral-criterion`(a) for the cut laws at every odd `p`, density range `[c, R c]`**:
S1's `Cx.spectral_criterion_cut_threeR` without `p ≡ 3 (mod 4)`; `ζ̄` (`hζ`, used only at
`p ≡ 1`) and `Λ₊ ≥ λ̄(𝐇 + [p ≡ 1]𝐇^cov)` (`hplus`) are hypotheses. -/
theorem spectral_criterion_cut_genR [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {cR RR : ℝ} (hcR : 0 < cR) (hRR : 1 ≤ RR)
    (hdensR : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      cR ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ RR * cR)
    -- error conditions
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    (hLpos : ∀ i, 0 < Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i))
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (he0 : ∀ j : D.cut.Half, TraceMixing.coarseErr p
      (Labellings.nbrCount D.halfGraph (univ.erase j) j) (Fintype.card D.cut.Half) < 1)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : D.cut.Half → ℂ, ∑ x, nuA D hne x * l2sq (fun a => ∑ j, w j *
      ((p : ℂ) * (PA D hne j x a : ℂ) - starProd D.Nset (sgnZ (p := p) D) j x a)) ≤
        ΓE * ∑ j, ‖w j‖ ^ 2)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      RR *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hHt : ∀ w : D.cut.Half → ℂ, (qform (gramΓ (nuA D hne) (psiField (PA D hne))) w).re ≤
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re + εH * ∑ j, ‖w j‖ ^ 2)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
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
    (hηB : etaBcx p (RR * cR)
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  -- the coupling data of instance (A)
  let DA := couplingDataA D hne (fun x hx => lt_of_lt_of_le hcR (hdensR x hx).1) cR RR hcR hRR
    hdensR
    (fun i => max 1 (Labellings.upperProd D.G (Fintype.card (ZMod p)) (fixSet D i) (l i) /
      Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i)))
    (fun i => le_max_left _ _)
    (fun i x hx a ha => PA_density D hWB hn hne l hnd hcov hdisj hLpos i hx ha)
  -- the pivot densities, from the graph law `λ(G⁺)`
  set D0 : D.cut.Half → ℝ := fun j => 2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
    (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
      (Fintype.card D.cut.Half)) with hD0
  have hμpiv : ∀ j x t, (D.halfLaw hne).weight x ≠ 0 →
      condLaw (D.halfLaw hne).weight j x t ≤ D0 j / p := fun j x t hx =>
    graphWeight_condLaw_le_coarse hWB D.halfGraph (D.half_nonempty hne) j (he0 j) x t hx
  have hpiv := PaleyB.pivot_of_density DA (D.halfLaw hne).nonneg
    (fun x hx => halfLaw_weight_off D hne hx) D0 hμpiv
  exact spectral_criterion_cutR D hW hMR Adj hp2 hn hne hcR hRR hdensR l hnd hcov hdisj hLpos he K₀
    Tns
    Tcoll hεZ hZ hT hK hns hcoll hΓ0 hΛ0 hΓ (fun j => RR * D0 j) hpiv hθ0 hθ hρ
    hζ0 hζ hHt hlam (fun w => hncQ_le_card Adj D.Nset (sgnZ (p := p) D) w) hplus
    hΛD hηQ0 hDE hE hN hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- *Both classes* (S2): S1's `Cx.spectral_criterion_cut_finalR` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_finalR_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {cR RR : ℝ} (hcR : 0 < cR) (hRR : 1 ≤ RR)
    (hdensR : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      cR ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ RR * cR)
    -- error conditions
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (heΔ : ∀ t ≤ Δ, TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn < 1)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (he0 : ∀ j : D.cut.Half, TraceMixing.coarseErr p
      (Labellings.nbrCount D.halfGraph (univ.erase j) j) (Fintype.card D.cut.Half) < 1)
    (hê : ∀ k : D.cut.Half,
      TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half) < 1)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      RR *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
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
    (hηB : etaBcx p (RR * cR)
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  obtain ⟨hρpos, hdens⟩ := rho_counts D hWB hn hne he1
  have hR1 := one_le_Rcut D he1
  set Rc := D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) with hRc
  have hRc0 : 0 < Rc := by linarith
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  -- the lower products along the orderings, and the densities
  have hLpos := lowerProd_pos_cut D heΔ hdeg l
  have hPd : ∀ i, ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      ∀ a ∈ allowedSet D.Nset (sgnZ D) i x,
        (Rprime p D nn l i)⁻¹ ≤ PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ∧
          PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ≤ Rprime p D nn l i :=
    fun i x hx a ha => PA_density D hWB hn hne l hnd hcov hdisj hLpos i hx ha
  have hRp : ∀ i, 1 ≤ Rprime p D nn l i := fun i => le_max_left _ _
  have hc : (0 : ℝ) < Rc⁻¹ := inv_pos.mpr hRc0
  have hR : (1 : ℝ) ≤ Rc ^ 2 := by nlinarith
  -- `Γ_E` and `ε_H` from the coarse counts
  have hw0 : ∀ w : D.cut.Half → ℂ, 0 ≤ ∑ j, ‖w j‖ ^ 2 := fun w => sum_nonneg fun j _ => sq_nonneg _
  have hΓ : ∀ w : D.cut.Half → ℂ, ∑ x, nuA D hne x * l2sq (fun a => ∑ j, w j *
      ((p : ℂ) * (PA D hne j x a : ℂ) - starProd D.Nset (sgnZ (p := p) D) j x a)) ≤
        ΓE * ∑ j, ‖w j‖ ^ 2 := fun w =>
    (gammaE_cut D hne hρpos Rc⁻¹ (Rc ^ 2) hc hR hdens (Rprime p D nn l) hRp hPd hWB hê w).trans
      (mul_le_mul_of_nonneg_right hΓc (hw0 w))
  have hΓ0 : 0 ≤ ΓE := by
    refine le_trans (sum_nonneg fun k _ => ?_) hΓc
    have h1 := TraceMixing.coarseErr_nonneg hq0 (D.Nset k).card (Fintype.card D.cut.Half)
    have h2 : (0 : ℝ) ≤ 2 ^ (D.Nset k).card * (1 + TraceMixing.coarseErr p (D.Nset k).card
        (Fintype.card D.cut.Half)) := mul_nonneg (by positivity) (by linarith)
    exact add_nonneg (mul_nonneg h2 (sq_nonneg _)) (by positivity)
  have hHt : ∀ w : D.cut.Half → ℂ, (qform (gramΓ (nuA D hne) (psiField (PA D hne))) w).re ≤
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re + εH * ∑ j, ‖w j‖ ^ 2 := fun w =>
    (hHt_cut D hne hρpos Rc⁻¹ (Rc ^ 2) hc hR hdens (Rprime p D nn l) hRp hPd hWB hê hrow hrowX
      w).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hεH (hw0 w)))
  exact spectral_criterion_cut_genR D hW hMR Adj hp2 hn hne hcR hRR hdensR l hnd hcov hdisj hLpos he
    he0 K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓ0 hΛ0 hΓ hθ0 hθ hρ hHt hlam hζ0 hζ hplus hΛD hηQ0 hDE
    hE hN hεV
    hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- *Both classes* (S2): S1's `Cx.spectral_criterion_cut_mainR` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_mainR_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {cR RR : ℝ} (hcR : 0 < cR) (hRR : 1 ≤ RR)
    (hdensR : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      cR ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ RR * cR)
    -- error conditions
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (heΔ : ∀ t ≤ Δ, TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn < 1)
    (he : ∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1)
    (he0 : ∀ j : D.cut.Half, TraceMixing.coarseErr p
      (Labellings.nbrCount D.halfGraph (univ.erase j) j) (Fintype.card D.cut.Half) < 1)
    (hê : ∀ k : D.cut.Half,
      TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half) < 1)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      RR *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    (mX : D.cut.Half → D.cut.Half → ℝ) (hmX0 : ∀ k l, 0 ≤ mX k l)
    (hmXsym : ∀ k l, mX k l = mX l k)
    (hsmall : ∀ k l, sgnZ (p := p) D k l = 0 →
      ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l‖ ≤ mX k l)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mX k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    (mV : D.cut.Half → D.cut.Half → ℝ) (hmV0 : ∀ k l, 0 ≤ mV k l)
    (hmVsym : ∀ k l, mV k l = mV l k)
    (hΔμ : ∀ k l, k ≠ l → ‖deltaMu (D.halfLaw hne).weight k l‖ ≤ mV k l)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mV k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne) he) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (RR * cR)
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  have hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) (sgnZ (p := p) D) ξ) ηQ :=
    fun ξ _ => normLe_mono (errQ_cut D hp2 hne hDE hΛD mX hmX0 hmXsym hsmall hrowS ξ) hηQc
  have hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV :=
    fun ξ _ => normLe_mono (degoneN_cut D hp2 hne mV hmV0 hmVsym hΔμ hrowV ξ) hεVc
  exact spectral_criterion_cut_finalR_gen D hW hMR Adj hp2 hn hne hcR hRR hdensR he1 l hnd hcov
    hdisj hdeg heΔ
    he he0 hê K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hζ0 hζ
    hplus hΛD hηQ0
    hDE hE hN hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- *Both classes* (S2): S1's `Cx.spectral_criterion_cut_S1R` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_S1R_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {cR RR : ℝ} (hcR : 0 < cR) (hRR : 1 ≤ RR)
    (hdensR : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      cR ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ RR * cR)
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      RR *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    (mX : D.cut.Half → D.cut.Half → ℝ) (hmX0 : ∀ k l, 0 ≤ mX k l)
    (hmXsym : ∀ k l, mX k l = mX l k)
    (hsmall : ∀ k l, sgnZ (p := p) D k l = 0 →
      ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l‖ ≤ mX k l)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mX k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    (mV : D.cut.Half → D.cut.Half → ℝ) (hmV0 : ∀ k l, 0 ≤ mV k l)
    (hmVsym : ∀ k l, mV k l = mV l k)
    (hΔμ : ∀ k l, k ≠ l → ‖deltaMu (D.halfLaw hne).weight k l‖ ≤ mV k l)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mV k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (RR * cR)
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  obtain ⟨he1, heΔ, he, he0, hê⟩ := errors_of_S1 D hn hdeg hS1
  exact spectral_criterion_cut_mainR_gen D hW hMR Adj hp2 hn hne hcR hRR hdensR he1 l hnd hcov
    hdisj hdeg heΔ
    he he0 hê K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hζ0 hζ
    hplus hΛD hηQ0
    hDE mX hmX0 hmXsym hsmall hrowS hηQc mV hmV0 hmVsym hΔμ hrowV hεVc hεV hcbar0 hcbar hηQ hηB
    hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- *Both classes* (S2): S1's `Cx.spectral_criterion_cut_smallR` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_smallR_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {cR RR : ℝ} (hcR : 0 < cR) (hRR : 1 ≤ RR)
    (hdensR : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      cR ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ RR * cR)
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (D.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (D.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp D hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne D hne, x⟫_ℝ • Spectral.cutOne D hne +
      Spectral.starOp D hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      RR *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (RR * cR)
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  exact spectral_criterion_cut_S1R_gen D hW hMR Adj hp2 hn hne hcR hRR hdensR hdeg hS1 l hnd hcov
    hdisj K₀ Tns
    Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hζ0 hζ hplus hΛD hηQ0 hDE
    (mXcut p D)
    (mXcut_nonneg D hn hdeg hS1) (mXcut_symm D) (fun k l h => hsmall_cut D hn hdeg hS1 hWB hne k l h)
    hrowS hηQc (mVcut p D) (mVcut_nonneg D hn hdeg hS1) (mVcut_symm D)
    (fun k l h => hDeltaMu_cut D hn hdeg hS1 hWB hne k l h) hrowV hεVc hεV hcbar0 hcbar hηQ hηB
    hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- *Both classes* (S2): S1's `Cx.spectral_criterion_cut_expR` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_expR_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {cR RR : ℝ} (hcR : 0 < cR) (hRR : 1 ≤ RR)
    (hdensR : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      cR ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ RR * cR)
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion: bounds for the explicit nonstar and collision operators
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1)
    (hns : ∀ x, ‖nsOp D hne x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖collOp D hne x‖ ≤ Dcol * ‖x‖)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p hp2) D.halfGraph (D.half_nonempty hne)
        (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      RR *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (RR * cR)
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  have he := (errors_of_S1 D hn hdeg hS1).2.2.1
  have hZ : 1 - εZ ≤ Z0 D hne := le_trans (by linarith) (Z0_lower D hne hW hMR hp2 he hns hcoll)
  exact spectral_criterion_cut_smallR_gen D hW hMR Adj hp2 hn hne hcR hRR hdensR hdeg hS1 l hnd
    hcov hdisj
    (K0op D hne) (nsOp D hne) (collOp D hne) hεZ hZ (cutOp_eq_K0 D hne) (K0_expansion D hne hp2)
    hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hζ0 hζ hplus hΛD hηQ0 hDE hrowS hηQc hrowV hεVc
    hεV hcbar0
    hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at every odd `p` (both classes) with
the paper's
`R₊`**: as `spectral_criterion_cut_exp`, with `R₊ = 2^{m_×}∏𝔲(t_i)/((1 − ε_Z)∏𝔩(t⁰_i))`
(`rho_sup_le`) in `η_B` in place of `R_cut`, and the pivot densities `R₊ R_cut D⁰_j`.

*Both classes* (S2): S1's `Cx.spectral_criterion_cut_expRplus` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_expRplus_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (hL : 0 < ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j))
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion: bounds for the explicit nonstar and collision operators
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1)
    (hns : ∀ x, ‖nsOp D hne x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖collOp D hne x‖ ≤ Dcol * ‖x‖)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p hp2) D.halfGraph (D.half_nonempty hne)
        (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      ((2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j))) *
          D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn)) *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j)))
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  obtain ⟨he1, -, he, -, -⟩ := errors_of_S1 D hn hdeg hS1
  obtain ⟨-, hdens⟩ := rho_counts D hWB hn hne he1
  have hR1 := one_le_Rcut D he1
  set Rc := D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) with hRc
  have hRc0 : 0 < Rc := by linarith
  set Rp := 2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
    ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j)) with hRp
  have hsup : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ Rp := fun x hx =>
    rho_sup_le D hW hMR hp2 hne hn he hεZ hns hcoll hεZc hL hx
  obtain ⟨x0, hx0⟩ := D.half_nonempty hne
  have hRR : 1 ≤ Rp * Rc := by
    have h1 : Rc⁻¹ ≤ Rp := ((hdens x0 hx0).1).trans (hsup x0 hx0)
    calc (1 : ℝ) = Rc⁻¹ * Rc := by field_simp
      _ ≤ Rp * Rc := mul_le_mul_of_nonneg_right h1 hRc0.le
  have hdensR : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      Rc⁻¹ ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ Rp * Rc * Rc⁻¹ := fun x hx =>
    ⟨(hdens x hx).1, by rw [mul_assoc, mul_inv_cancel₀ hRc0.ne', mul_one]; exact hsup x hx⟩
  have e : Rp * Rc * Rc⁻¹ = Rp := by field_simp
  exact spectral_criterion_cut_expR_gen D hW hMR Adj hp2 hn hne (inv_pos.mpr hRc0) hRR hdensR
    hdeg hS1 l hnd hcov hdisj hεZ hns hcoll hεZc hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hζ0 hζ hplus
    hΛD hηQ0
    hDE hrowS hηQc hrowV hεVc hεV hcbar0 hcbar hηQ (by rw [e]; exact hηB) hεVb hεV0 hεV1 hsp hsm
    htp htm hgp hgm f

/-- `spectral_criterion_cut_X1` with the paper's `R₊` (`spectral_criterion_cut_expRplus`).

*Both classes* (S2): S1's `Cx.spectral_criterion_cut_X1Rplus` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_X1Rplus_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (hL : 0 < ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j))
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion: X1's nonstar bound, `Extraction`'s collision bounds
    {εZ Nns Dcol D1 D2 : ℝ} (hεZ : εZ < 1) (hNns0 : 0 ≤ Nns) (hD10 : 0 ≤ D1) (hD20 : 0 ≤ D2)
    (hnsX : ∀ f g : (D.cut.Half → ZMod p) → ℝ,
      |(D.halfLaw hne).expect (fun x => f x * (D.halfLaw hne).expect (fun x' =>
        (∑ S ∈ Extraction.nonstars D.crossPairs, ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x') *
          g x'))| ≤
        Nns * Real.sqrt ((D.halfLaw hne).expect (fun x => f x ^ 2)) *
          Real.sqrt ((D.halfLaw hne).expect (fun x => g x ^ 2)))
    (hcoll1 : Sarkozy.Influence.OpBound (Labellings.injLabellings (ZMod p) D.halfGraph)
      (Labellings.injLabellings (ZMod p) D.halfGraph)
      (fun x x' => Extraction.collisionKernel1 D.sgn x x' /
        (Labellings.injLabellings (ZMod p) D.halfGraph).card) D1)
    (hcoll2 : Sarkozy.Influence.OpBound (Labellings.injLabellings (ZMod p) D.halfGraph)
      (Labellings.injLabellings (ZMod p) D.halfGraph)
      (fun x x' => Extraction.collisionKernel2 D.sgn x x' /
        (Labellings.injLabellings (ZMod p) D.halfGraph).card) D2)
    (hDcol : D1 + D2 ≤ Dcol)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p hp2) D.halfGraph (D.half_nonempty hne)
        (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      ((2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j))) *
          D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn)) *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j)))
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  have hns : ∀ x, ‖nsOp D hne x‖ ≤ Nns * ‖x‖ := by
    intro v
    have hk : nsKer (p := p) D = fun x x' => ∑ S ∈ Extraction.nonstars D.crossPairs,
        ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x' := by
      funext x x'
      exact nsKer_eq D x x'
    unfold nsOp
    rw [hk]
    exact kernelOp_norm_le_of_bilinear (D.halfLaw hne) _ hNns0 hnsX v
  have hcoll : ∀ x, ‖collOp D hne x‖ ≤ Dcol * ‖x‖ := by
    intro v
    have hk : collKer (p := p) D = fun x x' => Extraction.collisionKernel1 D.sgn x x' +
        Extraction.collisionKernel2 D.sgn x x' := by
      funext x x'
      rw [collKer_eq, Extraction.collisionKernelColl_eq]
    unfold collOp
    rw [hk, kernelOp_add_ker]
    have h1 := kernelOp_norm_le_of_opBound D.halfGraph (D.half_nonempty hne) _ hD10 hcoll1 v
    have h2 := kernelOp_norm_le_of_opBound D.halfGraph (D.half_nonempty hne) _ hD20 hcoll2 v
    calc ‖Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel1 D.sgn x x') v +
          Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel2 D.sgn x x') v‖
        ≤ ‖Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel1 D.sgn x x') v‖ +
          ‖Spectral.kernelOp (D.halfLaw hne) (fun x x' => Extraction.collisionKernel2 D.sgn x x') v‖ :=
          norm_add_le _ _
      _ ≤ D1 * ‖v‖ + D2 * ‖v‖ := add_le_add h1 h2
      _ = (D1 + D2) * ‖v‖ := by ring
      _ ≤ Dcol * ‖v‖ := mul_le_mul_of_nonneg_right hDcol (norm_nonneg v)
  exact spectral_criterion_cut_expRplus_gen D hW hMR Adj hp2 hn hne hL hdeg hS1 l hnd hcov hdisj
    hεZ hns
    hcoll hεZc hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hζ0 hζ hplus hΛD hηQ0 hDE hrowS hηQc hrowV
    hεVc hεV hcbar0
    hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- **`spectral_criterion_cut_full` with the paper's `R₊`** in `η_B` (`rho_sup_le`).

*Both classes* (S2): S1's `Cx.spectral_criterion_cut_fullRplus` without `p ≡ 3 (mod 4)`;
`ζ̄`, `hζ` and `Λ₊` (`hplus`) as in `spectral_criterion_cut_genR`. -/
theorem spectral_criterion_cut_fullRplus_gen [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (hL : 0 < ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j))
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- the character expansion: the data of X1's and `Extraction`'s theorems
    (h4 : Extraction.FourCycleBound p)
    {Δ' : ℕ} (hΔ' : ∀ i, ExtractionK.cmpDeg D.halfGraph D.sgn i ≤ Δ')
    (𝔓 : Finset (Finset (D.cut.Half × D.cut.Half) × Finset (D.cut.Half × D.cut.Half)))
    (h𝔓 : Extraction.IsExactPartition D.crossPairs 𝔓 (Extraction.nonstars D.crossPairs))
    (wit : Finset (D.cut.Half × D.cut.Half) × Finset (D.cut.Half × D.cut.Half) →
      Fin 2 → D.cut.Half × D.cut.Half)
    (cx cz : Finset (D.cut.Half × D.cut.Half) × Finset (D.cut.Half × D.cut.Half) →
      Finset D.cut.Half)
    (bucket : Finset (D.cut.Half × D.cut.Half) × Finset (D.cut.Half × D.cut.Half) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, Extraction.IsWitness D.crossPairs c.1 c.2 (wit c))
    (hcovX : ∀ c ∈ 𝔓, Extraction.IsCover D.crossPairs c.1 c.2 (wit c) (cx c) (cz c))
    (hbucket : ∀ c ∈ 𝔓, ExtractionK.cmpOc D.halfGraph (D.crossPairs \ (c.1 ∪ c.2))
      (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c) ≤
        (bucket c : ℝ) * 2 ^ 𝔮)
    (ord : D.cut.Half → D.cut.Half → D.cut.Half → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (πc : ℕ → D.cut.Half → ℕ) (hπc : ∀ k, Function.Injective (πc k))
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hNns0 : 0 ≤ Nns)
    (hNnsB : (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        ExtractionK.cmpLambda0 D.halfGraph D.sgn (Fintype.card (ZMod p)) (Fintype.card D.cut.Half)
          (TraceMixing.coarseErr p Δ nn) 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ Extraction.twoCycleCount (ExtractionK.witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ ExtractionK.cmpEx D.halfGraph (D.crossPairs \ (c.1 ∪ c.2))
              (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c))) *
          Real.exp (ExtractionK.cmpGamma (Fintype.card (ZMod p)) (Fintype.card D.cut.Half) Δ' * (b * 2 ^ 𝔮))) ≤ Nns)
    (hDcol : Extraction.collisionD1 D.halfGraph D.sgn ord (Fintype.card (ZMod p))
        (Fintype.card D.cut.Half) +
      Extraction.collisionD2 D.halfGraph D.sgn πc (Fintype.card (ZMod p))
        (Fintype.card D.cut.Half) ≤ Dcol)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p hp2) D.halfGraph (D.half_nonempty hne)
        (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) + Nns + Dcol ≤
        εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rprime p D nn l k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) (Rprime p D nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : D.cut.Half,
      ((2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j))) *
          D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn)) *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one inputs (`subsec:advance:parity`)
    {ζ Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ΛD ηQ εV : ℝ} (hΛD : 0 ≤ ΛD) (hηQ0 : 0 ≤ ηQ) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (2 ^ D.mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) (D.tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn (D.t0deg j)))
        Λp εH θ ρ ΓE lamH ζ
        ((PaleyB.ncSets Adj).card * Fintype.card D.cut.Half : ℝ) εV ΛD ηQ ≤ ηBbar)
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
  have hqp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hU : Fintype.card D.cut.Half ≤ nn :=
    (Fintype.card_le_of_injective (fun u : D.cut.Half => u.1) fun a b h => Subtype.ext h).trans hn
  have hn' : Fintype.card D.cut.Half ≤ Fintype.card D.cut.Half := le_rfl
  have hce : ∀ t m : ℕ, Extraction.coarseError t (Fintype.card (ZMod p) : ℕ) (m : ℝ) =
      TraceMixing.coarseErr p t m := by
    intro t m
    rw [ZMod.card]
    unfold Extraction.coarseError Extraction.coarseH TraceMixing.coarseErr
    simp only [inv_pow, Real.sq_sqrt hqp.le, one_div]
    ring
  have hehat : ∀ i, Extraction.coarseError (Extraction.rowsDeg0 D.halfGraph i)
      (Fintype.card (ZMod p) : ℕ) (Fintype.card D.cut.Half : ℕ) ≤ TraceMixing.coarseErr p Δ nn := by
    intro i
    rw [hce]
    exact TraceMixing.coarseErr_mono hqp (graphNbrs_half_le D hdeg i) hU
  have hehat1 : TraceMixing.coarseErr p Δ nn < 1 := hS1
  have hS1' : ∀ v, Extraction.coarseError (Extraction.rowsDeg0 D.halfGraph v)
      (Fintype.card (ZMod p) : ℕ) (Fintype.card D.cut.Half : ℕ) < 1 :=
    fun v => (hehat v).trans_lt hS1
  have hςv : ∀ j k, D.sgn j k = 0 ∨ D.sgn j k = 1 ∨ D.sgn j k = -1 := by
    intro j k
    unfold Cuts.SpecData.sgn
    split_ifs <;> simp
  have hanti : ∀ j k, D.sgn k j = -D.sgn j k := fun j k => D.sgn_antisymm j k
  have hEx : ∀ e ∈ D.crossPairs, D.sgn e.1 e.2 ≠ 0 := fun e he => by
    simp only [Cuts.SpecData.crossPairs, mem_filter, mem_univ, true_and] at he
    exact he
  have hq0 : (0 : ℝ) < (Fintype.card (ZMod p) : ℕ) := by exact_mod_cast Fintype.card_pos
  have hnsX : ∀ f g : (D.cut.Half → ZMod p) → ℝ,
      |(D.halfLaw hne).expect (fun x => f x * (D.halfLaw hne).expect (fun x' =>
        (∑ S ∈ Extraction.nonstars D.crossPairs, ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x') *
          g x'))| ≤
        Nns * Real.sqrt ((D.halfLaw hne).expect (fun x => f x ^ 2)) *
          Real.sqrt ((D.halfLaw hne).expect (fun x => g x ^ 2)) := fun f g =>
    (ExtractionK.extraction_compressed_buckets_two hp2 h4 hWB D.halfGraph D.sgn hςv hanti
      (D.half_nonempty hne) hn' hehat hehat1 hΔ' D.crossPairs hEx 𝔓 h𝔓 wit cx cz bucket 𝔮 hwit
      hcovX hbucket f g).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNnsB (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hcoll1 := Extraction.collision_opBound hWB D.halfGraph D.sgn hςv hanti
    (D.half_nonempty hne) hn' hS1' ord hord
  have hcoll2 := Extraction.collision_opBound2 hWB D.halfGraph D.sgn hςv hanti
    (D.half_nonempty hne) hn' hS1' πc hπc
  have hD10 := Extraction.collisionD1_nonneg D.halfGraph D.sgn ord hq0 hS1'
  have hD20 := Extraction.collisionD2_nonneg D.halfGraph D.sgn πc hq0 hS1'
  exact spectral_criterion_cut_X1Rplus_gen D hW hMR Adj hp2 hn hne hL hdeg hS1 l hnd hcov hdisj hεZ
    hNns0
    hD10 hD20 hnsX hcoll1 hcoll2 hDcol hεZc hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hζ0 hζ hplus hΛD
    hηQ0 hDE
    hrowS hηQc hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralOne
