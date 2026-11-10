module

public import Sarkozy.SpectralD.CxCounts

@[expose] public section

/-!
# The spectral criterion for the cut laws, with the counting inputs discharged

`paper/sections/14_spectral.tex`, `thm:spectral-criterion`(a) for `λ_p(G⁺)` at `p ≡ 3 (mod 4)`.
`spectral_criterion_cut_final` is `spectral_criterion_cut_three` with the following inputs
discharged, for any orderings `l_i` of the remaining vertices (e.g. `restList`):
* `L_i > 0`, from `e_t(p, n') < 1` for `t ≤ Δ` and the degree bound `Δ` (`lowerProd_pos_cut`);
* the densities, with `R'_i = Rprime p D nn l i = max(1, U_i/L_i)` (`PA_density`);
* `hΓ` from the scalar condition `Ê² ≤ Γ_E` (`hΓc`; `gammaE_cut`, the coarse counts);
* `hHt` from the row sums of `β` and `b^X` (`hHt_cut`, WP-K's `gram_comparison`), i.e.
  `ε_H = ε'_H + ε_X`.

These are the paper's standard choices `Γ_E = Ê²`, `ε_H = ε'_H + ε_X` (`cor:spec2:coupling`).
For the refined inputs `Γ^loc_E` (`lem:projection-diagonal`) and `ε^loc_H`
(`lem:push:conditionalgram`), use `spectral_criterion_cut_three`, which takes `hΓ` and `hHt`
directly. `Λ_D ≥ ‖Δ^E‖` (`hDE`) and `ρ_row` (`hρ`) are taken in the paper's form; `CxInputs`
gives sufficient conditions (`deltaE_normLe`, `rhoRow_le`).

Remaining hypotheses: `Target.Weil`, `Target.MovingRoot`; the orderings `l_i`; scalar error
conditions; the expansion inputs (`hT`, `hK`, `hns`, `hcoll`, `hZ`); scalar and row-sum
conditions on explicit reals (`hΓc`, `hrow`, `hrowX`, `hεH`, `hθ`, `hρ`, and those of the
finite tests); the matrix certificates `hlam` (`λ̄(𝐇)`), `hDE` (`Λ_D`), `hE` (`η_Q`), `hN`
(`ε_V`); WP-A's finite tests (`htp`, `htm`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

variable (p) in
/-- The graded density constant `R'_i = max(1, U_i/L_i)` of `eq:spec:Rprime` along the
orderings `l_i`. -/
noncomputable def Rprime (nn : ℕ) (l : D.cut.Half → List W) (i : D.cut.Half) : ℝ :=
  max 1 (Labellings.upperProd D.G (Fintype.card (ZMod p)) (fixSet D i) (l i) /
    Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i))

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**, with the
counting inputs discharged; see the module docstring for the hypotheses. -/
theorem spectral_criterion_cut_final [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
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
      D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
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
    (hηB : etaBcx p (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹)
        lamH εH θ ρ ΓE lamH 1
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
  exact spectral_criterion_cut_three D hW hMR Adj hp2 hp3 hn hne he1 l hnd hcov hdisj hLpos he
    he0 K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓ0 hΛ0 hΓ hθ0 hθ hρ hHt hlam hΛD hηQ0 hDE hE hN hεV
    hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
