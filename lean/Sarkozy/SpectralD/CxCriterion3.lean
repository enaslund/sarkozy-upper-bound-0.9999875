module

public import Sarkozy.SpectralD.CxCriterion
public import Sarkozy.SpectralD.CouplingInputs
public import Sarkozy.SpectralD.GraphPivotCoarse

@[expose] public section

/-!
# The spectral criterion for the cut at `p ≡ 3 (mod 4)`, with the structural inputs discharged

`paper/sections/14_spectral.tex`, `thm:spectral-criterion`(a) at class three. From
`spectral_criterion_cut`, four more inputs are discharged:
* `ζ̄ = 1` (`|t_J| ≤ r` always, fork B's `tJ_le_one_mul`); the class-one term drops at `p ≡ 3`;
* `Λ_nc = #{non-coverable J} · |U⁺|` (`hncQ_le_card`, Cauchy–Schwarz with `|ε_J| ≤ 1`); it
  enters `η_B` only with the class-one indicator;
* `Λ₊ = λ̄(𝐇)` at `p ≡ 3` (`𝐇⁺ = 𝐇`);
* the pivot densities of the coupling data, `D_j = R_cut² · 2^{t_j}/(1 − e_{t_j}(p, |U⁺|))`
  (fork B's `pivot_of_density` with S1's graph-law pivot bound `graphWeight_condLaw_le_coarse`
  for `μ = λ(G⁺)`, `t_j` the degree of `j` in `G⁺`).

`spectral_criterion_cut_three`: the conclusion `⟪f, Op f⟫ ≥ −g r‖f‖²` for real `f`, with only:
`Target.Weil`, `Target.MovingRoot`; the error conditions; the expansion inputs
(`lem:spec:expansion`, `lem:matching:extractionk`, `lem:oct24-collision`,
`prop:spec2:mucentre`(c1)); the certified numbers `Γ_E`, `ε_H`, `λ̄(𝐇)`, `θ`, `ρ_row`, `Λ_D`,
`η_Q`, `ε_V`; WP-A's finite tests and scalar conditions.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators InnerProductSpace

/-- `w^*𝐇^nc w ≤ #{non-coverable J} · |U| · |w|²`. -/
theorem hncQ_le_card {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]
    (Adj : U → U → Prop) [DecidableRel Adj] (N : U → Finset U) (ς : U → U → ZMod p)
    (w : U → ℂ) :
    PaleyB.hncQ Adj N ς w ≤
      ((PaleyB.ncSets Adj).card * Fintype.card U : ℝ) * ∑ k, ‖w k‖ ^ 2 := by
  unfold PaleyB.hncQ
  have hJ : ∀ J : Finset U, ‖∑ k, PaleyB.epsJ N ς J k * w k‖ ^ 2 ≤
      (Fintype.card U : ℝ) * ∑ k, ‖w k‖ ^ 2 := by
    intro J
    have h1 : ‖∑ k, PaleyB.epsJ N ς J k * w k‖ ≤ ∑ k, ‖w k‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
      rw [norm_mul]
      have := PaleyB.norm_epsJ_le N ς J k
      have h2 : ‖PaleyB.epsJ N ς J k‖ ≤ 1 := this.trans (by split_ifs <;> norm_num)
      calc ‖PaleyB.epsJ N ς J k‖ * ‖w k‖ ≤ 1 * ‖w k‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖w k‖ := one_mul _
    have h3 : (∑ k, ‖w k‖) ^ 2 ≤ (Fintype.card U : ℝ) * ∑ k, ‖w k‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset U)) (f := fun k => ‖w k‖)
      simpa [card_univ] using this
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h3
  calc ∑ J ∈ PaleyB.ncSets Adj, ‖∑ k, PaleyB.epsJ N ς J k * w k‖ ^ 2
      ≤ ∑ _J ∈ PaleyB.ncSets Adj, (Fintype.card U : ℝ) * ∑ k, ‖w k‖ ^ 2 :=
        sum_le_sum fun J _ => hJ J
    _ = ((PaleyB.ncSets Adj).card * Fintype.card U : ℝ) * ∑ k, ‖w k‖ ^ 2 := by
        rw [sum_const, nsmul_eq_mul]; ring

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**, with `ζ̄`,
`Λ_nc`, `Λ₊` and the pivot densities discharged. -/
theorem spectral_criterion_cut_three [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    -- error conditions
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
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
      D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hHt : ∀ w : D.cut.Half → ℂ, (qform (gramΓ (nuA D hne) (psiField (PA D hne))) w).re ≤
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re + εH * ∑ j, ‖w j‖ ^ 2)
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
  -- the coupling data of instance (A)
  let DA := couplingDataA D hne hρpos Rc⁻¹ (Rc ^ 2) (inv_pos.mpr hRc0) (by nlinarith) hdens
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
  -- `ζ̄ = 1`, `Λ_nc`, `Λ₊ = λ̄(𝐇)`
  have hν0 : ∀ x, 0 ≤ nuA D hne x := DA.ν_nonneg
  have hν1 : ∑ x, nuA D hne x = 1 := PaleyB.couplingData_sum_ν DA
  have hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ 1 * rp p :=
    fun _ J _ _ => PaleyB.tJ_le_one_mul hp2 (nuA D hne) hν0 hν1 J
  have hp1 : p % 4 ≠ 1 := by omega
  have hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        lamH * ∑ j, ‖w j‖ ^ 2 := by
    intro w
    simp only [hp1, ↓reduceIte, zero_mul, add_zero]
    exact hlam w
  exact spectral_criterion_cut D hW hMR Adj hp2 hn hne he1 l hnd hcov hdisj hLpos he K₀ Tns
    Tcoll hεZ hZ hT hK hns hcoll hΓ0 hΛ0 hΓ (fun j => Rc ^ 2 * D0 j) hpiv hθ0 hθ hρ
    zero_le_one hζ hHt hlam (fun w => hncQ_le_card Adj D.Nset (sgnZ (p := p) D) w) hplus
    hΛD hηQ0 hDE hE hN hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
