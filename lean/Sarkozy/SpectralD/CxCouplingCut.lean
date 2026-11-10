module

public import Sarkozy.SpectralD.CxDensity

@[expose] public section

/-!
# The coupling bound for the cut with the counting content discharged

`paper/sections/14_spectral.tex`, `cor:spec2:coupling` for the cut operator, with instance (A)
of `def:coupling-data` built from the counts: `couplingBound_cut_counted` is
`couplingBound_cut` with
* `ϱ > 0` on `𝓘⁺` and `R_cut⁻¹ ≤ ϱ ≤ R_cut` from WP-P's `rho_Rcut` (`rho_counts`), and
* the densities `|Φ_i|P_i ∈ [1/R'_i, R'_i]` from the sequential counts (`PA_density`), with
  `R'_i = max(1, U_i/L_i)` along orderings `l_i` of the vertices outside `U⁺ ∪ {ϑi}` (any
  orderings; `L_i > 0` from WP-P's `lowerProd_pos` when `e_t(p, n') < 1` up to the maximal
  degree).

What remains are the paper's numbers (`Γ_E`, `D_j`/`θ`, `ρ_row`, `ζ̄`, the model bounds,
`Λ_D`, `η_Q`, `ε_V`) and the error conditions.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- The default orderings: the remaining vertices in any order (`Finset.toList`). -/
noncomputable def restList (i : D.cut.Half) : List W :=
  (univ.filter (fun w => w ∉ fixSet D i)).toList

theorem restList_nodup (i : D.cut.Half) : (restList D i).Nodup := nodup_toList _

theorem restList_cover (i : D.cut.Half) (w : W) : w ∈ fixSet D i ∨ w ∈ restList D i := by
  by_cases h : w ∈ fixSet D i
  · exact Or.inl h
  · right
    unfold restList
    rw [mem_toList, mem_filter]
    exact ⟨mem_univ _, h⟩

theorem restList_disj (i : D.cut.Half) : ∀ w ∈ restList D i, w ∉ fixSet D i := by
  intro w hw
  unfold restList at hw
  rw [mem_toList, mem_filter] at hw
  exact hw.2

/-- **`cor:spec2:coupling` for the cut, counting content discharged**: `CouplingBoundCx` for
`λ(G⁺)` and `K/Z` with `R₊ = R_cut` and `R'_i = max(1, U_i/L_i)`. Hypotheses: `thm:weil`
(`hW`), the error conditions `e_{t_i}(p, n') < 1` (`he1`) and `L_i > 0` (`hLpos`), the orderings
`l_i`, and the paper's numbers for the coupling data `couplingDataA` (stated for `ν = nuA`,
`P = PA`). -/
theorem couplingBound_cut_counted (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hW : Labellings.WeilBound (ZMod p)) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    (hLpos : ∀ i, 0 < Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i))
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
    {ΛD η εV : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) (sgnZ (p := p) D) ξ) η)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV) (hεV : 0 ≤ εV) :
    CouplingBoundCx (D.halfLaw hne).weight (cutKn D hne) (qXcx Adj D.Nset (sgnZ (p := p) D))
      (etaBcx p (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
          (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹)
        Λp εH θ ρ ΓE lamH ζ Λnc εV ΛD η) := by
  obtain ⟨hρpos, hdens⟩ := rho_counts D hW hn hne he1
  have hR1 := one_le_Rcut D he1
  set Rc := D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) with hRc
  have hRc0 : 0 < Rc := by linarith
  exact couplingBound_cut D Adj hp2 hne hρpos Rc⁻¹ (Rc ^ 2) (inv_pos.mpr hRc0)
    (by nlinarith) hdens
    (fun i => max 1 (Labellings.upperProd D.G (Fintype.card (ZMod p)) (fixSet D i) (l i) /
      Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i)))
    (fun i => le_max_left _ _)
    (fun i x hx a ha => PA_density D hW hn hne l hnd hcov hdisj hLpos i hx ha)
    hΓ0 hΛ0 hΓ Dj hpiv hθ0 hθ hρ hζ0 hζ hHt hlam hnc hplus hΛD hη hDE hE hN hεV

end Sarkozy.SpectralD.Cx
