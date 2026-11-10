module

public import Sarkozy.SpectralD.CxCriterionFinal

@[expose] public section

/-!
# `η_Q` and `ε_V` for the cut (`lem:spec:degone`(b), (c))

`paper/sections/14_spectral.tex`, `lem:spec:degone`. For the cut law
`Λ = μ ⊗ μ · K/Z` (`μ = λ(G⁺)`):
* `deltaX_cross`: the cross constraints `δ^×_kl = χ(ς_kl)` whenever `ς_kl ≠ 0`. On the support
  of `Λ` the cut condition `CutOK` gives `χ(ς_kl(x'_l − x_k)) = 1`, and `Λ` has mass one;
* `errQ_cut`: `‖E_Q(ξ)‖ ≤ Λ_D/(p − 1) + (p/(p − 1))ρ_s + n/((p − 1)r)` from `‖Δ^E‖ ≤ Λ_D` and
  the small-pair bounds `|δ^×_kl| ≤ m_kl` on the pairs with `ς_kl = 0` (`lem:spec:small`(a),
  a hypothesis), via WP-K's `degone_block`;
* `degoneN_cut`: `‖𝐍(ξ) − I‖ ≤ (n − 1)/(p − 1) + (p/(p − 1)) r ρ_v` from the bounds
  `|Δ^μ_kl| ≤ m_kl` (`lem:spec:small`(b), a hypothesis), via WP-K's `degoneN_sub_one`;
* `spectral_criterion_cut_main`: `spectral_criterion_cut_final` with `hE`, `hN` replaced by
  these entrywise bounds and scalar conditions.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC Sarkozy.Characters
open scoped BigOperators InnerProductSpace

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- `ς_kl = 0 ↔ ς_lk = 0`. -/
lemma sgnZ_zero_iff (k l : D.cut.Half) : sgnZ (p := p) D k l = 0 ↔ sgnZ (p := p) D l k = 0 := by
  unfold sgnZ
  rw [D.sgn_antisymm k l]
  push_cast
  rw [neg_eq_zero]

/-- **The cross constraints** of `lem:spec:degone`(b): `δ^×_kl = χ(ς_kl)` when `ς_kl ≠ 0`. -/
theorem deltaX_cross (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (k l : D.cut.Half) (hkl : sgnZ (p := p) D k l ≠ 0) :
    deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l = chiC p (sgnZ (p := p) D k l) := by
  classical
  have hs : D.sgn k l ≠ 0 := fun h => hkl (by unfold sgnZ; rw [h]; simp)
  have hq : (k, l) ∈ D.crossPairs := by
    simp only [Cuts.SpecData.crossPairs, mem_filter, mem_univ, true_and]; exact hs
  unfold deltaX
  have hpt : ∀ z : (D.cut.Half → ZMod p) × (D.cut.Half → ZMod p),
      (cutLaw (D.halfLaw hne).weight (cutKn D hne) z : ℂ) * chiC p (z.2 l - z.1 k) =
        (cutLaw (D.halfLaw hne).weight (cutKn D hne) z : ℂ) * chiC p (sgnZ (p := p) D k l) := by
    intro z
    by_cases hz : D.CutOK z.1 z.2
    · have h1 : quadraticChar (ZMod p) (sgnZ (p := p) D k l * (z.2 l - z.1 k)) = 1 :=
        hz.2 (k, l) hq
      have hne' : sgnZ (p := p) D k l * (z.2 l - z.1 k) ≠ 0 := fun h0 => by
        rw [h0, quadraticChar_zero] at h1; exact zero_ne_one h1
      have h2 : quadraticChar (ZMod p) (z.2 l - z.1 k) =
          quadraticChar (ZMod p) (sgnZ (p := p) D k l) :=
        (sq_cond_iff hkl _).mp ⟨hne', (quadraticChar_one_iff_isSquare hne').mp h1⟩
      have h3 : chiC p (z.2 l - z.1 k) = chiC p (sgnZ (p := p) D k l) := by
        simp only [chiC, MulChar.ringHomComp_apply, h2]
      rw [h3]
    · have h0 : cutLaw (D.halfLaw hne).weight (cutKn D hne) z = 0 := by
        unfold cutLaw cutKn Cuts.SpecData.cutK
        simp [hz]
      rw [h0, Complex.ofReal_zero, zero_mul, zero_mul]
  rw [sum_congr rfl fun z _ => hpt z, ← sum_mul, ← Complex.ofReal_sum, cutLaw_total D hne]
  simp

/-- **`η_Q` for the cut** (`lem:spec:degone`(b), WP-K's `degone_block`), from `‖Δ^E‖ ≤ Λ_D` and
the small-pair bounds `|δ^×_kl| ≤ m_kl` for `ς_kl = 0` (`lem:spec:small`(a)). -/
theorem errQ_cut (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {ΛD : ℝ} (hD : NormLe (deltaE (sgnZ (p := p) D)) ΛD) (hΛD : 0 ≤ ΛD)
    (m : D.cut.Half → D.cut.Half → ℝ) (hm0 : ∀ k l, 0 ≤ m k l) (hmsym : ∀ k l, m k l = m l k)
    (hsmall : ∀ k l, sgnZ (p := p) D k l = 0 →
      ‖deltaX (cutLaw (D.halfLaw hne).weight (cutKn D hne)) k l‖ ≤ m k l)
    {ρs : ℝ} (hrow : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then m k l else 0) ≤ ρs)
    (ξ : ZMod p) :
    NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) (sgnZ (p := p) D) ξ)
      (ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p)) :=
  degone_block hp2 _ (sgnZ (p := p) D) (sgnZ_zero_iff D) hD hΛD
    (fun k l h => deltaX_cross D hne k l h) m hm0 hmsym hsmall hrow ξ

/-- **`ε_V` for the cut** (`lem:spec:degone`(c), WP-K's `degoneN_sub_one`), from the bounds
`|Δ^μ_kl| ≤ m_kl` for `k ≠ l` (`lem:spec:small`(b)). -/
theorem degoneN_cut (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (m : D.cut.Half → D.cut.Half → ℝ) (hm0 : ∀ k l, 0 ≤ m k l) (hmsym : ∀ k l, m k l = m l k)
    (hΔ : ∀ k l, k ≠ l → ‖deltaMu (D.halfLaw hne).weight k l‖ ≤ m k l)
    {ρv : ℝ} (hrow : ∀ k, ∑ l, (if k = l then 0 else m k l) ≤ ρv) (ξ : ZMod p) :
    NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l - if k = l then 1 else 0)
      (((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv) :=
  degoneN_sub_one hp2 _ m hm0 hmsym hΔ hrow ξ

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**: as
`spectral_criterion_cut_final`, with `η_Q` and `ε_V` obtained from the entrywise bounds of
`lem:spec:small` (`hsmall`, `hΔμ`) and scalar conditions (`hηQc`, `hεVc`). -/
theorem spectral_criterion_cut_main [LinearOrder D.cut.Half] (hW : Target.Weil)
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
  have hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) (sgnZ (p := p) D) ξ) ηQ :=
    fun ξ _ => normLe_mono (errQ_cut D hp2 hne hDE hΛD mX hmX0 hmXsym hsmall hrowS ξ) hηQc
  have hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV :=
    fun ξ _ => normLe_mono (degoneN_cut D hp2 hne mV hmV0 hmVsym hΔμ hrowV ξ) hεVc
  exact spectral_criterion_cut_final D hW hMR Adj hp2 hp3 hn hne he1 l hnd hcov hdisj hdeg heΔ
    he he0 hê K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hΛD hηQ0
    hDE hE hN hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
