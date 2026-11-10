module

public import Sarkozy.SpectralD.CxDegone

@[expose] public section

/-!
# The error conditions from the single condition (S1) `e_Δ(p, n') < 1`

`paper/sections/14_spectral.tex`: the error conditions of the chain all follow from
`e_Δ(p, 2n) < 1`, where `Δ` is the maximum degree of `G`, by the monotonicity of `e_t(p, n)` in
`t` and `n` (`it:et:poly`, `coarseErr_mono`), since every degree that occurs is at most `Δ`.

* `tdeg_le`, `nbrCount_half_le`, `Nset_card_le`, `graphNbrs_half_le`: the degrees that occur
  (deletion degrees, degrees in `G⁺`, cross degrees `r_k`) are at most `Δ`;
* `graphCountError_lt`: `graphCountError < 1` from `e_t(p, |U⁺|) < 1`;
* `errors_of_S1`: all five error conditions from `e_Δ(p, n') < 1` and the degree bound;
* `spectral_criterion_cut_S1`: `spectral_criterion_cut_main` with the error conditions
  replaced by (S1).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

section Degrees

variable {Δ : ℕ}
  (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
include hdeg

/-- The deletion degrees `t_i` are at most `Δ`. -/
lemma tdeg_le (i : Fin D.cut.half.card) : D.tdeg i ≤ Δ := by
  refine le_trans (card_le_card fun w hw => ?_) (hdeg (D.order i).1)
  simp only [mem_filter, mem_univ, true_and] at hw ⊢
  exact hw.1

/-- The degrees of `G⁺` are at most `Δ`. -/
lemma nbrCount_half_le (j : D.cut.Half) :
    Labellings.nbrCount D.halfGraph (univ.erase j) j ≤ Δ := by
  classical
  unfold Labellings.nbrCount
  refine le_trans ?_ (hdeg j.1)
  refine card_le_card_of_injOn (fun u => u.1) ?_ ?_
  · intro u hu
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, mem_erase,
      Cuts.SpecData.halfGraph] at hu ⊢
    rcases hu.2 with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro a _ b _ h
    exact Subtype.ext h

/-- The neighbourhoods of `G⁺` have at most `Δ` elements. -/
lemma graphNbrs_half_le (j : D.cut.Half) : (SecondOrder.graphNbrs D.halfGraph j).card ≤ Δ := by
  classical
  unfold SecondOrder.graphNbrs
  refine le_trans ?_ (hdeg j.1)
  refine card_le_card_of_injOn (fun u => u.1) ?_ ?_
  · intro u hu
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and, Cuts.SpecData.halfGraph] at hu ⊢
    rcases hu with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro a _ b _ h
    exact Subtype.ext h

/-- The cross degrees `r_k = |N(k)|` are at most `Δ`. -/
lemma Nset_card_le (k : D.cut.Half) : (D.Nset k).card ≤ Δ := by
  classical
  refine le_trans ?_ (hdeg (D.cut.flip k.1))
  refine card_le_card_of_injOn (fun j => j.1) ?_ ?_
  · intro j hj
    simp only [Finset.mem_coe, Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] at hj ⊢
    unfold Cuts.SpecData.sgn at hj
    split_ifs at hj with h1 h2
    · exact Or.inr h1
    · exact Or.inl h2
    · exact absurd rfl hj
  · intro a _ b _ h
    exact Subtype.ext h

end Degrees

/-- `graphCountError < 1` from `e_t(p, |U|) < 1`, `t` the degree. -/
lemma graphCountError_lt {U : Type*} [Fintype U] [DecidableEq U] (G : Labellings.OrientedGraph U)
    (i : U)
    (h : TraceMixing.coarseErr p (SecondOrder.graphNbrs G i).card (Fintype.card U) < 1) :
    SecondOrder.graphCountError (p := p) G i < 1 := by
  unfold SecondOrder.graphCountError
  set t := (SecondOrder.graphNbrs G i).card with ht
  set n := Fintype.card U with hn
  have hq1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hq0 : (0 : ℝ) < p := by linarith
  have hsoft := Cuts.SpecData.softError_le hq1 t
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  set H := (t : ℝ) / 2 - 1 + (1 / 2) ^ t with hH
  have hs1 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hq0.le
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hq0
  have hpinv : (p : ℝ) * (Real.sqrt p)⁻¹ = Real.sqrt p := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hsp.ne', hs1]
  have hE : (p : ℝ) * TraceMixing.coarseErr p t n = 2 ^ t * (H * Real.sqrt p + n) := by
    unfold TraceMixing.coarseErr
    rw [← hH]
    calc (p : ℝ) * (2 ^ t * (H * (Real.sqrt p)⁻¹ + n / p))
        = 2 ^ t * (H * ((p : ℝ) * (Real.sqrt p)⁻¹) + n * ((p : ℝ) / p)) := by ring
      _ = 2 ^ t * (H * Real.sqrt p + n) := by rw [hpinv, div_self hq0.ne', mul_one]
  have hlt : (p : ℝ) * TraceMixing.coarseErr p t n < p := mul_lt_of_lt_one_right hq0 h
  rw [hE] at hlt
  rw [div_le_iff₀ h2] at hsoft
  rw [div_lt_one hq0]
  nlinarith

/-- **(S1) gives all the error conditions**: with `e_Δ(p, n') < 1`, `|W| ≤ n'` and the degree
bound `Δ`, the conditions `he1`, `heΔ`, `he`, `he0`, `hê` of the criterion hold. -/
theorem errors_of_S1 {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1) :
    (∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1) ∧
    (∀ t ≤ Δ, TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn < 1) ∧
    (∀ i, SecondOrder.graphCountError (p := p) D.halfGraph i < 1) ∧
    (∀ j : D.cut.Half, TraceMixing.coarseErr p
      (Labellings.nbrCount D.halfGraph (univ.erase j) j) (Fintype.card D.cut.Half) < 1) ∧
    (∀ k : D.cut.Half,
      TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half) < 1) := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : ((Fintype.card (ZMod p) : ℕ) : ℝ) = p := by rw [ZMod.card]
  have hU : Fintype.card D.cut.Half ≤ nn :=
    (Fintype.card_le_of_injective (fun u : D.cut.Half => u.1) fun a b h => Subtype.ext h).trans hn
  have hmono : ∀ {t n : ℕ}, t ≤ Δ → n ≤ nn → TraceMixing.coarseErr p t n < 1 :=
    fun ht hn' => lt_of_le_of_lt (TraceMixing.coarseErr_mono hq0 ht hn') hS1
  refine ⟨fun i => ?_, fun t ht => ?_, fun i => ?_, fun j => ?_, fun k => ?_⟩
  · rw [hc]; exact hmono (tdeg_le D hdeg i) le_rfl
  · rw [hc]; exact hmono ht le_rfl
  · exact graphCountError_lt D.halfGraph i (hmono (graphNbrs_half_le D hdeg i) hU)
  · exact hmono (nbrCount_half_le D hdeg j) hU
  · exact hmono (Nset_card_le D hdeg k) hU

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**, with the error
conditions replaced by (S1) `e_Δ(p, n') < 1` (`errors_of_S1`); otherwise as
`spectral_criterion_cut_main`. -/
theorem spectral_criterion_cut_S1 [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
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
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
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
  obtain ⟨he1, heΔ, he, he0, hê⟩ := errors_of_S1 D hn hdeg hS1
  exact spectral_criterion_cut_main D hW hMR Adj hp2 hp3 hn hne he1 l hnd hcov hdisj hdeg heΔ
    he he0 hê K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hΛD hηQ0
    hDE mX hmX0 hmXsym hsmall hrowS hηQc mV hmV0 hmVsym hΔμ hrowV hεVc hεV hcbar0 hcbar hηQ hηB
    hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
