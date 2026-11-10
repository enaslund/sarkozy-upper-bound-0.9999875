module

public import Sarkozy.SpectralD.RootCriterion
public import Sarkozy.SpectralOne.ChainGen
public import Sarkozy.SpectralOne.Rfull

@[expose] public section

/-!
# The spectral criterion at the root cuts LL20 and LL22, at both classes

`paper/sections/25_upper_reference.tex`, `lem:upper-completed-root` (`𝔠 ∈ {1, 3}`);
`paper/sections/27_tail_index.tex`, proof of `lem:tail-law`(i): "The root caps `113` (LL20) and
`45` (LL22) come from the tests of both classes, the class-one ones with the class-one Paley terms
and the parity transfer". The root `G_{LL,2}` of these cuts is the graph of the tail law's root
component.

`LL20_criterion_one`, `LL22_criterion_one`: S1's `Root.LL20_criterion`, `Root.LL22_criterion`
(which are at `p ≡ 3 (mod 4)`) at every prime `p ≥ 2⁵²`, through `spectral_criterion_cut_S1_gen`,
with `ζ̄` discharged by `hzeta_cut_paper` and every count condition from S1's root facts
(`Δ = 20`, `n' = 72`, `n = 36`).

New material for this paper.
-/

namespace Sarkozy.SpectralOne

open scoped BigOperators InnerProductSpace
open Finset Sarkozy Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx Sarkozy.SpectralD.Root

/-- **`thm:spectral-criterion`(a) at the root cut LL20 at both classes**
(`lem:upper-completed-root` with `𝔠 ∈ {1, 3}`, `subsec:advance:parity`): S1's `Root.LL20_criterion`
without `p ≡ 3 (mod 4)`, for every prime `p ≥ 2⁵²`. `ζ̄` is discharged by `lem:spec2:paley-one`
(`hzeta_cut_paper`, the paper's `ζ = (R_cut R_full − 1) + n/((p − n) r)`, `n = |U⁺| = 36`), for any
relation `Adj` containing the adjacency of `G⁺`. The class-one inputs that remain are the certified
`Λ₊` with `𝐇^cov` (`hplus`) and the two finite tests (`htp`, `htm`); the paper's smaller root-cut
`ζ̄` of `lem:spec2:parity-transfer` is `hzeta_cut_min`, to be used with
`spectral_criterion_cut_S1_gen`. -/
theorem LL20_criterion_one {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : LL20.cut.Half → LL20.cut.Half → Prop) [DecidableRel Adj]
    (hAdj : ∀ i j : LL20.cut.Half, (i, j) ∈ LL20.halfGraph.E ∨ (j, i) ∈ LL20.halfGraph.E →
      Adj i j)
    (hp52 : 2 ^ 52 ≤ p)
    (hne : (Labellings.injLabellings (ZMod p) LL20.G).Nonempty)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (LL20.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (LL20.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp LL20 hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne LL20 hne, x⟫_ℝ • Spectral.cutOne LL20 hne +
      Spectral.starOp LL20 hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (LL20.Nset k).card *
          (1 + TraceMixing.coarseErr p (LL20.Nset k).card (Fintype.card LL20.cut.Half)) *
          devConst (Rprime p LL20 72 (restList LL20) k)
            (TraceMixing.coarseErr p (LL20.Nset k).card (Fintype.card LL20.cut.Half)) ^ 2 +
        (Fintype.card LL20.cut.Half : ℝ) * 4 ^ (LL20.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG LL20.Nset (sgnZ (p := p) LL20)
      (fun t => TraceMixing.coarseErr p t (Fintype.card LL20.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX LL20.Nset (sgnZ (p := p) LL20)
      (fun t => TraceMixing.coarseErr p t (Fintype.card LL20.cut.Half))
        (Rprime p LL20 72 (restList LL20)) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : LL20.cut.Half,
      LL20.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
        (2 ^ Labellings.nbrCount LL20.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount LL20.halfGraph (univ.erase j) j)
            (Fintype.card LL20.cut.Half))) - 1 ≤ θ ^ 2)
    (hlam : ∀ w : LL20.cut.Half → ℂ,
      (qform (PaleyB.modelHC LL20.Nset (sgnZ (p := p) LL20)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one input `Λ₊ ≥ λ̄(𝐇 + [p ≡ 1]𝐇^cov)` (`subsec:advance:parity`)
    {Λp : ℝ}
    (hplus : ∀ w : LL20.cut.Half → ℂ, (qform (PaleyB.modelHC LL20.Nset (sgnZ (p := p) LL20)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj LL20.Nset (sgnZ (p := p) LL20) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ηQ εV : ℝ} (hηQ0 : 0 ≤ ηQ)
    (mX : LL20.cut.Half → LL20.cut.Half → ℝ) (hmX0 : ∀ k l, 0 ≤ mX k l)
    (hmXsym : ∀ k l, mX k l = mX l k)
    (hsmall : ∀ k l, sgnZ (p := p) LL20 k l = 0 →
      ‖deltaX (cutLaw (LL20.halfLaw hne).weight (cutKn LL20 hne)) k l‖ ≤ mX k l)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) LL20 k l = 0 then mX k l else 0) ≤ ρs)
    (hηQc : 12 / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card LL20.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    (mV : LL20.cut.Half → LL20.cut.Half → ℝ) (hmV0 : ∀ k l, 0 ≤ mV k l)
    (hmVsym : ∀ k l, mV k l = mV l k)
    (hΔμ : ∀ k l, k ≠ l → ‖deltaMu (LL20.halfLaw hne).weight k l‖ ≤ mV k l)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mV k l) ≤ ρv)
    (hεVc : ((Fintype.card LL20.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned
          (Labellings.weilBound_of_target hW p (ne_two_of_ge hp52))
          LL20.halfGraph (LL20.half_nonempty hne)
          (errors_of_S1 LL20 card_slot.le LL20_hdeg (coarseErr_root_lt_nat hp52)).2.2.1)
          LL20.Nset (Spectral.starCoef (p := p) LL20) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (LL20.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
        (LL20.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72))⁻¹)
        Λp εH θ 301768740 ΓE lamH
        ((LL20.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) *
            RfullPaper (p := p) LL20 (Fintype.card LL20.cut.Half) - 1) +
          (Fintype.card LL20.cut.Half : ℝ) / (((p : ℝ) - Fintype.card LL20.cut.Half) * rp p))
        ((PaleyB.ncSets Adj).card * Fintype.card LL20.cut.Half : ℝ) εV 12 ηQ ≤ ηBbar)
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ : ZMod p, (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) LL20) ξ) x).re)
        (qXcx Adj LL20.Nset (sgnZ (p := p) LL20) ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ : ZMod p, ¬ (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) LL20) ξ) x).re)
        (qXcx Adj LL20.Nset (sgnZ (p := p) LL20) ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (f : EuclideanSpace ℝ (LL20.cut.Half → ZMod p)) :
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp LL20 hne f⟫_ℝ := by
  have hWB := Labellings.weilBound_of_target hW p (ne_two_of_ge hp52)
  obtain ⟨he1, -, -, he0, -⟩ :=
    errors_of_S1 LL20 card_slot.le LL20_hdeg (coarseErr_root_lt_nat hp52)
  have hmp : Fintype.card LL20.cut.Half < p := by
    have h1 : Fintype.card LL20.cut.Half ≤ Fintype.card Slot :=
      Fintype.card_le_of_injective (fun u : LL20.cut.Half => u.1) fun a b h => Subtype.ext h
    rw [card_slot] at h1
    omega
  have hR1 := one_le_RfullPaper LL20 he0
  exact spectral_criterion_cut_S1_gen LL20 hW hMR Adj (ne_two_of_ge hp52) card_slot.le hne LL20_hdeg
    (coarseErr_root_lt_nat hp52) (restList LL20) (restList_nodup LL20) (restList_cover LL20)
    (restList_disj LL20) K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ
    LL20_rho hlam (zeta_cut_nonneg LL20 he1 hmp hR1)
    (fun _ => hzeta_cut_paper LL20 hWB (ne_two_of_ge hp52) card_slot.le hne he1 le_rfl hmp he0 Adj
      hAdj) hplus (by norm_num) hηQ0 LL20_deltaE mX hmX0 hmXsym hsmall hrowS hηQc mV hmV0
    hmVsym hΔμ hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- **`thm:spectral-criterion`(a) at the root cut LL22 at both classes**
(`lem:upper-completed-root` with `𝔠 ∈ {1, 3}`, `subsec:advance:parity`): S1's `Root.LL22_criterion`
without `p ≡ 3 (mod 4)`, for every prime `p ≥ 2⁵²`. `ζ̄` is discharged by `lem:spec2:paley-one`
(`hzeta_cut_paper`, the paper's `ζ = (R_cut R_full − 1) + n/((p − n) r)`, `n = |U⁺| = 36`), for any
relation `Adj` containing the adjacency of `G⁺`. The class-one inputs that remain are the certified
`Λ₊` with `𝐇^cov` (`hplus`) and the two finite tests (`htp`, `htm`); the paper's smaller root-cut
`ζ̄` of `lem:spec2:parity-transfer` is `hzeta_cut_min`, to be used with
`spectral_criterion_cut_S1_gen`. -/
theorem LL22_criterion_one {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : LL22.cut.Half → LL22.cut.Half → Prop) [DecidableRel Adj]
    (hAdj : ∀ i j : LL22.cut.Half, (i, j) ∈ LL22.halfGraph.E ∨ (j, i) ∈ LL22.halfGraph.E →
      Adj i j)
    (hp52 : 2 ^ 52 ≤ p)
    (hne : (Labellings.injLabellings (ZMod p) LL22.G).Nonempty)
    -- the character expansion
    (K₀ Tns Tcoll : EuclideanSpace ℝ (LL22.cut.Half → ZMod p) →ₗ[ℝ]
      EuclideanSpace ℝ (LL22.cut.Half → ZMod p))
    {Z₀ εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, Spectral.cutOp LL22 hne x = (Z₀⁻¹ : ℝ) • K₀ x)
    (hK : ∀ x, K₀ x = ⟪Spectral.cutOne LL22 hne, x⟫_ℝ • Spectral.cutOne LL22 hne +
      Spectral.starOp LL22 hne x + Tns x - Tcoll x)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE lamH εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (LL22.Nset k).card *
          (1 + TraceMixing.coarseErr p (LL22.Nset k).card (Fintype.card LL22.cut.Half)) *
          devConst (Rprime p LL22 72 (restList LL22) k)
            (TraceMixing.coarseErr p (LL22.Nset k).card (Fintype.card LL22.cut.Half)) ^ 2 +
        (Fintype.card LL22.cut.Half : ℝ) * 4 ^ (LL22.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG LL22.Nset (sgnZ (p := p) LL22)
      (fun t => TraceMixing.coarseErr p t (Fintype.card LL22.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX LL22.Nset (sgnZ (p := p) LL22)
      (fun t => TraceMixing.coarseErr p t (Fintype.card LL22.cut.Half))
        (Rprime p LL22 72 (restList LL22)) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ lamH + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : LL22.cut.Half,
      LL22.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
        (2 ^ Labellings.nbrCount LL22.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount LL22.halfGraph (univ.erase j) j)
            (Fintype.card LL22.cut.Half))) - 1 ≤ θ ^ 2)
    (hlam : ∀ w : LL22.cut.Half → ℂ,
      (qform (PaleyB.modelHC LL22.Nset (sgnZ (p := p) LL22)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one input `Λ₊ ≥ λ̄(𝐇 + [p ≡ 1]𝐇^cov)` (`subsec:advance:parity`)
    {Λp : ℝ}
    (hplus : ∀ w : LL22.cut.Half → ℂ, (qform (PaleyB.modelHC LL22.Nset (sgnZ (p := p) LL22)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj LL22.Nset (sgnZ (p := p) LL22) w ≤
        Λp * ∑ j, ‖w j‖ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ηQ εV : ℝ} (hηQ0 : 0 ≤ ηQ)
    (mX : LL22.cut.Half → LL22.cut.Half → ℝ) (hmX0 : ∀ k l, 0 ≤ mX k l)
    (hmXsym : ∀ k l, mX k l = mX l k)
    (hsmall : ∀ k l, sgnZ (p := p) LL22 k l = 0 →
      ‖deltaX (cutLaw (LL22.halfLaw hne).weight (cutKn LL22 hne)) k l‖ ≤ mX k l)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) LL22 k l = 0 then mX k l else 0) ≤ ρs)
    (hηQc : 10 / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card LL22.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    (mV : LL22.cut.Half → LL22.cut.Half → ℝ) (hmV0 : ∀ k l, 0 ≤ mV k l)
    (hmVsym : ∀ k l, mV k l = mV l k)
    (hΔμ : ∀ k l, k ≠ l → ‖deltaMu (LL22.halfLaw hne).weight k l‖ ≤ mV k l)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mV k l) ≤ ρv)
    (hεVc : ((Fintype.card LL22.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hcbar0 : 0 ≤ cbar)
    (hcbar : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned
          (Labellings.weilBound_of_target hW p (ne_two_of_ge hp52))
          LL22.halfGraph (LL22.half_nonempty hne)
          (errors_of_S1 LL22 card_slot.le LL22_hdeg (coarseErr_root_lt_nat hp52)).2.2.1)
          LL22.Nset (Spectral.starCoef (p := p) LL22) +
          Nns + Dcol) / (1 - εZ)) ^ 2 ≤ cbar * rp p)
    (hηQ : ηQ ≤ ηQbar)
    (hηB : etaBcx p (LL22.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
        (LL22.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72))⁻¹)
        Λp εH θ 37675044 ΓE lamH
        ((LL22.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) *
            RfullPaper (p := p) LL22 (Fintype.card LL22.cut.Half) - 1) +
          (Fintype.card LL22.cut.Half : ℝ) / (((p : ℝ) - Fintype.card LL22.cut.Half) * rp p))
        ((PaleyB.ncSets Adj).card * Fintype.card LL22.cut.Half : ℝ) εV 10 ηQ ≤ ηBbar)
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ : ZMod p, (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) LL22) ξ) x).re)
        (qXcx Adj LL22.Nset (sgnZ (p := p) LL22) ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ : ZMod p, ¬ (IsSquare ξ ∧ ξ ≠ 0) →
      Sarkozy.Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) LL22) ξ) x).re)
        (qXcx Adj LL22.Nset (sgnZ (p := p) LL22) ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (f : EuclideanSpace ℝ (LL22.cut.Half → ZMod p)) :
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp LL22 hne f⟫_ℝ := by
  have hWB := Labellings.weilBound_of_target hW p (ne_two_of_ge hp52)
  obtain ⟨he1, -, -, he0, -⟩ :=
    errors_of_S1 LL22 card_slot.le LL22_hdeg (coarseErr_root_lt_nat hp52)
  have hmp : Fintype.card LL22.cut.Half < p := by
    have h1 : Fintype.card LL22.cut.Half ≤ Fintype.card Slot :=
      Fintype.card_le_of_injective (fun u : LL22.cut.Half => u.1) fun a b h => Subtype.ext h
    rw [card_slot] at h1
    omega
  have hR1 := one_le_RfullPaper LL22 he0
  exact spectral_criterion_cut_S1_gen LL22 hW hMR Adj (ne_two_of_ge hp52) card_slot.le hne LL22_hdeg
    (coarseErr_root_lt_nat hp52) (restList LL22) (restList_nodup LL22) (restList_cover LL22)
    (restList_disj LL22) K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ
    LL22_rho hlam (zeta_cut_nonneg LL22 he1 hmp hR1)
    (fun _ => hzeta_cut_paper LL22 hWB (ne_two_of_ge hp52) card_slot.le hne he1 le_rfl hmp he0 Adj
      hAdj) hplus (by norm_num) hηQ0 LL22_deltaE mX hmX0 hmXsym hsmall hrowS hηQc mV hmV0
    hmVsym hΔμ hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralOne
