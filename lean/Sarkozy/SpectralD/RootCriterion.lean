module

public import Sarkozy.SpectralD.RootChecks
public import Sarkozy.SpectralD.CxErrors

/-!
# The spectral criterion at the root cuts LL20 and LL22

`paper/sections/25_upper_reference.tex`, `subsec:record:upper_root` (route B at
`p ≡ 3 (mod 4)`), and `paper/sections/14_spectral.tex`, `thm:spectral-criterion`(a).

`LL20_criterion`, `LL22_criterion`: `Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1` at the root
cuts, for primes `p ≥ 2^52` with `p ≡ 3 (mod 4)`, with the hypotheses that are facts about the
root discharged:
* `p ≠ 2` (`ne_two_of_ge`), `|U| = 72` (`n' = 72`, `card_slot`);
* the degree bound `Δ = 20` (`LL20_hdeg`, `LL22_hdeg`) and (S1) `e_20(p, 72) < 1`
  (`coarseErr_root_lt_nat`);
* the orderings `l_i` of `eq:spec:Rprime` (`Cx.restList`);
* `ρ_row` (`LL20_rho`: `301768740`; `LL22_rho`: `37675044`);
* `Λ_D = max_k r_k` (`LL20_deltaE`: `12`; `LL22_deltaE`: `10`).

The total order of `U⁺` of `prop:advance:ordered-star` is the order of the code
`slotCode (u₀, u₁, ℓ) = 12 u₀ + 2 u₁ + ℓ` (`LL20_linearOrder`, `LL22_linearOrder`).

The remaining hypotheses are the paper's certified numbers (`cor:spec2:coupling`,
`lem:spec:degone`, the character expansion of the cut kernel and WP-A's finite tests), exactly as
in `spectral_criterion_cut_S1`; `Inj_p(G) ≠ ∅` (`hne`) is supplied by `LL20_hne`, `LL22_hne`.

New material for this paper.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.SpectralD.Root

open Sarkozy Sarkozy.SpectralC Sarkozy.SpectralD.Cx

/-- An injective code of the slots, `(u₀, u₁, ℓ) ↦ 12 u₀ + 2 u₁ + ℓ`. -/
def slotCode (v : Slot) : ℕ := v.1.val * 12 + v.2.1.val * 2 + v.2.2.val

theorem slotCode_injective : Function.Injective slotCode := by
  decide +kernel

/-- The total order of `U⁺` for LL20: the order of `slotCode`. -/
instance LL20_linearOrder : LinearOrder LL20.cut.Half :=
  LinearOrder.lift' (fun k => slotCode k.1) (slotCode_injective.comp Subtype.val_injective)

/-- The total order of `U⁺` for LL22: the order of `slotCode`. -/
instance LL22_linearOrder : LinearOrder LL22.cut.Half :=
  LinearOrder.lift' (fun k => slotCode k.1) (slotCode_injective.comp Subtype.val_injective)

theorem ne_two_of_ge {p : ℕ} (hp : 2 ^ 52 ≤ p) : p ≠ 2 := by
  omega

/-- **`thm:spectral-criterion`(a) at the root cut LL20** (`subsec:record:upper_root`, route B
at `p ≡ 3 (mod 4)`): `Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1` at `D := LL20`, for primes
`p ≥ 2^52` with `p ≡ 3 (mod 4)`, with these hypotheses discharged: `p ≠ 2`, `|U| = 72 ≤ n'`
(`n' = 72`), the degree bound `Δ = 20` (`LL20_hdeg`), (S1) `e_20(p, 72) < 1`
(`coarseErr_root_lt_nat`), the orderings `l_i` (`restList`), `ρ_row = 301768740` (`LL20_rho`) and
`Λ_D = 12 = max_k r_k` (`LL20_deltaE`). The remaining hypotheses are the certified numbers of
`cor:spec2:coupling`, `lem:spec:degone` and WP-A's finite tests, as in
`spectral_criterion_cut_S1`; `hne` is supplied by `LL20_hne`. The total order of `U⁺` is
`LL20_linearOrder` (any order works in `spectral_criterion_cut_S1`). -/
theorem LL20_criterion {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : LL20.cut.Half → LL20.cut.Half → Prop) [DecidableRel Adj]
    (hp52 : 2 ^ 52 ≤ p) (hp3 : p % 4 = 3)
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
        lamH εH θ 301768740 ΓE lamH 1
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
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp LL20 hne f⟫_ℝ :=
  spectral_criterion_cut_S1 LL20 hW hMR Adj (ne_two_of_ge hp52) hp3 card_slot.le hne LL20_hdeg
    (coarseErr_root_lt_nat hp52) (restList LL20) (restList_nodup LL20) (restList_cover LL20)
    (restList_disj LL20) K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ
    LL20_rho hlam (by norm_num) hηQ0 LL20_deltaE mX hmX0 hmXsym hsmall hrowS hηQc mV hmV0
    hmVsym hΔμ hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- **`thm:spectral-criterion`(a) at the root cut LL22** (`subsec:record:upper_root`, route B
at `p ≡ 3 (mod 4)`): `Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1` at `D := LL22`, for primes
`p ≥ 2^52` with `p ≡ 3 (mod 4)`, with these hypotheses discharged: `p ≠ 2`, `|U| = 72 ≤ n'`
(`n' = 72`), the degree bound `Δ = 20` (`LL22_hdeg`), (S1) `e_20(p, 72) < 1`
(`coarseErr_root_lt_nat`), the orderings `l_i` (`restList`), `ρ_row = 37675044` (`LL22_rho`) and
`Λ_D = 10 = max_k r_k` (`LL22_deltaE`). The remaining hypotheses are the certified numbers of
`cor:spec2:coupling`, `lem:spec:degone` and WP-A's finite tests, as in
`spectral_criterion_cut_S1`; `hne` is supplied by `LL22_hne`. The total order of `U⁺` is
`LL22_linearOrder` (any order works in `spectral_criterion_cut_S1`). -/
theorem LL22_criterion {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : LL22.cut.Half → LL22.cut.Half → Prop) [DecidableRel Adj]
    (hp52 : 2 ^ 52 ≤ p) (hp3 : p % 4 = 3)
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
        lamH εH θ 37675044 ΓE lamH 1
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
    -(g * rp p) * ‖f‖ ^ 2 ≤ ⟪f, Spectral.cutOp LL22 hne f⟫_ℝ :=
  spectral_criterion_cut_S1 LL22 hW hMR Adj (ne_two_of_ge hp52) hp3 card_slot.le hne LL22_hdeg
    (coarseErr_root_lt_nat hp52) (restList LL22) (restList_nodup LL22) (restList_cover LL22)
    (restList_disj LL22) K₀ Tns Tcoll hεZ hZ hT hK hns hcoll hΓc hrow hrowX hεH hΛ0 hθ0 hθ
    LL22_rho hlam (by norm_num) hηQ0 LL22_deltaE mX hmX0 hmXsym hsmall hrowS hηQc mV hmV0
    hmVsym hΔμ hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Root
