module

public import Sarkozy.SpectralD.RootCriterion
public import Sarkozy.SpectralD.RootModelH
public import Sarkozy.SpectralD.CxExpansion

/-!
# The spectral criterion at the root cuts, expansion form

`paper/sections/25_upper_reference.tex`, `subsec:record:upper_root` (route B at
`p ≡ 3 (mod 4)`), and `paper/sections/14_spectral.tex`, `thm:spectral-criterion`(a).

`LL20_criterion_exp`, `LL22_criterion_exp`: S1's `Sarkozy.SpectralD.Cx.spectral_criterion_cut_exp`
(the character expansion and `lem:spec:small` proved) at the root cuts, for primes `p ≥ 2^52`
with `p ≡ 3 (mod 4)`, with the facts about the root discharged as in `LL20_criterion` (`p ≠ 2`,
`n' = 72`, `Δ = 20`, (S1), the orderings, `ρ_row`, `Λ_D`) and in addition `λ̄(𝐇)`, the maximal
absolute row sum of the integer matrix `𝐇` (`LL20_lamH`: `8856`; `LL22_lamH`: `1098`).

New material for this paper.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.SpectralD.Root

open Sarkozy Sarkozy.SpectralC Sarkozy.SpectralD.Cx

/-- **`thm:spectral-criterion`(a) at the root cut LL20, expansion form**
(`subsec:record:upper_root`, route B at `p ≡ 3 (mod 4)`):
`Sarkozy.SpectralD.Cx.spectral_criterion_cut_exp` at `D := LL20` for primes `p ≥ 2^52` with
`p ≡ 3 (mod 4)`, with these hypotheses discharged: `p ≠ 2`, `|U| = 72 ≤ n'` (`n' = 72`), the degree
bound `Δ = 20` (`LL20_hdeg`), (S1) `e_20(p, 72) < 1` (`coarseErr_root_lt_nat`), the orderings
`l_i` (`restList`), `ρ_row = 301768740` (`LL20_rho`), `λ̄(𝐇) = 8856` (the maximal absolute row
sum, `LL20_lamH`) and `Λ_D = 12 = max_k r_k` (`LL20_deltaE`). The remaining hypotheses are
as in `spectral_criterion_cut_exp`, with `λ̄(𝐇) = 8856` substituted; `hne` is supplied by
`LL20_hne`. The total order of `U⁺` is `LL20_linearOrder`. -/
theorem LL20_criterion_exp {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : LL20.cut.Half → LL20.cut.Half → Prop) [DecidableRel Adj]
    (hp52 : 2 ^ 52 ≤ p) (hp3 : p % 4 = 3)
    (hne : (Labellings.injLabellings (ZMod p) LL20.G).Nonempty)
    -- the character expansion: bounds for the explicit nonstar and collision operators
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1)
    (hns : ∀ x, ‖nsOp LL20 hne x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖collOp LL20 hne x‖ ≤ Dcol * ‖x‖)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p (ne_two_of_ge hp52)) LL20.halfGraph
        (LL20.half_nonempty hne)
        (errors_of_S1 LL20 card_slot.le LL20_hdeg (coarseErr_root_lt_nat hp52)).2.2.1) LL20.Nset
        (Spectral.starCoef (p := p) LL20) + Nns + Dcol ≤ εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE εH ρβ ρX : ℝ}
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
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ 8856 + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : LL20.cut.Half,
      LL20.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
        (2 ^ Labellings.nbrCount LL20.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount LL20.halfGraph (univ.erase j) j)
            (Fintype.card LL20.cut.Half))) - 1 ≤ θ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ηQ εV : ℝ} (hηQ0 : 0 ≤ ηQ)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) LL20 k l = 0 then mXcut p LL20 k l else 0) ≤ ρs)
    (hηQc : 12 / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card LL20.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p LL20 k l) ≤ ρv)
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
        8856 εH θ 301768740 ΓE 8856 1
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
  spectral_criterion_cut_exp LL20 hW hMR Adj (ne_two_of_ge hp52) hp3 card_slot.le hne LL20_hdeg
    (coarseErr_root_lt_nat hp52) (restList LL20) (restList_nodup LL20) (restList_cover LL20)
    (restList_disj LL20) hεZ hns hcoll hεZc hΓc hrow hrowX hεH hΛ0 hθ0 hθ LL20_rho
    (LL20_lamH hp3) (by norm_num) hηQ0 LL20_deltaE hrowS hηQc hrowV hεVc hεV hcbar0 hcbar hηQ
    hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

/-- **`thm:spectral-criterion`(a) at the root cut LL22, expansion form**
(`subsec:record:upper_root`, route B at `p ≡ 3 (mod 4)`):
`Sarkozy.SpectralD.Cx.spectral_criterion_cut_exp` at `D := LL22` for primes `p ≥ 2^52` with
`p ≡ 3 (mod 4)`, with these hypotheses discharged: `p ≠ 2`, `|U| = 72 ≤ n'` (`n' = 72`), the degree
bound `Δ = 20` (`LL22_hdeg`), (S1) `e_20(p, 72) < 1` (`coarseErr_root_lt_nat`), the orderings
`l_i` (`restList`), `ρ_row = 37675044` (`LL22_rho`), `λ̄(𝐇) = 1098` (the maximal absolute row
sum, `LL22_lamH`) and `Λ_D = 10 = max_k r_k` (`LL22_deltaE`). The remaining hypotheses are
as in `spectral_criterion_cut_exp`, with `λ̄(𝐇) = 1098` substituted; `hne` is supplied by
`LL22_hne`. The total order of `U⁺` is `LL22_linearOrder`. -/
theorem LL22_criterion_exp {p : ℕ} [Fact p.Prime] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : LL22.cut.Half → LL22.cut.Half → Prop) [DecidableRel Adj]
    (hp52 : 2 ^ 52 ≤ p) (hp3 : p % 4 = 3)
    (hne : (Labellings.injLabellings (ZMod p) LL22.G).Nonempty)
    -- the character expansion: bounds for the explicit nonstar and collision operators
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1)
    (hns : ∀ x, ‖nsOp LL22 hne x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖collOp LL22 hne x‖ ≤ Dcol * ‖x‖)
    (hεZc : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p (ne_two_of_ge hp52)) LL22.halfGraph
        (LL22.half_nonempty hne)
        (errors_of_S1 LL22 card_slot.le LL22_hdeg (coarseErr_root_lt_nat hp52)).2.2.1) LL22.Nset
        (Spectral.starCoef (p := p) LL22) + Nns + Dcol ≤ εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE εH ρβ ρX : ℝ}
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
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ 1098 + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : LL22.cut.Half,
      LL22.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t 72) ^ 2 *
        (2 ^ Labellings.nbrCount LL22.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount LL22.halfGraph (univ.erase j) j)
            (Fintype.card LL22.cut.Half))) - 1 ≤ θ ^ 2)
    -- the certified numbers of `lem:spec:degone`
    {ηQ εV : ℝ} (hηQ0 : 0 ≤ ηQ)
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) LL22 k l = 0 then mXcut p LL22 k l else 0) ≤ ρs)
    (hηQc : 10 / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card LL22.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p LL22 k l) ≤ ρv)
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
        1098 εH θ 37675044 ΓE 1098 1
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
  spectral_criterion_cut_exp LL22 hW hMR Adj (ne_two_of_ge hp52) hp3 card_slot.le hne LL22_hdeg
    (coarseErr_root_lt_nat hp52) (restList LL22) (restList_nodup LL22) (restList_cover LL22)
    (restList_disj LL22) hεZ hns hcoll hεZc hΓc hrow hrowX hεH hΛ0 hθ0 hθ LL22_rho
    (LL22_lamH hp3) (by norm_num) hηQ0 LL22_deltaE hrowS hηQc hrowV hεVc hεV hcbar0 hcbar hηQ
    hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Root
