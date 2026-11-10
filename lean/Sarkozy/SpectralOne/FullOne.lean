module

public import Sarkozy.SpectralOne.ChainGen

@[expose] public section

/-!
# The class-one spectral criterion for the cut laws, in S1's final form

`paper/sections/14_spectral.tex`, `thm:spectral-criterion`(a), `subsec:advance:parity`,
`lem:spec2:paley-one`.

**`spectral_criterion_cut_full_one`**: `spectral_criterion_cut_full_gen` (S1's
`spectral_criterion_cut_full` at both classes) with `ζ̄` discharged by `lem:spec2:paley-one` in
instance (A) (`hzeta_cut`). It holds at every odd `p`; at `p ≡ 3 (mod 4)` the class-one
hypotheses are vacuous or reduce to S1's (`hplus` is `hlam` with `Λ₊ = λ̄(𝐇)`).

New material for this paper.
-/

namespace Sarkozy.SpectralOne

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx
open scoped BigOperators InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at both classes, in S1's final form,
with `ζ̄` discharged** (`lem:spec2:paley-one`, `subsec:advance:parity`): S1's
`spectral_criterion_cut_full` without `p ≡ 3 (mod 4)`. At `p ≡ 1 (mod 4)` this is the class-one
criterion: `ζ̄ = ζ = (R_cut R_full − 1) + m/((p − m) r)` (`hzeta_cut`), for a relation `Adj`
containing the adjacency of `G⁺` and `R_full ≥ U_J/L_J` on the non-coverable `J`
(`hLJ`, `hRJ`). The class-one data that remain hypotheses are the certified `Λ₊` with `𝐇^cov`
(`hplus`), `R_full`, and the two finite tests `htp`, `htm` (distinct at class one). -/
theorem spectral_criterion_cut_full_one [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hAdj : ∀ i j : D.cut.Half, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    (hp2 : p ≠ 2) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    -- error conditions
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    -- `R_full` of `lem:spec2:paley-one`
    {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m) (hmp : m < p) {Rfull : ℝ} (hRfull1 : 1 ≤ Rfull)
    (hLJ : ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      0 < lowJ (p := p) D m J)
    (hRJ : ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      upJ (p := p) D J ≤ Rfull * lowJ (p := p) D m J)
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
      D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (2 ^ Labellings.nbrCount D.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase j) j)
            (Fintype.card D.cut.Half))) - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ j, ((2 : ℝ) ^ (D.Nset j).card - 1) *
      ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤ ρ)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ j, ‖w j‖ ^ 2)
    -- the class-one input `Λ₊ ≥ λ̄(𝐇 + [p ≡ 1]𝐇^cov)` (`subsec:advance:parity`)
    {Λp : ℝ}
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
    (hηB : etaBcx p (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) ^ 2 *
        (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn))⁻¹)
        Λp εH θ ρ ΓE lamH
        ((D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) * Rfull - 1) +
          (m : ℝ) / (((p : ℝ) - m) * rp p))
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
  have he1 := (errors_of_S1 D hn hdeg hS1).1
  exact spectral_criterion_cut_full_gen D hW hMR Adj hp2 hn hne hdeg hS1 l hnd hcov hdisj h4
    hΔ' 𝔓 h𝔓 wit cx cz bucket 𝔮 hwit hcovX hbucket ord hord πc hπc hεZ hNns0 hNnsB hDcol hεZc
    hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam (zeta_cut_nonneg D he1 hmp hRfull1)
    (fun _ => hzeta_cut D hWB hp2 hn hne he1 hm hmp Adj hAdj hLJ hRJ) hplus hΛD hηQ0 hDE
    hrowS hηQc hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralOne
