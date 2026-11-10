module

public import Sarkozy.MiddleCertificates.Route
public import Sarkozy.MiddleCertificates.UpperChain

/-!
# Route A at one prime, part (d) (`thm:spectral-criterion`(d))

* `RouteAUpper D p Adj c̄ τ η̄_Q η̄_B ε̄_V g B`: **the analytic part of
  `thm:spectral-criterion`(d) at `p`**: the finite tests of `𝐀₀(ξ)` and of `-𝐀₀(ξ)` at the bars,
  `(c̄_⊥ + τ)/(1 - ε̄_V) ≤ g` and `g p^{-1/2} < 1` give `A_p ⪯ 1 + B/p`. *Open input* for the
  middle cuts;
* **`routeAUpper_of_full`**: `RouteAUpper` from the inputs of `spectral_criterion_cut_full` (the
  same as for part (a), `routeALower_of_full`) and `ε_ϱ(p)²/(1 - g p^{-1/2}) ≤ B/p`
  (`thm:spectral-criterion`(c),(d): with `B = B⁺ = p₀ε_ϱ(r₀)²/(1 - g r₀)` this is the
  monotonicity `p ε_ϱ(r)² ≤ p₀ ε_ϱ(r₀)²` of (c)); through `spectral_criterion_cut_full_upper`.
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx
open scoped BigOperators InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **The analytic part of `thm:spectral-criterion`(d) at the prime `p`**, at the bars
`(c̄_⊥, τ, η̄_Q, η̄_B, ε̄_V)` and the constants `g`, `B`: the finite tests of `±𝐀₀(ξ)` for every
`ξ`, `(c̄_⊥ + τ)/(1 - ε̄_V) ≤ g` and `g p^{-1/2} < 1` give `A_p ⪯ 1 + B/p`. *Open input* for the
middle cuts; sufficient conditions: `routeAUpper_of_full`. -/
def RouteAUpper (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (cbar s ηQbar ηBbar εVbar g B : ℝ) : Prop :=
  ∀ hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty,
    (∀ ξ : ZMod p, Spectral.FiniteTest (fun x => (qform (azero (sgnZ (p := p) D) ξ) x).re)
      (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar s ηQbar ηBbar) →
    (∀ ξ : ZMod p, Spectral.FiniteTest (fun x => -(qform (azero (sgnZ (p := p) D) ξ) x).re)
      (qXcx Adj D.Nset (sgnZ (p := p) D) ξ) cbar s ηQbar ηBbar) →
    (cbar + s) / (1 - εVbar) ≤ g → g * rp p < 1 →
    ∀ f : EuclideanSpace ℝ (D.cut.Half → ZMod p),
      ⟪f, Spectral.cutOp D hne f⟫_ℝ ≤ (1 + B / p) * ‖f‖ ^ 2

/-- **`RouteAUpper` from the inputs of `spectral_criterion_cut_full`** and
`ε_ϱ²/(1 - g p^{-1/2}) ≤ B/p` (`thm:spectral-criterion`(c),(d)). -/
theorem routeAUpper_of_full [LinearOrder D.cut.Half] (hW : Target.Weil)
    (hMR : Target.MovingRoot) (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hp3 : p % 4 = 3) {nn Δ : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
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
    {ρs : ℝ} (hrowS : ∀ k, ∑ l, (if sgnZ (p := p) D k l = 0 then mXcut p D k l else 0) ≤ ρs)
    (hηQc : ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρs +
        (Fintype.card D.cut.Half : ℝ) / (((p : ℝ) - 1) * rp p) ≤ ηQ)
    {ρv : ℝ} (hrowV : ∀ k, ∑ l, (if k = l then 0 else mVcut p D k l) ≤ ρv)
    (hεVc : ((Fintype.card D.cut.Half : ℝ) - 1) / ((p : ℝ) - 1) +
        (p : ℝ) / ((p : ℝ) - 1) * rp p * ρv ≤ εV) (hεV : 0 ≤ εV)
    -- WP-A's finite tests
    {cbar ηQbar ηBbar εVbar s g B : ℝ} (hcbar0 : 0 ≤ cbar)
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
    (hεVb : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hs : 0 < s)
    (hB : ((Spectral.starMstar (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2)
          D.halfGraph (D.half_nonempty hne)
          (errors_of_S1 D hn hdeg hS1).2.2.1) D.Nset (Spectral.starCoef (p := p) D) +
          Nns + Dcol) / (1 - εZ)) ^ 2 / (1 - g * rp p) ≤ B / p) :
    RouteAUpper (p := p) D Adj cbar s ηQbar ηBbar εVbar g B := by
  intro hne' htest htest' hg hgr f
  exact spectral_criterion_cut_full_upper D hW hMR Adj hp2 hp3 hn hne hdeg hS1 l hnd hcov hdisj h4
    hΔ' 𝔓 h𝔓 wit cx cz bucket 𝔮 hwit hcovX hbucket ord hord πc hπc hεZ hNns0 hNnsB hDcol hεZc hΓc
    hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hΛD hηQ0 hDE hrowS hηQc hrowV hεVc hεV hcbar0 hcbar hηQ hηB
    hεVb hεV0 hεV1 hs hs (fun ξ _ => htest ξ) (fun ξ _ => htest ξ) hg hg (fun ξ _ => htest' ξ)
    (fun ξ _ => htest' ξ) hgr hB f

end Sarkozy.MiddleCertificates
