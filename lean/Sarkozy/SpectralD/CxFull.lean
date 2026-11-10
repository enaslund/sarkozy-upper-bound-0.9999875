module

public import Sarkozy.SpectralD.CxNonstar

@[expose] public section

/-!
# The spectral criterion for the cut laws with X1's extraction and collision data

`spectral_criterion_cut_full`: `spectral_criterion_cut_X1` with
* the nonstar bound from X1's `ExtractionK.extraction_compressed_buckets_two`
  (`cor:extraction-compressed`, witnesses of size two over `𝔽_p`; inputs: `WeilBound`,
  `FourCycleBound p` from `cor:dl:normalized`(a), an exact partition `𝔓` of the nonstar sets with
  witnesses, covers and buckets), `N_ns` any number above its bound;
* the collision bounds from `Extraction.collision_opBound`, `collision_opBound2`
  (`lem:oct24-collision`(a), (b): `D_col = D_1 + D_{≥2}` for orders `ord`, `πc`);
* their count-error conditions (`ê = e_Δ(p, n')`, `e_{d⁰_v}(p, |U⁺|) < 1`) from (S1), via
  `coarseError = coarseErr` and the degree bound.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- **`thm:spectral-criterion`(a) for the cut laws `λ_p(G⁺)` at `p ≡ 3 (mod 4)`**, with the
nonstar and collision operators bounded by X1's and `Extraction`'s theorems; the remaining
hypotheses are their data (`FourCycleBound p`, the partition `𝔓` and its records, the orders
`ord`, `πc`, the count errors) and the numbers of the earlier versions. -/
theorem spectral_criterion_cut_full [LinearOrder D.cut.Half] (hW : Target.Weil)
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
  have hWB := Labellings.weilBound_of_target hW p hp2
  have hqp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hU : Fintype.card D.cut.Half ≤ nn :=
    (Fintype.card_le_of_injective (fun u : D.cut.Half => u.1) fun a b h => Subtype.ext h).trans hn
  have hn' : Fintype.card D.cut.Half ≤ Fintype.card D.cut.Half := le_rfl
  have hce : ∀ t m : ℕ, Extraction.coarseError t (Fintype.card (ZMod p) : ℕ) (m : ℝ) =
      TraceMixing.coarseErr p t m := by
    intro t m
    rw [ZMod.card]
    unfold Extraction.coarseError Extraction.coarseH TraceMixing.coarseErr
    simp only [inv_pow, Real.sq_sqrt hqp.le, one_div]
    ring
  have hehat : ∀ i, Extraction.coarseError (Extraction.rowsDeg0 D.halfGraph i)
      (Fintype.card (ZMod p) : ℕ) (Fintype.card D.cut.Half : ℕ) ≤ TraceMixing.coarseErr p Δ nn := by
    intro i
    rw [hce]
    exact TraceMixing.coarseErr_mono hqp (graphNbrs_half_le D hdeg i) hU
  have hehat1 : TraceMixing.coarseErr p Δ nn < 1 := hS1
  have hS1' : ∀ v, Extraction.coarseError (Extraction.rowsDeg0 D.halfGraph v)
      (Fintype.card (ZMod p) : ℕ) (Fintype.card D.cut.Half : ℕ) < 1 :=
    fun v => (hehat v).trans_lt hS1
  have hςv : ∀ j k, D.sgn j k = 0 ∨ D.sgn j k = 1 ∨ D.sgn j k = -1 := by
    intro j k
    unfold Cuts.SpecData.sgn
    split_ifs <;> simp
  have hanti : ∀ j k, D.sgn k j = -D.sgn j k := fun j k => D.sgn_antisymm j k
  have hEx : ∀ e ∈ D.crossPairs, D.sgn e.1 e.2 ≠ 0 := fun e he => by
    simp only [Cuts.SpecData.crossPairs, mem_filter, mem_univ, true_and] at he
    exact he
  have hq0 : (0 : ℝ) < (Fintype.card (ZMod p) : ℕ) := by exact_mod_cast Fintype.card_pos
  have hnsX : ∀ f g : (D.cut.Half → ZMod p) → ℝ,
      |(D.halfLaw hne).expect (fun x => f x * (D.halfLaw hne).expect (fun x' =>
        (∑ S ∈ Extraction.nonstars D.crossPairs, ∏ e ∈ S, ExtractionK.chiPair D.sgn e x x') *
          g x'))| ≤
        Nns * Real.sqrt ((D.halfLaw hne).expect (fun x => f x ^ 2)) *
          Real.sqrt ((D.halfLaw hne).expect (fun x => g x ^ 2)) := fun f g =>
    (ExtractionK.extraction_compressed_buckets_two hp2 h4 hWB D.halfGraph D.sgn hςv hanti
      (D.half_nonempty hne) hn' hehat hehat1 hΔ' D.crossPairs hEx 𝔓 h𝔓 wit cx cz bucket 𝔮 hwit
      hcovX hbucket f g).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNnsB (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  have hcoll1 := Extraction.collision_opBound hWB D.halfGraph D.sgn hςv hanti
    (D.half_nonempty hne) hn' hS1' ord hord
  have hcoll2 := Extraction.collision_opBound2 hWB D.halfGraph D.sgn hςv hanti
    (D.half_nonempty hne) hn' hS1' πc hπc
  have hD10 := Extraction.collisionD1_nonneg D.halfGraph D.sgn ord hq0 hS1'
  have hD20 := Extraction.collisionD2_nonneg D.halfGraph D.sgn πc hq0 hS1'
  exact spectral_criterion_cut_X1 D hW hMR Adj hp2 hp3 hn hne hdeg hS1 l hnd hcov hdisj hεZ hNns0
    hD10 hD20 hnsX hcoll1 hcoll2 hDcol hεZc hΓc hrow hrowX hεH hΛ0 hθ0 hθ hρ hlam hΛD hηQ0 hDE
    hrowS hηQc hrowV hεVc hεV hcbar0 hcbar hηQ hηB hεVb hεV0 hεV1 hsp hsm htp htm hgp hgm f

end Sarkozy.SpectralD.Cx
