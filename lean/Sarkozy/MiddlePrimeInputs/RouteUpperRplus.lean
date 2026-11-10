module

public import Sarkozy.MiddlePrimeInputs.RouteRplus
public import Sarkozy.MiddlePrimeInputs.UpperChainR

/-!
# Route A part (d) for L10 and L21 through the `R₊` chain, at C8's bars and the ALLp constants

`paper/sections/14_spectral.tex`, `thm:spectral-criterion`(c),(d) and `prop:spec2:mucentre`(c2);
`paper/sections/20_middle_reference.tex`, `lem:layer12-caps`(a), `cert:layer12-grid`.

* **`routeAUpper_midRplus`**: C8's `RouteAUpper` at the bars of piece `i` and
  `(g, B) = (allpG, allpB)`, at every prime `p ≥ X_i`, `p ≡ 3 (mod 4)`, from the inputs of
  `routeALower_midRplus` and `hB : ε_ϱ²/(1 - g p^{-1/2}) ≤ B/p`, along
  `spectral_criterion_cut_fullRplusE_upper` (`RchainE`, on `UpperChainR`). The `ε_V`, `η_Q`, `Λ_D`, `ρ_row` and
  graph inputs are proved, as in `routeALower_midRplus`.

With `midPrimeInputs_of_Rplus` this gives C8's `MidPrimeInputs c i p`, hence (C8's
`middleRootCaps_l10`, `middleL21Caps_of_inputs`) B6's fields `h10` and `h21`, from the open
inputs listed in `RouteRplus`.
-/

@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.PartV Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.SpectralD.Cx
  Sarkozy.MiddleCertificates MiddleCertificates.MidCut
open scoped BigOperators InnerProductSpace

/-- **Route A part (d) for L10 and L21 at the bars of piece `i` and the ALLp constants, through
the `R₊` chain** (`thm:spectral-criterion`(d), `lem:layer12-caps`(a)): the open inputs of
`routeALower_midRplus` and `hB`. -/
theorem routeAUpper_midRplus (m : MidCut) (i : Fin 33) {p : ℕ} [Fact p.Prime]
    (hW : Target.Weil) (hMR : Target.MovingRoot)
    (Adj : m.data.cut.Half → m.data.cut.Half → Prop) [DecidableRel Adj]
    (hp : 2 ^ 24 ≤ p) (hp3 : p % 4 = 3) (hX : pieceStart i ≤ p)
    (hne : (Labellings.injLabellings (ZMod p) m.data.G).Nonempty)
    -- the deletion order of the chain (any; for instance a concrete one, see `Orders`)
    (o : Fin m.data.cut.half.card ≃ m.data.cut.Half)
    {nn Δ : ℕ} (hn : Fintype.card m.Vertex ≤ nn)
    (hdeg : ∀ v, (univ.filter (fun w => (v, w) ∈ m.data.G.E ∨ (w, v) ∈ m.data.G.E)).card ≤ Δ)
    (hS1 : TraceMixing.coarseErr p Δ nn < 1)
    {ehat : ℝ} (hehat : ∀ i, Extraction.coarseError (Extraction.rowsDeg0 m.data.halfGraph i)
      (Fintype.card (ZMod p) : ℕ) (Fintype.card m.data.cut.Half : ℕ) ≤ ehat) (hehat1 : ehat < 1)
    (hnn : nn ≤ 12)
    -- the orderings `l_i` of `W ∖ fix(i)` (for instance C8's `restList`)
    (l : m.data.cut.Half → List m.Vertex) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet m.data i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet m.data i)
    -- the character expansion: the data of X1's and `Extraction`'s theorems
    (h4 : Extraction.FourCycleBound p)
    {Δ' : ℕ} (hΔ' : ∀ i, ExtractionK.cmpDeg m.data.halfGraph m.data.sgn i ≤ Δ')
    (𝔓 : Finset (Finset (m.data.cut.Half × m.data.cut.Half) ×
      Finset (m.data.cut.Half × m.data.cut.Half)))
    (h𝔓 : Extraction.IsExactPartition m.data.crossPairs 𝔓 (Extraction.nonstars m.data.crossPairs))
    (wit : Finset (m.data.cut.Half × m.data.cut.Half) × Finset (m.data.cut.Half × m.data.cut.Half) →
      Fin 2 → m.data.cut.Half × m.data.cut.Half)
    (cx cz : Finset (m.data.cut.Half × m.data.cut.Half) ×
      Finset (m.data.cut.Half × m.data.cut.Half) → Finset m.data.cut.Half)
    (bucket : Finset (m.data.cut.Half × m.data.cut.Half) ×
      Finset (m.data.cut.Half × m.data.cut.Half) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, Extraction.IsWitness m.data.crossPairs c.1 c.2 (wit c))
    (hcovX : ∀ c ∈ 𝔓, Extraction.IsCover m.data.crossPairs c.1 c.2 (wit c) (cx c) (cz c))
    (hbucket : ∀ c ∈ 𝔓, ExtractionK.cmpOc m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
      (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c) ≤
        (bucket c : ℝ) * 2 ^ 𝔮)
    (ord : m.data.cut.Half → m.data.cut.Half → m.data.cut.Half → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (πc : ℕ → m.data.cut.Half → ℕ) (hπc : ∀ k, Function.Injective (πc k))
    {εZ Nns Dcol : ℝ} (hεZ : εZ < 1) (hNns0 : 0 ≤ Nns)
    (hNnsB : (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        ExtractionK.cmpLambda0 m.data.halfGraph m.data.sgn (Fintype.card (ZMod p))
          (Fintype.card m.data.cut.Half) ehat 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ Extraction.twoCycleCount (ExtractionK.witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ ExtractionK.cmpEx m.data.halfGraph (m.data.crossPairs \ (c.1 ∪ c.2))
              (ExtractionK.witV (wit c)) (ExtractionK.witW (wit c)) (cx c) (cz c))) *
          Real.exp (ExtractionK.cmpGamma (Fintype.card (ZMod p)) (Fintype.card m.data.cut.Half)
            Δ' * (b * 2 ^ 𝔮))) ≤ Nns)
    (hDcol : Extraction.collisionD1 m.data.halfGraph m.data.sgn ord (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) +
      Extraction.collisionD2 m.data.halfGraph m.data.sgn πc (Fintype.card (ZMod p))
        (Fintype.card m.data.cut.Half) ≤ Dcol)
    (hεZc : 2 * ((1 / Real.sqrt p) ^ 2 * vPairs m) + Nns + Dcol ≤ εZ)
    -- the certified numbers of `cor:spec2:coupling`
    {ΓE εH ρβ ρX : ℝ}
    (hΓc : ∑ k, ((2 : ℝ) ^ (m.data.Nset k).card *
          (1 + TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) *
          devConst (Rprime p m.data nn l k)
            (TraceMixing.coarseErr p (m.data.Nset k).card (Fintype.card m.data.cut.Half)) ^ 2 +
        (Fintype.card m.data.cut.Half : ℝ) * 4 ^ (m.data.Nset k).card / p) ≤ ΓE)
    (hrow : ∀ k, ∑ l, betaG m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l', bX m.data.Nset (sgnZ (p := p) m.data)
      (fun t => TraceMixing.coarseErr p t (Fintype.card m.data.cut.Half))
        (Rprime p m.data nn l) k l' ≤ ρX)
    (hεH : ρβ + ρX ≤ εH) (hΛ0 : 0 ≤ (lamMid m : ℝ) + εH)
    {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ j : m.data.cut.Half,
      ((2 ^ (withOrder m o).mcross * (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) ((withOrder m o).tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn ((withOrder m o).t0deg j))) *
          (withOrder m o).Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn)) *
        (2 ^ Labellings.nbrCount m.data.halfGraph (univ.erase j) j /
          (1 - TraceMixing.coarseErr p (Labellings.nbrCount m.data.halfGraph (univ.erase j) j)
            (Fintype.card m.data.cut.Half))) - 1 ≤ θ ^ 2)
    -- the comparisons with C8's bars at the piece start
    (hcbar : (Nns + Dcol) / (1 - εZ) + ((Nns + Dcol) / (1 - εZ)) ^ 2 ≤ (cbar m i : ℝ) * rp p)
    (hηB : etaBcx p (2 ^ (withOrder m o).mcross *
          (∏ j, Labellings.stepUpper (Fintype.card (ZMod p)) ((withOrder m o).tdeg j)) /
          ((1 - εZ) * ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn ((withOrder m o).t0deg j)))
        (lamMid m) εH θ (rhoRow m) ΓE (lamMid m) 1
        ((PaleyB.ncSets Adj).card * Fintype.card m.data.cut.Half : ℝ) (epsV m i)
        (Real.sqrt (lamD2 m)) (etaQ m i) ≤ (etaB m i : ℝ))
    (hB : ((Nns + Dcol) / (1 - εZ)) ^ 2 /
        (1 - (BlockSpecPaper.AllpData.allpG i m.allpIdx : ℝ) * rp p) ≤
        (BlockSpecPaper.AllpData.allpB i m.allpIdx : ℝ) / p) :
    RouteAUpper (p := p) m.data Adj (cbar m i) (tau m i) (etaQ m i) (etaB m i) (epsV m i)
      (BlockSpecPaper.AllpData.allpG i m.allpIdx) (BlockSpecPaper.AllpData.allpB i m.allpIdx) := by
  intro hne' htest htest' hg hgr f
  obtain ⟨hΛD, hDE, hrowS, hηQc⟩ := etaQ_input m i hp3 hX
  obtain ⟨hrowV, hεVc⟩ := epsV_input m i hX
  obtain ⟨_, hτ, hc0, hv0, hv1, _⟩ := scalars m i
  have hτ' : (0 : ℝ) < tau m i := by exact_mod_cast hτ
  have hc0' : (0 : ℝ) ≤ cbar m i := by exact_mod_cast hc0
  have hv0' : (0 : ℝ) ≤ epsV m i := by exact_mod_cast hv0
  have hv1' : (epsV m i : ℝ) < 1 := by exact_mod_cast hv1
  have hq0 : (0 : ℝ) ≤ etaQ m i := by exact_mod_cast etaQ_nonneg m i
  have hεZc' : 2 * Spectral.starZstar (SecondOrder.graphPinned
        (Labellings.weilBound_of_target hW p (mid_ne_two hp)) m.data.halfGraph
        (m.data.half_nonempty hne) (errors_of_S1 m.data hn hdeg hS1).2.2.1) m.data.Nset
        (Spectral.starCoef (p := p) m.data) + Nns + Dcol ≤ εZ := by
    have := starZstar_mid m (SecondOrder.graphPinned (Labellings.weilBound_of_target hW p (mid_ne_two hp)) m.data.halfGraph (m.data.half_nonempty hne) (errors_of_S1 m.data hn hdeg hS1).2.2.1)
    linarith
  have hcbar' : (Nns + Dcol) / (1 - εZ) +
        ((Spectral.starMstar (SecondOrder.graphPinned
          (Labellings.weilBound_of_target hW p (mid_ne_two hp))
          m.data.halfGraph (m.data.half_nonempty hne)
          (errors_of_S1 m.data hn hdeg hS1).2.2.1) m.data.Nset
            (Spectral.starCoef (p := p) m.data) + Nns + Dcol) / (1 - εZ)) ^ 2 ≤
        (cbar m i : ℝ) * rp p := by
    rw [starMstar_mid, zero_add]
    exact hcbar
  have hB' : ((Spectral.starMstar (SecondOrder.graphPinned
          (Labellings.weilBound_of_target hW p (mid_ne_two hp))
          m.data.halfGraph (m.data.half_nonempty hne)
          (errors_of_S1 m.data hn hdeg hS1).2.2.1) m.data.Nset
            (Spectral.starCoef (p := p) m.data) + Nns + Dcol) / (1 - εZ)) ^ 2 /
        (1 - (BlockSpecPaper.AllpData.allpG i m.allpIdx : ℝ) * rp p) ≤
        (BlockSpecPaper.AllpData.allpB i m.allpIdx : ℝ) / p := by
    rw [starMstar_mid, zero_add]
    exact hB
  exact spectral_criterion_cut_fullRplusE_upper (withOrder m o) hW hMR Adj (mid_ne_two hp) hp3 hn hne
    (hL_mid m o hp hnn)
    hdeg hS1 hehat hehat1 l hnd hcov hdisj h4
    hΔ' 𝔓 h𝔓 wit cx cz bucket 𝔮 hwit hcovX hbucket ord hord πc hπc hεZ hNns0 hNnsB hDcol hεZc'
    hΓc hrow hrowX hεH hΛ0 hθ0 hθ (rhoRow_le m) (mid_lam m hp3) hΛD hq0 hDE hrowS hηQc hrowV
    hεVc hv0' hc0' hcbar' le_rfl hηB le_rfl hv0' hv1' hτ' hτ' (fun ξ _ => htest ξ)
    (fun ξ _ => htest ξ) hg hg (fun ξ _ => htest' ξ) (fun ξ _ => htest' ξ) hgr hB' f

end Sarkozy.MiddlePrimeInputs
